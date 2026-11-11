-- Prove2me | Definitions.Def_OncePaid_Sparse_Circuit
-- name    : OncePaid_Sparse_Circuit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T13:45:33.799069+00:00
-- url     : https://prove2.me/theorems/88359cf4-177e-44f5-a2e5-cd715977cfb9
-- title:
--   Min-plus circuits with positive scalar gates and real constants: value, addition count $a(C)$, path gains, soundness and approximation
-- statement:
--   A **min-plus circuit with positive scalar gates** over the price inputs $\iota$ is a finite directed acyclic graph whose gates are: price inputs $c_x$ ($x\in\iota$); finite real constants (of any sign); binary minimum gates; binary addition gates; and unary gates multiplying their argument by a fixed real $\theta>0$. The structure and the constants are fixed before the prices are known; a gate may feed many later gates (sharing). The circuit computes $C(c)$, the value of its output gate at the price vector $c$.
--
--   - $a(C)$ is the number of binary addition gates of the shared DAG, each gate counted once; minimum gates, scalar gates, constants, inputs and wires are free.
--   - A **path** is a directed path from an input gate to the output gate; its **gain** is the product of the scale factors of the scalar gates on it. The circuit has **path-gain floor** $\lambda$ on a set $A$ of inputs if every path starting at an input $c_x$ with $x\in A$ has gain at least $\lambda$ (paths starting at constants are unconstrained).
--   - For an objective $f:\mathbb R^\iota\to\mathbb R\cup\{+\infty\}$ and a price domain $D$, $C$ is **sound** on $D$ if $f(c)\le C(c)$ for all $c\in D$, and a **sound factor-$\rho$ approximation** on $D$ if moreover $C(c)\le\rho f(c)$ for all $c\in D$:
--
--   $$
--   f(c)\ \le\ C(c)\ \le\ \rho\, f(c)\qquad(c\in D).
--   $$
--
--   - $\{2,3,4\}^\iota$ is the finite price domain used throughout.
--
--   These are the objects of all the lower bounds of the mission: $a(C)$ is the cost measure, and soundness plus the approximation inequality is the guarantee demanded on the finite domain.
--
--   **Formalization Note** A circuit is a straight-line program: a list of gates, each referring to earlier gates by index, the output being the last gate (`Circuit.WF` requires a nonempty list, arguments pointing to earlier gates, and every scale factor positive). $a(C)$ counts the addition gates of the list (also unreachable ones, which can only increase it). Paths are lists of gate indices from an input gate to the output, each an argument of the next. Objectives take values in `WithTop ℝ` (`⊤` $=+\infty$), and $C(c)\le\rho f(c)$ is imposed only where $f(c)$ is finite (where $f(c)=+\infty$ it holds trivially, and soundness fails anyway).
-- source:
--   Chao, Li, Gao, Wang, Once-Paid Subsequences and the Cost of Min-Plus Approximation, STOC 2027 submission (manuscript sha256 9dc21472…), pp. 2–3, §1.1 and pp. 11–12, §3.1 (PDF pp. 4–5, 13–14)

import Mathlib

namespace OncePaid.Sparse

/-!
# Min-plus circuits with positive scalar gates

Chao, Li, Gao, Wang, *Once-Paid Subsequences and the Cost of Min-Plus Approximation*,
STOC 2027 submission (manuscript sha256 9dc21472…), pp. 2–3 §1.1 and pp. 11–12 §3.1.

A circuit over the price inputs `ι` is a finite DAG whose gates are price inputs, finite real
constants (of any sign), binary minimum, binary addition, and (scalar extension) unary
multiplication by a fixed positive real. It is encoded as a straight-line program: a list of
gates `g₀, …, g_{m-1}` in which every gate refers only to earlier gates by their index; the
output is the last gate. Sharing is automatic (any gate may be referred to many times).

* `Circuit.WF`: the list is nonempty, every argument index is smaller than the gate's own index,
  and every scale factor is strictly positive.
* `Circuit.eval C c`: the value `C(c)` at the price vector `c : ι → ℝ`.
* `Circuit.addCount C = a(C)`: the number of binary addition gates of the shared DAG, each gate
  counted once (minimum gates, scale gates, constants and inputs are free).
* A path is a list of gate indices `p₀, …, p_k` starting at an input gate, ending at the output
  gate, each gate an argument of the next; its gain is the product of the scale factors of the
  scale gates on it. `GainFloorOn C A λ`: every path starting at an input gate whose label lies in
  `A` has gain at least `λ` (paths from constant gates are not constrained).
* `SoundOn f C D` and `ApproxWithin ρ f C D` encode `f(c) ≤ C(c)` and `C(c) ≤ ρ f(c)` on the
  price domain `D`, for an objective `f` with values in `WithTop ℝ` (`⊤ = +∞`); `priceBox ι` is
  `{2, 3, 4}^ι`.
-/

/-- A gate of a min-plus circuit with positive scalar gates; arguments are indices of earlier
gates. -/
inductive Gate (ι : Type) where
  /-- the price input `c_x` -/
  | input (x : ι)
  /-- a finite real constant (any sign) -/
  | const (r : ℝ)
  /-- binary minimum of gates `j` and `k` -/
  | min (j k : ℕ)
  /-- binary addition of gates `j` and `k` -/
  | add (j k : ℕ)
  /-- multiplication of gate `j` by the fixed real `θ` (required positive by `Circuit.WF`) -/
  | scale (θ : ℝ) (j : ℕ)

namespace Gate

/-- The argument indices of a gate. -/
def args {ι : Type} : Gate ι → List ℕ
  | input _ => []
  | const _ => []
  | min j k => [j, k]
  | add j k => [j, k]
  | scale _ j => [j]

/-- The scale factor contributed by a gate to a path gain (`1` unless it is a scale gate). -/
def scaleFactor {ι : Type} : Gate ι → ℝ
  | scale θ _ => θ
  | _ => 1

/-- Whether a gate is a binary addition gate. -/
def isAdd {ι : Type} : Gate ι → Bool
  | add _ _ => true
  | _ => false

/-- The value of a gate given the values `vals` of the earlier gates and the prices `c`. -/
noncomputable def evalWith {ι : Type} (vals : List ℝ) (c : ι → ℝ) : Gate ι → ℝ
  | input x => c x
  | const r => r
  | min j k => Min.min (vals.getD j 0) (vals.getD k 0)
  | add j k => vals.getD j 0 + vals.getD k 0
  | scale θ j => θ * vals.getD j 0

end Gate

/-- A min-plus circuit with positive scalar gates, as a straight-line program over the inputs
`ι`; the output is the last gate. -/
structure Circuit (ι : Type) where
  /-- the gates, in topological order -/
  gates : List (Gate ι)

namespace Circuit

variable {ι : Type}

/-- Well-formedness: nonempty, arguments point to earlier gates, scale factors are positive. -/
def WF (C : Circuit ι) : Prop :=
  C.gates ≠ [] ∧
    ∀ (m : ℕ) (g : Gate ι), C.gates[m]? = some g →
      (∀ j ∈ g.args, j < m) ∧ (∀ (θ : ℝ) (j : ℕ), g = Gate.scale θ j → 0 < θ)

/-- The index of the output gate (the last gate). -/
def output (C : Circuit ι) : ℕ := C.gates.length - 1

/-- The list of the values of all gates at the prices `c`, computed in order. -/
noncomputable def values (C : Circuit ι) (c : ι → ℝ) : List ℝ :=
  C.gates.foldl (fun vals g => vals ++ [g.evalWith vals c]) []

/-- The value `C_u(c)` of gate `u` at the prices `c`. -/
noncomputable def gateValue (C : Circuit ι) (c : ι → ℝ) (u : ℕ) : ℝ :=
  (C.values c).getD u 0

/-- The value `C(c)` of the circuit (its output gate) at the prices `c`. -/
noncomputable def eval (C : Circuit ι) (c : ι → ℝ) : ℝ :=
  C.gateValue c C.output

/-- `a(C)`: the number of binary addition gates, each gate of the shared DAG counted once. -/
def addCount (C : Circuit ι) : ℕ :=
  C.gates.countP Gate.isAdd

/-- Gate `j` is an argument of gate `u` (a directed wire `j → u`). -/
def IsArg (C : Circuit ι) (j u : ℕ) : Prop :=
  ∃ g, C.gates[u]? = some g ∧ j ∈ g.args

/-- `p` is a directed path from an input gate whose label lies in `A` to the output gate. -/
def IsInputPath (C : Circuit ι) (A : Set ι) (p : List ℕ) : Prop :=
  (∃ (u : ℕ) (x : ι), p.head? = some u ∧ C.gates[u]? = some (Gate.input x) ∧ x ∈ A) ∧
    p.getLast? = some C.output ∧ p.IsChain (fun a b => C.IsArg a b)

/-- The gain of a path: the product of the scale factors of the scale gates on it. -/
noncomputable def pathGain (C : Circuit ι) (p : List ℕ) : ℝ :=
  (p.map (fun u => ((C.gates[u]?).map Gate.scaleFactor).getD 1)).prod

/-- Path-gain floor `lam` on the inputs in `A`: every directed path from an input gate with label
in `A` to the output has gain at least `lam`. -/
def GainFloorOn (C : Circuit ι) (A : Set ι) (lam : ℝ) : Prop :=
  ∀ p : List ℕ, C.IsInputPath A p → lam ≤ C.pathGain p

end Circuit

/-- Soundness on the price domain `D`: `f(c) ≤ C(c)` for every `c ∈ D` (`f` may be `+∞`). -/
def SoundOn {ι : Type} (f : (ι → ℝ) → WithTop ℝ) (C : (ι → ℝ) → ℝ) (D : Set (ι → ℝ)) : Prop :=
  ∀ c ∈ D, f c ≤ ((C c : ℝ) : WithTop ℝ)

/-- The upper approximation inequality `C(c) ≤ ρ f(c)` on `D` (vacuous where `f(c) = +∞`). -/
def ApproxWithin {ι : Type} (ρ : ℝ) (f : (ι → ℝ) → WithTop ℝ) (C : (ι → ℝ) → ℝ)
    (D : Set (ι → ℝ)) : Prop :=
  ∀ c ∈ D, ∀ y : ℝ, f c = (y : WithTop ℝ) → C c ≤ ρ * y

/-- A sound factor-`ρ` approximation on `D`: `f(c) ≤ C(c) ≤ ρ f(c)` for every `c ∈ D`. -/
def SoundApprox {ι : Type} (ρ : ℝ) (f : (ι → ℝ) → WithTop ℝ) (C : (ι → ℝ) → ℝ)
    (D : Set (ι → ℝ)) : Prop :=
  SoundOn f C D ∧ ApproxWithin ρ f C D

/-- The finite price domain `{2, 3, 4}^ι`. -/
def priceBox (ι : Type) : Set (ι → ℝ) :=
  {c | ∀ x, c x = 2 ∨ c x = 3 ∨ c x = 4}

end OncePaid.Sparse


