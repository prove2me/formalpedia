-- Prove2me | Definitions.Def_LimitsLifting_Approximation_ApproxModel
-- name    : LimitsLifting_Approximation_ApproxModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:35:30.717126+00:00
-- url     : https://prove2.me/theorems/dbbd71bd-0bba-4407-bfd0-8973e11cc0d1
-- title:
--   §2.1, Definitions 4.2–4.3 — circuits, $\mathrm{Size}$, $\mathrm{Size}^+$, approximation models and $\mu(f,\mathcal M)$
-- statement:
--   Fix a finite set $\iota$ of input variables (the source's $[n]$) and a domain $Z\subseteq\{0,1\}^\iota$. A **partial Boolean function** with domain $Z$ is a map $f:Z\to\{0,1\}$; $\mathcal F(Z)$ denotes the set of all of them. $f$ is **monotone** if $u\le v$ coordinatewise implies $f(u)\le f(v)$ for all $u,v\in Z$.
--
--   A **circuit** is a De Morgan circuit with fan-in-two $\wedge$ and $\vee$ gates whose leaves are literals $x_i$, $\neg x_i$ and the constants $0,1$; gates may be shared (a DAG). It is **monotone** when it has no negative literal. Its **size** is its number of $\wedge$ and $\vee$ gates. $\mathrm{Size}(f)$ and $\mathrm{Size}^+(f)$ are the minimum sizes of a circuit, respectively a monotone circuit, agreeing with $f$ on every point of $Z$.
--
--   An **approximation model** $\langle\mathcal M,\bar\wedge,\bar\vee\rangle$ over $Z$ consists of a set $\mathcal M\subseteq\mathcal F(Z)$ containing $0$, $1$ and every input $x_i$, and commutative operators $\bar\wedge,\bar\vee:\mathcal M\times\mathcal M\to\mathcal M$. It is **non-monotone** if $\mathcal M$ also contains every $\neg x_i$.
--
--   The **balanced law** of $f$ picks $b\in\{0,1\}$ uniformly and then a uniform point of $f^{-1}(b)$, so that $\Pr[x=z]=1/(2|f^{-1}(b)|)$ for $z\in f^{-1}(b)$. With probabilities under this law,
--   $$\varepsilon_{\mathcal M}(f)=\min_{g\in\mathcal M}\Pr[f(x)\ne g(x)],\qquad \delta_{\mathcal M}(f)=\max_{g,h\in\mathcal M,\ \circ\in\{\vee,\wedge\}}\Pr[(g\mathbin{\bar\circ}h)(x)\ne(g\circ h)(x)],$$
--   and the **distance** of $f$ from the model is $\mu(f,\mathcal M)=\varepsilon_{\mathcal M}(f)/\delta_{\mathcal M}(f)$.
--
--   These are the objects of Razborov's approximation method: $\varepsilon$ measures how well the model approximates $f$, $\delta$ the error committed by replacing one gate by its approximating gate.
--
--   **Formalization Note** A circuit is a straight-line program: gate $k$ is a triple (operation, operand, operand), an operand being a literal, a constant or an earlier gate; well-formedness says every reference points to an earlier gate. $\mathrm{Size}$ and $\mathrm{Size}^+$ are infima in $\mathbb N$ (they would be $0$ for an empty set, which does not occur: every partial function on a finite domain has a circuit, and every partial monotone one a monotone circuit). $\min$ and $\max$ are real $\inf$/$\sup$ of finite nonempty sets, hence attained. $\mu$ uses real division ($\mu=0$ when $\delta=0$). If some class $f^{-1}(b)$ is empty its term is $0$. The zero-denominator convention agrees with §5.1 (printed p.27, PDF p.28). The balanced expression has total mass one when both label classes are nonempty, mass one-half when just one is nonempty, and zero on the empty domain; only the two-class case is a probability law.
-- source:
--   Gaia Carenini, Bruno Cavalar, Stefan Grosser, Jan Pich, Limits of Lifting, STOC 2027 submission #309 (October 2026), §2.1 (printed p. 9, PDF p. 10), Definition 4.2 and Definition 4.3 (printed p. 19, PDF p. 20)

import Mathlib

noncomputable section

namespace LimitsLifting.Approximation

open Classical

/-! # Partial Boolean functions, De Morgan circuits and approximation models

Carenini, Cavalar, Grosser, Pich, *Limits of Lifting*, STOC 2027 submission #309,
§2.1 (printed p. 9, PDF p. 10) and §4.1, Definitions 4.2 and 4.3 (printed p. 19, PDF p. 20).

The input variables are indexed by an arbitrary finite type `ι` (the source's `[n]`), and the
domain of a partial Boolean function is a set `Z ⊆ {0,1}^ι`; a partial function with domain `Z`
is a total function `Z → Bool`. -/

section Circuits

variable {ι : Type}

/-- An operand of a gate: a literal (`lit i true` is `x_i`, `lit i false` is `¬x_i`), a
constant, or the output of an earlier gate (by its position in the gate list). -/
inductive Operand (ι : Type) where
  | lit (i : ι) (pos : Bool)
  | const (b : Bool)
  | gate (j : ℕ)
  deriving DecidableEq

/-- A Boolean circuit in De Morgan form with binary `∧`/`∨` gates, written as a straight-line
program: gate `k` is `(isAnd, a, b)` and computes `a ∧ b` if `isAnd = true`, `a ∨ b` otherwise.
Negations occur only at the inputs (negative literals). Gates may be reused (DAG). -/
structure Circuit (ι : Type) where
  gates : List (Bool × Operand ι × Operand ι)
  output : Operand ι

/-- An operand refers only to gates strictly before position `k`. -/
def Operand.RefsBelow : Operand ι → ℕ → Prop
  | .gate j, k => j < k
  | _, _ => True

/-- Every gate refers only to earlier gates, and the output to an existing gate. -/
def Circuit.WellFormed (C : Circuit ι) : Prop :=
  (∀ k (hk : k < C.gates.length),
      (C.gates[k]).2.1.RefsBelow k ∧ (C.gates[k]).2.2.RefsBelow k) ∧
    C.output.RefsBelow C.gates.length

/-- A circuit is monotone when it has no negative literal. -/
def Circuit.IsMonotone (C : Circuit ι) : Prop :=
  (∀ g ∈ C.gates, (∀ i, g.2.1 ≠ .lit i false) ∧ (∀ i, g.2.2 ≠ .lit i false)) ∧
    ∀ i, C.output ≠ .lit i false

/-- The size of a circuit: its number of `∧` and `∨` gates. -/
def Circuit.size (C : Circuit ι) : ℕ := C.gates.length

/-- Value of an operand, given the values `acc` of the gates computed so far, in an arbitrary
value domain `V` with interpretations of literals and constants. -/
def Operand.value {V : Type} (litV : ι → Bool → V) (constV : Bool → V) (acc : List V) :
    Operand ι → V
  | .lit i b => litV i b
  | .const b => constV b
  | .gate j => acc.getD j (constV false)

/-- The values of all gates of a circuit, in order, for an interpretation of literals, constants,
`∧` and `∨` in a value domain `V`. -/
def Circuit.gateValues {V : Type} (C : Circuit ι) (litV : ι → Bool → V) (constV : Bool → V)
    (andV orV : V → V → V) : List V :=
  C.gates.foldl
    (fun acc g =>
      acc ++ [(if g.1 then andV else orV) (g.2.1.value litV constV acc)
        (g.2.2.value litV constV acc)]) []

/-- The value of the output of a circuit in a value domain `V`. -/
def Circuit.outValue {V : Type} (C : Circuit ι) (litV : ι → Bool → V) (constV : Bool → V)
    (andV orV : V → V → V) : V :=
  C.output.value litV constV (C.gateValues litV constV andV orV)

/-- The Boolean value computed by a circuit on an input `z ∈ {0,1}^ι`. -/
def Circuit.eval (C : Circuit ι) (z : ι → Bool) : Bool :=
  C.outValue (fun i b => if b then z i else !z i) id (· && ·) (· || ·)

end Circuits

section PartialFunctions

variable {ι : Type} [Fintype ι]

/-- A circuit computes the partial function `f` (with domain `Z`) if it agrees with `f` on
every point of `Z`. -/
def Computes {Z : Set (ι → Bool)} (C : Circuit ι) (f : Z → Bool) : Prop :=
  ∀ z : Z, C.eval z.1 = f z

/-- `Size(f)`: the minimum size of a well-formed De Morgan circuit computing `f` on its domain
(`sInf` in `ℕ`; every partial function on a finite domain is computed by some circuit). -/
noncomputable def circuitSize {Z : Set (ι → Bool)} (f : Z → Bool) : ℕ :=
  sInf {s : ℕ | ∃ C : Circuit ι, C.WellFormed ∧ Computes C f ∧ C.size = s}

/-- `Size⁺(f)`: the minimum size of a well-formed monotone circuit computing `f` on its domain
(`sInf` in `ℕ`; a partial monotone function is computed by some monotone circuit). -/
noncomputable def monotoneSize {Z : Set (ι → Bool)} (f : Z → Bool) : ℕ :=
  sInf {s : ℕ | ∃ C : Circuit ι, C.WellFormed ∧ C.IsMonotone ∧ Computes C f ∧ C.size = s}

/-- A partial Boolean function is monotone when `u ≤ v` coordinatewise implies
`f u ≤ f v` for all points `u, v` of its domain. -/
def PartialMonotone {Z : Set (ι → Bool)} (f : Z → Bool) : Prop :=
  ∀ u v : Z, (∀ i, u.1 i ≤ v.1 i) → f u ≤ f v

/-- The balanced input law of Definition 4.3: choose `b ∈ {0,1}` uniformly, then a uniform point
of `f⁻¹(b)`; i.e. `P[x = z] = 1/(2|f⁻¹(b)|)` for `z ∈ f⁻¹(b)`. This is the probability of an
event `E ⊆ Z` under that law. -/
noncomputable def balancedProb {Z : Set (ι → Bool)} (f : Z → Bool) (E : Z → Prop) : ℝ :=
  ∑ b : Bool, (1 / 2 : ℝ) *
    ((Nat.card {z : Z // f z = b ∧ E z} : ℝ) / (Nat.card {z : Z // f z = b} : ℝ))

/-- `ε_M(f) = min_{g ∈ M} P[f(x) ≠ g(x)]` under the balanced law. -/
noncomputable def epsM {Z : Set (ι → Bool)} (f : Z → Bool) (M : Set (Z → Bool)) : ℝ :=
  sInf ((fun g => balancedProb f (fun z => f z ≠ g z)) '' M)

/-- `δ_M(f) = max_{g,h ∈ M, ∘ ∈ {∨,∧}} P[(g ∘̄ h)(x) ≠ (g ∘ h)(x)]` under the balanced law,
where `andOp`, `orOp` are the approximating gates `∧̄`, `∨̄` of the model. -/
noncomputable def deltaM {Z : Set (ι → Bool)} (f : Z → Bool) (M : Set (Z → Bool))
    (andOp orOp : (Z → Bool) → (Z → Bool) → (Z → Bool)) : ℝ :=
  sSup {r : ℝ | ∃ g ∈ M, ∃ h ∈ M,
    r = balancedProb f (fun z => andOp g h z ≠ (g z && h z)) ∨
    r = balancedProb f (fun z => orOp g h z ≠ (g z || h z))}

/-- The distance `µ(f, M) = ε_M(f) / δ_M(f)` (real division). -/
noncomputable def muM {Z : Set (ι → Bool)} (f : Z → Bool) (M : Set (Z → Bool))
    (andOp orOp : (Z → Bool) → (Z → Bool) → (Z → Bool)) : ℝ :=
  epsM f M / deltaM f M andOp orOp

/-- An approximation model `⟨M, ∧̄, ∨̄⟩` over `Z` (Definition 4.2): `M ⊆ F(Z)` contains the
constants `0, 1` and the inputs `x_i`, and `∧̄, ∨̄ : M × M → M` are commutative operators. -/
structure ApproxModel (Z : Set (ι → Bool)) where
  M : Set (Z → Bool)
  andOp : (Z → Bool) → (Z → Bool) → (Z → Bool)
  orOp : (Z → Bool) → (Z → Bool) → (Z → Bool)
  zero_mem : (fun _ => false) ∈ M
  one_mem : (fun _ => true) ∈ M
  input_mem : ∀ i : ι, (fun z : Z => z.1 i) ∈ M
  and_mem : ∀ g ∈ M, ∀ h ∈ M, andOp g h ∈ M
  or_mem : ∀ g ∈ M, ∀ h ∈ M, orOp g h ∈ M
  and_comm : ∀ g ∈ M, ∀ h ∈ M, andOp g h = andOp h g
  or_comm : ∀ g ∈ M, ∀ h ∈ M, orOp g h = orOp h g

/-- A non-monotone approximation model additionally contains every negated input `¬x_i`. -/
def ApproxModel.IsNonMonotone {Z : Set (ι → Bool)} (A : ApproxModel Z) : Prop :=
  ∀ i : ι, (fun z : Z => !z.1 i) ∈ A.M

/-- `µ(f, M)` for an approximation model. -/
noncomputable def ApproxModel.mu {Z : Set (ι → Bool)} (A : ApproxModel Z) (f : Z → Bool) : ℝ :=
  muM f A.M A.andOp A.orOp

end PartialFunctions

end LimitsLifting.Approximation

end


