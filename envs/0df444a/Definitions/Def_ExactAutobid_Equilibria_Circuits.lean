-- Prove2me | Definitions.Def_ExactAutobid_Equilibria_Circuits
-- name    : ExactAutobid_Equilibria_Circuits
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:56:15.201133+00:00
-- url     : https://prove2.me/theorems/e480c520-2544-417c-b52c-f43553ccf0fc
-- title:
--   Generalized circuits with gates C, D, ϕ; gate networks, outdegree, and implementation by fixed-size subcircuits (§2.3, Thm 3.1, Lemma B.2)
-- statement:
--   **The source problem (Lemma 2.5).** A generalized circuit with gates $C, D, \phi$ has variables $x_0,\dots,x_{N-1}$ ($N \ge 1$), each the output of exactly one gate
--   $$x_i = C(x_j) = 1 - x_j,\qquad x_i = D(x_j) = \min\{2x_j, 1\},\qquad x_i = \phi(x_j,x_k) = \tfrac{(1+x_j)(1+x_k)}{4},$$
--   with input indices in $\{0,\dots,N-1\}$; directed cycles and self-inputs are allowed. A solution is $x \in [0,1]^N$ satisfying every gate equation simultaneously. The real search problem `cdphiProblem` has these circuits (as lists of gates, binary encoded) as instances and these solutions.
--
--   **Gate networks (Lemma 2.6).** A gate type is an arity together with a gate equation, a relation between input values and output value (domain restrictions included). A gate network has variables $0,\dots,N-1$, variable $i$ being the output of gate $i$; its solutions are the assignments in $[0,1]^N$ satisfying every gate equation. The **outdegree** of a variable is the number of input positions of gates that read it; a network has **no self-loops** if no gate reads its own output. The complement gate is $y = 1 - x$ on $[0,1]$.
--
--   **Implementation by a fixed-size subcircuit (Theorem 3.1, Lemma B.2).** A subcircuit has $k$ input wires, internal wires each defined by one gate, and an output wire. A gate set $\mathcal{G}$ **implements** $f$ on $D$ if one finite subcircuit with gates in $\mathcal{G}$ satisfies: every input $x \in D$ extends to internal values satisfying all gate equations, and every such solution has output $f(x)$. The **strong** version of Lemma B.2 also requires the internal values to be uniquely determined by $x$ and to lie in $[0,1]$.
--
--   **Gate sets.** Lemma B.2's gates $y = \min\{1, c - \sum_{j\le k} a_j x_j\}$, $k \le 2$, $a_j \ge 0$, $c \ge \sum a_j$, inputs in $[0,1]$. Theorem 3.1(i): signed clipped affine gates $y = \mathrm{clip}_{[0,1]}(c + \sum_j a_j x_j)$ with rational coefficients, together with the response gate $y = h(\mathrm{lo} + (\mathrm{hi}-\mathrm{lo})s)$, $s \in [0,1]$ (the response $h$ on $I_0 = [\mathrm{lo},\mathrm{hi}]$ read through the affine encoding of $I_0$ into $[0,1]$). Theorem 3.1(ii): complement, capped doubling $\min\{2x,1\}$, halving $x/2$, capped addition $\min\{x+y,1\}$ and $I(x) = 1/(1+x)$, all on $[0,1]$.
--
--   **Formalization Note.** Rationality of a subcircuit is carried by its gate set (every gate type is built from rational constants); "fixed size" is the single finite subcircuit.
-- source:
--   Huang, Liu, Yan, On the Complexity of Exact Autobidding Equilibria, arXiv:2611.04475 (sha256 270d1b74…), §2.3, pp. 5–6 (Lemmas 2.5, 2.6); Theorem 3.1, p. 10; Lemma B.2, p. 58

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_FixpReciprocal_frame
import Definitions.Def_FixpReciprocal_RealSearch

namespace ExactAutobid.Equilibria

open OnlineCRS.Combine FixpReciprocal

/-! ### The source problem of Lemma 2.5 -/

/-- **The gates of Lemma 2.5**, with their input indices: `x_i = C(x_j) = 1 − x_j`,
`x_i = D(x_j) = min{2x_j, 1}`, `x_i = ϕ(x_j, x_k) = (1 + x_j)(1 + x_k)/4`.

Huang, Liu, Yan, *On the Complexity of Exact Autobidding Equilibria*, arXiv:2611.04475
(sha256 270d1b74…), §2.3, pp. 5–6, Lemma 2.5. -/
inductive CDPhiGate where
  | compl (j : ℕ)
  | dbl (j : ℕ)
  | phi (j k : ℕ)

/-- The right-hand side of the gate equation, reading the variables through `v`. -/
noncomputable def CDPhiGate.eval (v : ℕ → ℝ) : CDPhiGate → ℝ
  | .compl j => 1 - v j
  | .dbl j => min (2 * v j) 1
  | .phi j k => (1 + v j) * (1 + v k) / 4

/-- The gate's input indices are below `N`. -/
def CDPhiGate.ReadsBelow (N : ℕ) : CDPhiGate → Prop
  | .compl j => j < N
  | .dbl j => j < N
  | .phi j k => j < N ∧ k < N

/-- A generalized circuit with gates `C, D, ϕ`: `N ≥ 1` gates, gate `i` defining variable `x_i`,
input indices in `[N]` (cycles and self-inputs allowed). -/
def CDPhiValid (C : List CDPhiGate) : Prop :=
  1 ≤ C.length ∧ ∀ g ∈ C, g.ReadsBelow C.length

/-- The solutions of such a circuit: `x ∈ [0, 1]^N` satisfying every gate equation simultaneously
(§2.3, p. 6: "A solution assigns values to all variables so that every gate equation holds
simultaneously"). -/
def CDPhiSol (C : List CDPhiGate) : Set (Fin C.length → ℝ) :=
  {x | (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) ∧ ∀ i : Fin C.length, x i = (C.get i).eval (lookup x)}

/-- Numeric form of a gate. -/
def CDPhiGate.code : CDPhiGate → ℕ × ℕ × ℕ
  | .compl j => (0, j, 0)
  | .dbl j => (1, j, 0)
  | .phi j k => (2, j, k)

theorem CDPhiGate.code_injective : Function.Injective CDPhiGate.code := by
  intro a b h
  cases a <;> cases b <;> simp_all [CDPhiGate.code]

/-- Binary encoding of a gate. -/
def encCDPhiGate (g : CDPhiGate) : List Sym := fNat g.code.1 ++ fNat g.code.2.1 ++ fNat g.code.2.2

theorem encCDPhiGate_prefixFree : PrefixFree encCDPhiGate := by
  intro a b s t h
  simp only [encCDPhiGate, List.append_assoc] at h
  obtain ⟨h1, h⟩ := fNat_prefixFree h
  obtain ⟨h2, h⟩ := fNat_prefixFree h
  obtain ⟨h3, h⟩ := fNat_prefixFree h
  exact ⟨CDPhiGate.code_injective (Prod.ext h1 (Prod.ext h2 h3)), h⟩

/-- **Finding an exact solution of a generalized circuit with gate functions `C, D, ϕ`** (the
source problem of Lemma 2.5), as a real search problem.

Huang, Liu, Yan, arXiv:2611.04475 (sha256 270d1b74…), §2.3, pp. 5–6, Lemma 2.5. -/
def cdphiProblem : RealSearch where
  Inst := {C : List CDPhiGate // CDPhiValid C}
  enc := fun I => fList encCDPhiGate I.1
  enc_injective := fun _ _ h => Subtype.ext (encCDPhiGate_prefixFree.fList.injective h)
  dim := fun I => I.1.length
  Sol := fun I => CDPhiSol I.1

/-! ### Gate networks (Lemma 2.6) and subcircuit implementations (Theorem 3.1, Lemma B.2) -/

/-- **A gate type**: an arity and the gate equation, a relation between the input values and the
output value (domain restrictions of the gate are part of the relation). -/
structure GateType where
  /-- the number of input positions (the indegree) -/
  arity : ℕ
  /-- the gate equation `y = f(x)` (with the gate's input domain) -/
  rel : (Fin arity → ℝ) → ℝ → Prop

/-- A gate of a network whose wires are indexed by `V`: a gate type and the wire read at each of
its input positions. -/
structure Gate (V : Type) where
  /-- the gate type -/
  type : GateType
  /-- the wire read at each input position -/
  inputs : Fin type.arity → V

/-- **A gate network (generalized circuit)** with variables `x_0, …, x_{N−1}`, variable `i` being
the output of gate `i`; directed cycles and self-inputs are allowed (§2.3, p. 6). -/
structure GateNetwork where
  /-- the number of variables (= gates) -/
  N : ℕ
  /-- the gate defining each variable -/
  gate : Fin N → Gate (Fin N)

/-- The solutions of a gate network: assignments in `[0, 1]^N` satisfying every gate equation. -/
def GateNetwork.Sol (G : GateNetwork) : Set (Fin G.N → ℝ) :=
  {x | (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) ∧
    ∀ i, (G.gate i).type.rel (fun p => x ((G.gate i).inputs p)) (x i)}

/-- The outdegree of variable `v`: the number of input positions of gates that read `v` (§2.3,
p. 6). -/
noncomputable def GateNetwork.outdeg (G : GateNetwork) (v : Fin G.N) : ℕ :=
  Nat.card {q : (i : Fin G.N) × Fin (G.gate i).type.arity // (G.gate q.1).inputs q.2 = v}

/-- No gate reads its own output. -/
def GateNetwork.NoSelfLoops (G : GateNetwork) : Prop :=
  ∀ i p, (G.gate i).inputs p ≠ i

/-- The complement gate `C(x) = 1 − x` on `[0, 1]`. -/
def complGate : GateType := ⟨1, fun x y => x 0 ∈ Set.Icc (0 : ℝ) 1 ∧ y = 1 - x 0⟩

/-- **A subcircuit** with `k` designated input wires (`Sum.inl`) and `N` internal wires
(`Sum.inr`), internal wire `i` being the output of gate `i`, and a designated output wire. -/
structure Subcircuit (k : ℕ) where
  /-- the number of internal wires -/
  N : ℕ
  /-- the gate defining each internal wire -/
  gate : Fin N → Gate (Fin k ⊕ Fin N)
  /-- the output wire -/
  out : Fin k ⊕ Fin N

/-- The internal values `z` satisfy every gate equation of the subcircuit at the input `x`. -/
def Subcircuit.Holds {k : ℕ} (S : Subcircuit k) (x : Fin k → ℝ) (z : Fin S.N → ℝ) : Prop :=
  ∀ i, (S.gate i).type.rel (fun p => Sum.elim x z ((S.gate i).inputs p)) (z i)

/-- The value on the output wire. -/
def Subcircuit.outVal {k : ℕ} (S : Subcircuit k) (x : Fin k → ℝ) (z : Fin S.N → ℝ) : ℝ :=
  Sum.elim x z S.out

/-- **A gate set implements `f` on `D` by a fixed-size subcircuit**: one finite subcircuit whose
gates all belong to `𝒢` such that every input assignment in `D` extends to internal values
satisfying all gate equations, and every such solution has output `f(x)`.

Huang, Liu, Yan, arXiv:2611.04475 (sha256 270d1b74…), Theorem 3.1, p. 10: "Every source input
assignment extends through the subcircuits, and every solution of their equations gives the required
source outputs."

**Formalization Note.** Rationality of the subcircuit is carried by the gate sets: every gate type
of this mission is built from rational constants. -/
def ImplementsOn {k : ℕ} (𝒢 : Set GateType) (D : Set (Fin k → ℝ)) (f : (Fin k → ℝ) → ℝ) : Prop :=
  ∃ S : Subcircuit k, (∀ i, (S.gate i).type ∈ 𝒢) ∧
    (∀ x ∈ D, ∃ z, S.Holds x z) ∧
    ∀ x ∈ D, ∀ z, S.Holds x z → S.outVal x z = f x

/-- **Implementation with bounded unique internal values** (Lemma B.2, p. 58): as `ImplementsOn`,
and moreover every input in `D` determines the internal values uniquely and all of them lie in
`[0, 1]`. -/
def ImplementsUniquelyIn01 {k : ℕ} (𝒢 : Set GateType) (D : Set (Fin k → ℝ))
    (f : (Fin k → ℝ) → ℝ) : Prop :=
  ∃ S : Subcircuit k, (∀ i, (S.gate i).type ∈ 𝒢) ∧
    (∀ x ∈ D, ∃! z, S.Holds x z) ∧
    ∀ x ∈ D, ∀ z, S.Holds x z → (∀ i, z i ∈ Set.Icc (0 : ℝ) 1) ∧ S.outVal x z = f x

/-- The unit cube `[0, 1]^k` of source inputs. -/
def unitCube (k : ℕ) : Set (Fin k → ℝ) := {x | ∀ j, x j ∈ Set.Icc (0 : ℝ) 1}

/-- Clipping to `[0, 1]`: `clip_{[0,1]}(t) = min{1, max{0, t}}` (§2.3, p. 6). -/
noncomputable def clip01 (t : ℝ) : ℝ := min 1 (max 0 t)

/-! #### Source functions -/

/-- `C(x) = 1 − x`. -/
noncomputable def srcC : (Fin 1 → ℝ) → ℝ := fun x => 1 - x 0

/-- `D(x) = min{2x, 1}`. -/
noncomputable def srcD : (Fin 1 → ℝ) → ℝ := fun x => min (2 * x 0) 1

/-- `ϕ(x, y) = (1 + x)(1 + y)/4`. -/
noncomputable def srcPhi : (Fin 2 → ℝ) → ℝ := fun x => (1 + x 0) * (1 + x 1) / 4

/-! #### Gate sets -/

/-- The decreasing capped affine gate of Lemma B.2: `y = min{1, c − Σ_{j<k} a_j x_j}` with inputs
in `[0, 1]`. -/
def decCapGate (k : ℕ) (c : ℚ) (a : Fin k → ℚ) : GateType :=
  ⟨k, fun x y => (∀ j, x j ∈ Set.Icc (0 : ℝ) 1) ∧
    y = min 1 ((c : ℝ) - ∑ j, (a j : ℝ) * x j)⟩

/-- **The gates of Lemma B.2**: `y = min{1, c − Σ_{j=1}^k a_j x_j}`, `k ∈ {0, 1, 2}`, `a_j ≥ 0`,
`c ≥ Σ a_j`, rational constants, inputs in `[0, 1]`. -/
def decCapGates : Set GateType :=
  {g | ∃ (k : ℕ) (c : ℚ) (a : Fin k → ℚ), k ≤ 2 ∧ (∀ j, 0 ≤ a j) ∧ ∑ j, a j ≤ c ∧
    g = decCapGate k c a}

/-- A signed clipped affine gate: `y = clip_{[0,1]}(c + Σ_{j<k} a_j x_j)` with rational
`c, a_j` of any sign. -/
def clipAffGate (k : ℕ) (c : ℚ) (a : Fin k → ℚ) : GateType :=
  ⟨k, fun x y => y = clip01 ((c : ℝ) + ∑ j, (a j : ℝ) * x j)⟩

/-- The response gate of Theorem 3.1(i), read through the affine encoding of `I₀ = [lo, hi]` into
`[0, 1]`: `y = h(lo + (hi − lo)s)` for `s ∈ [0, 1]`. -/
def responseGate (h : ℝ → ℝ) (lo hi : ℚ) : GateType :=
  ⟨1, fun s y => s 0 ∈ Set.Icc (0 : ℝ) 1 ∧ y = h ((lo : ℝ) + ((hi : ℝ) - lo) * s 0)⟩

/-- **The gate set of Theorem 3.1(i)**: all signed clipped affine expressions (any arity, rational
coefficients of any sign) and the response `h` on `I₀ = [lo, hi]`. -/
def gatesResponse (h : ℝ → ℝ) (lo hi : ℚ) : Set GateType :=
  {g | ∃ (k : ℕ) (c : ℚ) (a : Fin k → ℚ), g = clipAffGate k c a} ∪ {responseGate h lo hi}

/-- **The gate set of Theorem 3.1(ii)**, all on `[0, 1]`: complement `1 − x`, capped doubling
`min{2x, 1}`, halving `x/2`, capped addition `min{x + y, 1}`, and `I(x) = 1/(1 + x)`. -/
def gatesThrottle : Set GateType :=
  {complGate,
   ⟨1, fun x y => x 0 ∈ Set.Icc (0 : ℝ) 1 ∧ y = min (2 * x 0) 1⟩,
   ⟨1, fun x y => x 0 ∈ Set.Icc (0 : ℝ) 1 ∧ y = x 0 / 2⟩,
   ⟨2, fun x y => x 0 ∈ Set.Icc (0 : ℝ) 1 ∧ x 1 ∈ Set.Icc (0 : ℝ) 1 ∧ y = min (x 0 + x 1) 1⟩,
   ⟨1, fun x y => x 0 ∈ Set.Icc (0 : ℝ) 1 ∧ y = 1 / (1 + x 0)⟩}

end ExactAutobid.Equilibria


