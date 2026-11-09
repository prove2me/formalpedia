-- Prove2me | Definitions.Def_STOC2027BoolCSP_Approximation_SDP
-- name    : STOC2027BoolCSP_Approximation_SDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:09.817303+00:00
-- url     : https://prove2.me/theorems/e1388af9-e7c8-47db-a98c-0c8b465cc0ca
-- title:
--   Signed $k$-conjunction instances, the common-reference relaxation (5), the rounding (28)–(29), and Section 7 matrix objects
-- statement:
--   After the conjunction expansion of Section 2 an instance consists of $M$ signed conjunctions on $n$ variables,
--   $$C:\ x_i=\sigma_{C,i}\ (i\in C),\qquad |C|=k,\ \sigma_{C,i}\in\{-1,1\},$$
--   each with a rational weight $w_C$; it is **normalized** when the weights are nonnegative and sum to one.
--
--   The **common-reference relaxation** (5) has a unit reference vector $e$, a unit decision vector $d_i$ for each variable and a vector $z_C$ for each clause, with
--   $$\langle e,e\rangle=1,\quad\langle d_i,d_i\rangle=1,\quad q_C=\langle z_C,z_C\rangle=\langle e,z_C\rangle,\quad\langle\sigma_{C,i}d_i,z_C\rangle=q_C\ (i\in C),$$
--   and maximizes $\sum_C w_Cq_C$. In Gram-matrix form (Section 7.1) let $\mathcal A$ be the affine space of symmetric $D\times D$ matrices, $D=n+1+M$, indexed by $e,d_1,\dots,d_n,z_1,\dots,z_M$, with unit shared diagonals, $G_{e,z_C}=G_{z_C,z_C}$ and $G_{d_i,z_C}=\sigma_{C,i}G_{z_C,z_C}$. The feasible region is $\mathcal F=\{G\in\mathcal A:G\succeq0\}$, the objective is $f(G)=\sum_Cw_CG_{z_C,z_C}$, and $\mathrm{SDP}=\sup_{G\in\mathcal F}f(G)$. The rank is unrestricted.
--
--   The **rounding** (28)–(29) of a vector solution uses $m=k+1$ and $\delta=\pi/m$. It draws a standard Gaussian vector $g$ in the ambient space and, independently of $g$, independent standard normals $\xi_0,\dots,\xi_n$. It sets
--   $$S_0=\sqrt\delta\,\langle g,e\rangle+\sqrt{1-\delta}\,\xi_0,\qquad S_i=\sqrt\delta\,\langle g,d_i\rangle+\sqrt{1-\delta}\,\xi_i,\qquad x_i=\mathrm{sgn}(S_i)\,\mathrm{sgn}(S_0),$$
--   with one reference score $S_0$ shared by every variable. Clause $C$ is satisfied when $x_i=\sigma_{C,i}$ for all $i\in C$.
--
--   For Section 7: rational Gram matrices and $N\times N$ rational matrices have explicit codes. The shared-block score covariance is $H=\delta B+(1-\delta)I_N$ (equation (34)), with $H^{1/2}$ its positive semidefinite square root. $\|\cdot\|_{op}$ is the Euclidean operator norm and $\|\cdot\|_F$ the Frobenius norm.
--
--   **Formalization Note** The shared block is indexed by `Fin (n+1)`, index $0$ being $e$ and index $i+1$ being $d_i$. Signs are Booleans with `true` meaning $+1$. A score $0$ gets sign $+1$; ties have probability zero in the ideal rounding. $\mathrm{SDP}$ is a real supremum: the feasible region is nonempty and compact (facts of Section 3), so the supremum is the attained maximum. Vector solutions live in $\mathbb R^\iota$ for an arbitrary finite $\iota$, with the dot product as inner product.
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 6, 11, 13, 14 (PDF 9, 14, 16, 17), Section 2 (final conjunctions, eq. (4)), Section 3 eq. (5), Section 6 eqs. (28)–(29), Section 7.1 (𝒜, 𝓕, f) and Section 7.2 eq. (34)

import Mathlib
import Definitions.Def_STOC2027BoolCSP_Approximation_Instance
import Definitions.Def_STOC2027BoolCSP_Approximation_Encoding

namespace STOC2027BoolCSP.Approximation

open MeasureTheory ProbabilityTheory Matrix

/-- A signed conjunction on `k` distinct variables of `Fin n` (Section 2, printed p. 6):
`C : x_{vars j} = σ_{C,j}` for `j < k`, the sign `σ_{C,j} ∈ {-1,1}` encoded by `sign j`
(`true ↦ 1`). -/
structure Conj (n k : ℕ) where
  vars : Fin k → Fin n
  vars_inj : Function.Injective vars
  sign : Fin k → Bool

/-- A weighted instance of signed `k`-conjunctions: `n` variables, `M` clauses, rational weights. -/
structure ConjInstance (k : ℕ) where
  n : ℕ
  M : ℕ
  clause : Fin M → Conj n k
  w : Fin M → ℚ

/-- Index set of the Gram matrix of (5): the shared block `Fin (n+1)` (index `0` is the reference
vector `e`, index `i+1` the decision vector `d_i`) followed by one clause vector `z_C` per clause. -/
abbrev Idx (n M : ℕ) := Fin (n + 1) ⊕ Fin M

/-- The index of the reference vector `e`. -/
def eIdx {n M : ℕ} : Idx n M := Sum.inl 0

/-- The index of the decision vector `d_i`. -/
def dIdx {n M : ℕ} (i : Fin n) : Idx n M := Sum.inl i.succ

/-- The index of the clause vector `z_C`. -/
def zIdx {n M : ℕ} (c : Fin M) : Idx n M := Sum.inr c

namespace ConjInstance

variable {k : ℕ} (C : ConjInstance k)

/-- The Section 7 standing normalization (equation (4)): nonnegative weights summing to one. -/
def Normalized : Prop := (∀ c, 0 ≤ C.w c) ∧ ∑ c, C.w c = 1

/-- The affine space `𝒜` of Section 7.1 (printed p. 13): symmetric real matrices with unit
shared-vector diagonals, `G_{e,z_C} = G_{z_C,z_C}` and `G_{d_i,z_C} = σ_{C,i} G_{z_C,z_C}` for
every literal `i ∈ C`. -/
def InAffine (G : Matrix (Idx C.n C.M) (Idx C.n C.M) ℝ) : Prop :=
  G.IsSymm ∧ (∀ i : Fin (C.n + 1), G (Sum.inl i) (Sum.inl i) = 1) ∧
  (∀ c, G eIdx (zIdx c) = G (zIdx c) (zIdx c)) ∧
  (∀ c j, G (dIdx ((C.clause c).vars j)) (zIdx c) =
    sgnOf ((C.clause c).sign j) * G (zIdx c) (zIdx c))

/-- The feasible region `𝓕 = {G ∈ 𝒜 : G ⪰ 0}` of the common-reference relaxation (5). -/
def Feasible (G : Matrix (Idx C.n C.M) (Idx C.n C.M) ℝ) : Prop :=
  C.InAffine G ∧ G.PosSemidef

/-- The objective `f(G) = Σ_C w_C q_C` with `q_C = G_{z_C,z_C}`. -/
noncomputable def objective (G : Matrix (Idx C.n C.M) (Idx C.n C.M) ℝ) : ℝ :=
  ∑ c, (C.w c : ℝ) * G (zIdx c) (zIdx c)

/-- The value `SDP` of relaxation (5): the supremum (in fact the maximum) of the objective over
the feasible region, which is nonempty and bounded. -/
noncomputable def sdpValue : ℝ := sSup (C.objective '' {G | C.Feasible G})

/-- A feasible vector solution of (5) in the space `ι → ℝ` (any finite dimension):
`⟨e,e⟩ = 1`, `⟨d_i,d_i⟩ = 1`, `q_C = ⟨z_C,z_C⟩ = ⟨e,z_C⟩`, `⟨σ_{C,i} d_i, z_C⟩ = q_C`. -/
def VecFeasible {ι : Type} [Fintype ι] (v : Idx C.n C.M → ι → ℝ) : Prop :=
  v eIdx ⬝ᵥ v eIdx = 1 ∧ (∀ i, v (dIdx i) ⬝ᵥ v (dIdx i) = 1) ∧
  (∀ c, v (zIdx c) ⬝ᵥ v (zIdx c) = v eIdx ⬝ᵥ v (zIdx c)) ∧
  (∀ c j, sgnOf ((C.clause c).sign j) * (v (dIdx ((C.clause c).vars j)) ⬝ᵥ v (zIdx c)) =
    v (zIdx c) ⬝ᵥ v (zIdx c))

/-- The noise parameter `δ = π/m`, `m = k + 1`, of the rounding (28). -/
noncomputable def roundDelta (k : ℕ) : ℝ := Real.pi / ((k : ℝ) + 1)

/-- The sign of a score with ties broken at `+1` (`true` means `+1`). -/
noncomputable def signB (s : ℝ) : Bool := decide (0 ≤ s)

/-- The rounding (28)–(29) of a vector solution, as a function of the Gaussian sample
`(g, ξ_0, …, ξ_n)`: `S_0 = √δ⟨g,e⟩ + √(1-δ) ξ_0`, `S_i = √δ⟨g,d_i⟩ + √(1-δ) ξ_i` and
`x_i = sgn(S_i) sgn(S_0)`, one reference score `S_0` shared by all variables. -/
noncomputable def roundAssign {ι : Type} [Fintype ι] (v : Idx C.n C.M → ι → ℝ)
    (ω : (ι → ℝ) × (Fin (C.n + 1) → ℝ)) : Fin C.n → Bool := fun i =>
  let δ := roundDelta k
  let S0 := Real.sqrt δ * (ω.1 ⬝ᵥ v eIdx) + Real.sqrt (1 - δ) * ω.2 0
  let Si := Real.sqrt δ * (ω.1 ⬝ᵥ v (dIdx i)) + Real.sqrt (1 - δ) * ω.2 i.succ
  signB Si == signB S0

/-- The Gaussian law of the rounding sample: `g` standard Gaussian on `ι → ℝ`, independent of the
independent standard normal scalars `ξ_0, …, ξ_n`. -/
noncomputable def roundMeasure (ι : Type) [Fintype ι] (n : ℕ) :
    Measure ((ι → ℝ) × (Fin (n + 1) → ℝ)) :=
  (Measure.pi fun _ : ι => gaussianReal 0 1).prod (Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1)

/-- `Pr(C is satisfied)` under the rounding (28)–(29). -/
noncomputable def clauseProb {ι : Type} [Fintype ι] (v : Idx C.n C.M → ι → ℝ) (c : Fin C.M) : ℝ :=
  (roundMeasure ι C.n).real
    {ω | ∀ j, C.roundAssign v ω ((C.clause c).vars j) = (C.clause c).sign j}

/-- Code of a conjunction instance: `k`, the variable list in unary, then the list of clauses
(variables, sign bits, rational weight). -/
def code : List Bool :=
  natCode k ++ unaryCode C.n ++
    listCode (fun c : Fin C.M =>
      (List.ofFn (C.clause c).vars).flatMap (fun v => natCode v.val) ++
        List.ofFn (C.clause c).sign ++ ratCode (C.w c)) (List.finRange C.M)

end ConjInstance

/-- The indices of the Gram matrix in their fixed order `e, d_1, …, d_n, z_1, …, z_M`. -/
def idxList (n M : ℕ) : List (Idx n M) :=
  (List.finRange (n + 1)).map Sum.inl ++ (List.finRange M).map Sum.inr

/-- Code of a rational Gram matrix, row by row in the order `idxList`. -/
def gramCode {n M : ℕ} (G : Matrix (Idx n M) (Idx n M) ℚ) : List Bool :=
  (idxList n M).flatMap fun i => (idxList n M).flatMap fun j => ratCode (G i j)

/-- Code of a rational `N × N` matrix: `N` in unary, then the entries row by row. -/
def sqMatCode {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ) : List Bool :=
  unaryCode N ++ (List.finRange N).flatMap fun i => (List.finRange N).flatMap fun j => ratCode (A i j)

/-- The rational-to-real cast of a matrix. -/
def ratToReal {α β : Type} (A : Matrix α β ℚ) : Matrix α β ℝ := A.map (fun q => (q : ℝ))

/-- The covariance `H = δB + (1-δ) I_N` of the shared score vector, equation (34). -/
noncomputable def scoreCov (k : ℕ) {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  ConjInstance.roundDelta k • B + (1 - ConjInstance.roundDelta k) • (1 : Matrix (Fin N) (Fin N) ℝ)

open scoped MatrixOrder in
/-- The positive semidefinite square root `H^{1/2}` of a real positive semidefinite matrix
(Mathlib's continuous functional calculus `CFC.sqrt` for the Loewner order; it is the unique PSD
matrix whose square is `H`, and the same square root `multivariateGaussian` uses). -/
noncomputable def psdSqrt {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  CFC.sqrt H

/-- The Euclidean (`ℓ²`) operator norm of a real square matrix. -/
noncomputable def opNorm {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖

/-- The Frobenius norm `‖E‖_F = (Σ_{i,j} E_{ij}²)^{1/2}`. -/
noncomputable def frobNorm {α : Type} [Fintype α] (E : Matrix α α ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, E i j ^ 2)

end STOC2027BoolCSP.Approximation


