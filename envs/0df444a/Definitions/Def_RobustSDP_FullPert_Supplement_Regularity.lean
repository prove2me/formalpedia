-- Prove2me | Definitions.Def_RobustSDP_FullPert_Supplement_Regularity
-- name    : RobustSDP_FullPert_Supplement_Regularity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:45:28.749951+00:00
-- url     : https://prove2.me/theorems/44560e1a-5d81-4abd-ac2c-530aaa92712f
-- title:
--   C1 data families, O(‖u‖) suboptimality, Hölder regularity, and problems (21), (23), (25)
-- statement:
--   For Euclidean parameter vectors $u\in\mathbb R^k$, an accuracy budget is a nonnegative function $\varepsilon(u)$ for which some $K\ge0$ bounds $\varepsilon(u)\le K\|u\|$ near zero. This is exactly $\varepsilon=O(\|u\|)$; no numerical constant is specified in the source. A point is $\varepsilon$-suboptimal for feasible set $C$ and objective $c^Tx$ when it is feasible and $c^Tx\le c^Tz+\varepsilon$ for every $z\in C$. At the locally attained optima considered here, this equals $c^Tx\le v+\varepsilon$.
--
--   `HolderRegular` states that for every such budget there are $\gamma,\delta>0$ such that
--   $$\|x-x_0\|_2\le\gamma\sqrt{\|u\|_2}$$
--   for every $\|u\|_2<\delta$ and every budget-suboptimal point of the perturbed feasible set. `SmoothSDPFamily` requires coefficientwise $C^1$ dependence near zero of $F_i,R_i,L$ and symmetric $F_i$. `projected15` existentially eliminates the SDP auxiliary $\tau$.
--
--   The same module defines the full matrix constraint (21), its strict Slater condition, bounded objective sublevels H2, and coefficientwise symmetric $C^1$ matrix families. For (23) it defines the independent Euclidean perturbation of every LP row $(a_i,b_i)$, the exact constraints $a_i^Tx-\rho\sqrt{1+\|x\|_2^2}\ge b_i$, strict feasibility, and $C^1$ perturbation of all row data. Finally it defines the largest eigenvalue `lamMax` (the least $t$ with $tI-A\succeq0$, used for symmetric $A$ of positive size), the objective $\lambda_{\max}(F(x))+2\rho\sqrt{\|x\|_2^2+1}$ of (25), solutions of (25) and of the nominal problem (24), the minimum-norm nominal solution, local Lipschitz stability of the solution of (25) under symmetric perturbations of $F_0,\dots,F_m$, and the two data sets used against Theorem 5.3: $F(x)=[x]$ and $F_e(x)=\begin{pmatrix}x-1&e\\e&1-x\end{pmatrix}$.
--
--   **Formalization Note.** Euclidean parameter norms use `EuclideanSpace`; decision norms use explicit sums of squares. Comparison with every feasible objective avoids a real infimum on an empty or unbounded set. The $C^1$ conditions are `ContDiffAt` at zero, which provides the required local $C^1$ neighborhood. No global smoothness, numerical big-O constant, or bounded parameter set is added.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), pp. 40–43, §4.4 and §5.1, §5.3–§5.4

import Mathlib
import Definitions.Def_RobustSDP_Uniqueness_Model
import Definitions.Def_RobustSDP_Uniqueness_Hypotheses
import Definitions.Def_RobustSDP_Unstructured_Model
import Definitions.Def_RobustSDP_FullPert_Supplement_NormMin

open Matrix Filter Topology
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.FullPert.Supplement

/-- Euclidean parameter vectors in §4.4. -/
abbrev Param (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- The usual epsilon = O(norm u) at zero, with a nonnegative accuracy budget.
The existential constant is part of big-O notation, not a numerical source constant. -/
def AccuracyBudget {k : ℕ} (ε : Param k → ℝ) : Prop :=
  (∀ u, 0 ≤ ε u) ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ u in 𝓝 (0 : Param k), ε u ≤ K * ‖u‖

/-- Global minimization of c^T x over a feasible set. -/
def LinearOptimal {m : ℕ} (C : Set (Fin m → ℝ)) (c x : Fin m → ℝ) : Prop :=
  x ∈ C ∧ ∀ z ∈ C, c ⬝ᵥ x ≤ c ⬝ᵥ z

/-- The set S_epsilon of §4.4 without a potentially junk-valued real infimum.
When an optimum exists, comparison with every feasible objective is exactly
c^T x <= v + epsilon; this definition also says explicitly that x is feasible. -/
def LinearSuboptimal {m : ℕ} (C : Set (Fin m → ℝ)) (c : Fin m → ℝ) (ε : ℝ)
    (x : Fin m → ℝ) : Prop :=
  x ∈ C ∧ ∀ z ∈ C, c ⬝ᵥ x ≤ c ⬝ᵥ z + ε

/-- All epsilon-suboptimal points of a parameterized family obey the Holder-1/2
estimate (18), for every accuracy budget epsilon = O(norm u). -/
def HolderRegular {k m : ℕ} (C : Param k → Set (Fin m → ℝ))
    (c x0 : Fin m → ℝ) : Prop :=
  ∀ ε : Param k → ℝ, AccuracyBudget ε →
    ∃ γ : ℝ, 0 < γ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ u : Param k, ‖u‖ < δ → ∀ x : Fin m → ℝ,
        LinearSuboptimal (C u) c (ε u) x → euclidNorm (x - x0) ≤ γ * Real.sqrt ‖u‖

/-- Coefficientwise C1 dependence near zero, exactly as in §4.4.
The coefficients are finite arrays; C1 is independent of which equivalent finite-dimensional
norm is used for them. Symmetry of F is the standing SDP convention. -/
def SmoothSDPFamily {k m n p q : ℕ}
    (A : Param k → RobustSDP.Uniqueness.SDPData m n p q) : Prop :=
  (∀ u, (A u).Symmetric) ∧
  ContDiffAt ℝ 1 (fun u => (A u).F0) 0 ∧
  (∀ i, ContDiffAt ℝ 1 (fun u => (A u).Fs i) 0) ∧
  ContDiffAt ℝ 1 (fun u => (A u).L) 0 ∧
  ContDiffAt ℝ 1 (fun u => (A u).R0) 0 ∧
  (∀ i, ContDiffAt ℝ 1 (fun u => (A u).Rs i) 0)

/-- Project (15)-feasibility onto x; the auxiliary tau is not an arbitrary constructed object. -/
def projected15 {m n p q : ℕ} (A : RobustSDP.Uniqueness.SDPData m n p q) :
    Set (Fin m → ℝ) := {x | ∃ τ : ℝ, A.Feasible (x, τ)}

/-- Constraint (21), with Euclidean vector norm and spectral matrix conventions. -/
noncomputable def set21 {m n : ℕ}
    (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) : Set (Fin m → ℝ) :=
  {x | (RobustSDP.Unstructured.affineMap Fs x -
    (2 * ρ * Real.sqrt (∑ i, x i ^ 2 + 1)) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef}

/-- H1 for the convex matrix constraint (21). -/
def Slater21 {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) : Prop :=
  ∃ x : Fin m → ℝ, (RobustSDP.Unstructured.affineMap Fs x -
    (2 * ρ * Real.sqrt (∑ i, x i ^ 2 + 1)) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef

/-- H2 for a problem with feasible set C. Finite-dimensional closed constraints make bounded
sublevels compact. The source's H2 is not replaced by mere nonemptiness. -/
def InfCompactSet {m : ℕ} (C : Set (Fin m → ℝ)) (c : Fin m → ℝ) : Prop :=
  ∀ M : ℝ, Bornology.IsBounded {x | x ∈ C ∧ c ⬝ᵥ x ≤ M}

/-- Coefficientwise C1 symmetric matrix perturbations for Theorem 5.1. -/
def SmoothSymmetricFamily {k m n : ℕ}
    (A : Param k → Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ u i, (A u i).IsSymm) ∧ ∀ i, ContDiffAt ℝ 1 (fun u => A u i) 0

/-- Independent rowwise Euclidean uncertainty in (a_i,b_i), §5.3.
Coordinate zero perturbs b_i and the remaining coordinates perturb a_i. -/
def robustLPSet {m l : ℕ} (a : Fin l → Fin m → ℝ) (b : Fin l → ℝ) (ρ : ℝ) :
    Set (Fin m → ℝ) :=
  {x | ∀ i : Fin l, ∀ d : EuclideanSpace ℝ (Fin (m + 1)), ‖d‖ ≤ ρ →
    (∑ j : Fin m, (a i j + d j.succ) * x j) ≥ b i + d 0}

/-- The full SOCP counterpart (23), with the source constant rho. -/
def set23 {m l : ℕ} (a : Fin l → Fin m → ℝ) (b : Fin l → ℝ) (ρ : ℝ) :
    Set (Fin m → ℝ) :=
  {x | ∀ i : Fin l, a i ⬝ᵥ x - ρ * Real.sqrt (∑ j, x j ^ 2 + 1) ≥ b i}

/-- Strict feasibility H1 for (23). -/
def Slater23 {m l : ℕ} (a : Fin l → Fin m → ℝ) (b : Fin l → ℝ) (ρ : ℝ) : Prop :=
  ∃ x : Fin m → ℝ, ∀ i : Fin l, a i ⬝ᵥ x - ρ * Real.sqrt (∑ j, x j ^ 2 + 1) > b i

/-- C1 perturbation of every LP coefficient a_i,b_i, at fixed rho. -/
def SmoothLPFamily {k m l : ℕ} (a : Param k → Fin l → Fin m → ℝ)
    (b : Param k → Fin l → ℝ) : Prop :=
  (∀ i, ContDiffAt ℝ 1 (fun u => a u i) 0) ∧ ∀ i, ContDiffAt ℝ 1 (fun u => b u i) 0

/-- The largest eigenvalue `λmax(A)` of a symmetric `n × n` matrix (`n ≥ 1`), as the least `t`
with `tI − A ⪰ 0`. (For `n ≥ 1` and symmetric `A` this set is `[λmax(A), ∞)`; the definition is
only used at symmetric matrices with `n ≥ 1`.) -/
noncomputable def lamMax {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sInf {t : ℝ | (t • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef}

/-- The objective of the robust eigenvalue problem (25), p. 43:
`λmax(F(x)) + 2ρ√(‖x‖² + 1)`, with `F(x) = F₀ + ∑ᵢ xᵢFᵢ` and `‖x‖` Euclidean. -/
noncomputable def eigenObj25 {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ)
    (x : Fin m → ℝ) : ℝ :=
  lamMax (RobustSDP.Unstructured.affineMap Fs x) + 2 * ρ * Real.sqrt (∑ i, x i ^ 2 + 1)

/-- `x` solves (25): it minimizes `eigenObj25` over all of `ℝ^m`. -/
def IsEigenSolution25 {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ)
    (x : Fin m → ℝ) : Prop :=
  ∀ x' : Fin m → ℝ, eigenObj25 Fs ρ x ≤ eigenObj25 Fs ρ x'

/-- `x` solves the nominal problem (24): it minimizes `λmax(F(x))` over all of `ℝ^m`. -/
def IsNominalEigenSolution {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin m → ℝ) : Prop :=
  ∀ x' : Fin m → ℝ, lamMax (RobustSDP.Unstructured.affineMap Fs x) ≤
    lamMax (RobustSDP.Unstructured.affineMap Fs x')

/-- `x` is the minimum (Euclidean) norm solution of the nominal problem (24). -/
def IsMinNormNominalEigenSolution {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin m → ℝ) : Prop :=
  IsNominalEigenSolution Fs x ∧
    ∀ x' : Fin m → ℝ, IsNominalEigenSolution Fs x' → euclidNorm x ≤ euclidNorm x'

/-- Local Lipschitz stability of the solution of (25) at fixed `ρ` with respect to symmetric
perturbations of `F₀, …, F_m` (spectral norm), as claimed in Theorem 5.3. Kept as a predicate so
that its failure can be stated. -/
def EigenSolutionLipschitz {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) :
    Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (Fs' : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (η : ℝ), η < ε → (∀ i, (Fs' i).IsSymm) →
      (∀ i, ‖Fs' i - Fs i‖ ≤ η) → ∀ x x' : Fin m → ℝ,
        IsEigenSolution25 Fs ρ x → IsEigenSolution25 Fs' ρ x' → euclidNorm (x' - x) ≤ C * η

/-- Scalar data `F(x) = [x]` (`F₀ = 0`, `F₁ = 1`, `m = n = 1`): the nominal objective of (24)
is `x`, which is unbounded below. -/
def eigenScalarData : Fin 2 → Matrix (Fin 1) (Fin 1) ℝ :=
  ![!![0], !![1]]

/-- Symmetric `2 × 2` data `F_e(x) = [[x − 1, e], [e, 1 − x]]`, whose largest eigenvalue is
`√((x − 1)² + e²)`; used against the Lipschitz clause of Theorem 5.3. -/
def eigenLipCounterexampleData (e : ℝ) : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ :=
  ![!![-1, e; e, 1], !![1, 0; 0, -1]]

end RobustSDP.FullPert.Supplement


