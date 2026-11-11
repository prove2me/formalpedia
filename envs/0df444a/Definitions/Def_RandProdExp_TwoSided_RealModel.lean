-- Prove2me | Definitions.Def_RandProdExp_TwoSided_RealModel
-- name    : RandProdExp_TwoSided_RealModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:20:20.962294+00:00
-- url     : https://prove2.me/theorems/7d15cc24-b5ca-44ff-aa34-0eb35e950ca7
-- title:
--   Real Rademacher model, expectation over signs, Euclidean operator norm, the plane-interaction matrix $K$ and the sparse blocks $T_\lambda$ (Definitions 6.2, 6.11; §8 setup)
-- statement:
--   **Random model** (Definition 6.2). For integers $1\le k_i\le n$, take independent uniform signs $\sigma^{(i)}_{r,j}\in\{-1,1\}$ and the normalized Rademacher matrices $G_i=k_i^{-1/2}(\sigma^{(i)}_{r,j})\in\mathbb R^{k_i\times n}$, whose columns have norm one. In this model $\tau_M:=\bar\beta_M^G$ on $\mathcal G(M):=\operatorname{Coker}\alpha_M^G$, with no rank condition. $\mathbb E_\sigma$ and $\Pr_\sigma$ are the uniform average and the uniform counting probability over all sign matrices.
--
--   The **Euclidean operator norm** $\|A\|_{\mathrm{op}}$ of a real matrix is its norm as a linear map between Euclidean spaces (§3.5.1).
--
--   **Plane-interaction matrix** (Definitions 6.5, 6.11). With $\tau_P=\tau_{P\to[n]^D}$ and adjoints for the standard inner products, $K:U\to U$, $U=\bigoplus_{P\in\mathcal P_\cap(M)}U_P$, has blocks
--   $$K_{P,Q}=\begin{cases}0,&P\cap Q\neq\emptyset,\\ \tau_P^\dagger\tau_Q,&P\cap Q=\emptyset.\end{cases}$$
--
--   **Sparse blocks** (§8 setup, Proposition 8.1). For $D_j=G_j^\top G_j-\mathrm{Id}_{\mathbb R^n}$ and $X,Y\subseteq[n]^q$, $T=\Pi_X(\bigotimes_{j=1}^qD_j)\iota_Y:\mathbb R^Y\to\mathbb R^X$, the matrix with entries $T(x,y)=\prod_jD_j(x_j,y_j)$.
--
--   The plane-interaction matrix is the operator whose norm controls the injectivity of $\tau_M$ over the reals; the sparse blocks are the pieces into which it is decomposed.
--
--   **Formalization Note** `signAvg f` is $\frac1{|\Omega|}\sum_{\omega\in\Omega}f(\omega)$ and `signProb E` is $|\{\omega:E(\omega)\}|/|\Omega|$ over the finite sign space $\Omega$. `opNorm A` is the norm of `Matrix.toEuclideanLin A` as a continuous linear map. `interactionMatrix M σ` has entry $\sum_w\tau_P(w,v)\tau_Q(w,v')$ at $((P,v),(Q,v'))$ when $P\cap Q=\emptyset$ (the $(v,v')$ entry of $\tau_P^\top\tau_Q$) and $0$ otherwise, including $P=Q$. `sparseBlock σ X Y` takes $X,Y$ as finite sets.
-- source:
--   Chattopadhyay, Ringach, Spooner, Product Expansion of Random Codes via Analytic Techniques, STOC 2027 submission (manuscript sha256 9e4ac2d1…), p. 24 (§3.5.1); p. 35, Definition 6.2; pp. 36–39, Definitions 6.5, 6.11; p. 49, Proposition 7.9; p. 55, §8 Setup

import Mathlib
import Definitions.Def_RandProdExp_TwoSided_Grid
import Definitions.Def_RandProdExp_TwoSided_Diagram

namespace RandProdExp.TwoSided

/-!
# The real Rademacher model, the Euclidean operator norm, the plane-interaction matrix `K`, and the
# sparse tensor blocks `T_λ` of §8

Chattopadhyay, Ringach, Spooner, *Product Expansion of Random Codes via Analytic Techniques*,
STOC 2027 submission: Definition 6.2 (p. 35), Definitions 6.5 and 6.11 (pp. 36, 39), §3.5.1 (Euclidean
operator norm, p. 24), Proposition 7.9 (p. 49), §8 Setup (p. 55).

Expectations and probabilities "over the signs" are uniform averages over the finite set of all sign
matrices (independent uniform `±1` entries).
-/

variable {D n : ℕ}

/-- The expectation `E_σ[f(σ)]` of a real function of uniformly random signs: the uniform average
over the finite sign space `Ω`. -/
noncomputable def signAvg {Ω : Type} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / (Fintype.card Ω : ℝ)

open Classical in
/-- The probability `Pr_σ[E]` of an event of uniformly random signs: uniform counting probability. -/
noncomputable def signProb {Ω : Type} [Fintype Ω] (E : Ω → Prop) : ℝ :=
  (Fintype.card {ω // E ω} : ℝ) / (Fintype.card Ω : ℝ)

/-- The **normalized Rademacher matrix** `G = k^{−1/2} (σ_{r,c})_{r ∈ [k], c ∈ [n]} ∈ ℝ^{k × n}`
(Definition 6.2; Proposition 7.9): each column has Euclidean norm `1`. -/
noncomputable def normRademacher {k : ℕ} (σ : Matrix (Fin k) (Fin n) ℤˣ) : Matrix (Fin k) (Fin n) ℝ :=
  fun r c => (Real.sqrt k)⁻¹ * (((σ r c : ℤˣ) : ℤ) : ℝ)

/-- The real random model of Definition 6.2: `G_i = k_i^{−1/2} σ^{(i)}` for every `i ∈ [D]`. -/
noncomputable def normTuple {k : Fin D → ℕ} (σ : SignTuple k n) :
    (i : Fin D) → Matrix (Fin (k i)) (Fin n) ℝ :=
  fun i => normRademacher (σ i)

/-- The **Euclidean operator norm** `‖A‖_op` of a real matrix `A ∈ ℝ^{m × n}`, as a linear map
`ℓ²(n) → ℓ²(m)` (§3.5.1). -/
noncomputable def opNorm {m p : Type} [Fintype m] [Fintype p] [DecidableEq p] (A : Matrix m p ℝ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖

/-- `τ_M := β̄_M^G` injective in the real model of Definition 6.2 (`G(M) := Coker α_M^G`; no rank
condition on the `G_i`). -/
def RealTauInjective (M : Set (Fin D → Fin n)) {k : Fin D → ℕ} (σ : SignTuple k n) : Prop :=
  BarInjective M (normTuple σ)

open Classical in
/-- The **plane-interaction matrix** `K : U → U`, `U = ⊕_{P ∈ P∩(M)} U_P` (Definition 6.11), in the
real model of Definition 6.2: block `K_{P,Q} = 0` if `P ∩ Q ≠ ∅` and `K_{P,Q} = τ_P^† τ_Q` if
`P ∩ Q = ∅`, where `τ_P = τ_{P → [n]^D}` (Definition 6.5) and adjoints are for the standard inner
products. Entry `((P, v), (Q, v'))` of `τ_P^† τ_Q` is `Σ_w τ_P(w, v) τ_Q(w, v')`. -/
noncomputable def interactionMatrix (M : Set (Fin D → Fin n)) {k : Fin D → ℕ} (σ : SignTuple k n) :
    Matrix (UIdx M k) (UIdx M k) ℝ :=
  fun y y' =>
    if (planeOf y.1.1 ∩ planeOf y'.1.1).Nonempty then 0
    else ∑ w, betaMat M (normTuple σ) w y * betaMat M (normTuple σ) w y'

/-- `D = Gᵀ G − Id_{ℝ^n}` for a matrix `G ∈ ℝ^{k × n}` (§8 Setup, Definition 7.4). -/
def gramMinusId {k : ℕ} (G : Matrix (Fin k) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  G.transpose * G - 1

/-- The restricted operator `T = Π_X (⊗_{j=1}^q D_j) ι_Y : ℝ^Y → ℝ^X` of Proposition 8.1, for
`X, Y ⊆ [n]^q`, `D_j = G_jᵀ G_j − Id` and `G_j` the normalized Rademacher matrices of the signs
`σ^{(j)}`: its entry at `(x, y)` is `Π_j D_j(x_j, y_j)`. -/
noncomputable def sparseBlock {q : ℕ} {k : Fin q → ℕ} (σ : (j : Fin q) → Matrix (Fin (k j)) (Fin n) ℤˣ)
    (X Y : Finset (Fin q → Fin n)) : Matrix X Y ℝ :=
  fun x y => ∏ j : Fin q, gramMinusId (normRademacher (σ j)) (x.1 j) (y.1 j)

end RandProdExp.TwoSided


