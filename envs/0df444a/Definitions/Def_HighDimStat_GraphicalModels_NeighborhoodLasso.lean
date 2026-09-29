-- Prove2me | Definitions.Def_HighDimStat_GraphicalModels_NeighborhoodLasso
-- name    : HighDimStat_GraphicalModels_NeighborhoodLasso
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:20:33.853775+00:00
-- url     : https://prove2.me/theorems/d904a277-aee8-4a34-9e73-b15067f7b030
-- title:
--   Incoherence, the Gaussian random design and the neighborhood-Lasso estimator
-- statement:
--   This file collects the apparatus behind §11.2.2's neighborhood-based graph-selection
--   method, needed to state Theorem 11.12.
--
--   - **`IsAlphaIncoherent Γ T S α`**: $\Gamma$ (over ambient index set $T$) is
--     $\alpha$-incoherent with respect to $S\subseteq T$ (Eq. (11.23)):
--     $\max_{k\in T\setminus S}\|\Gamma_{kS}(\Gamma_{SS})^{-1}\|_1\le 1-\alpha$.
--   - **`opNormInfty A`**: the $\ell_\infty$-matrix-operator norm
--     $|\!|\!|A|\!|\!|_\infty:=\max_i\sum_j|A_{ij}|$.
--   - **`IsZeroMeanGaussianVector X P Sig`** / **`IsIIDGaussianDesign Xdes P Sig`**: $X$ is a
--     zero-mean Gaussian vector with covariance $\mathrm{Sig}$, characterized via every linear
--     combination being univariate Gaussian with the matching variance; `IsIIDGaussianDesign`
--     is $n$ i.i.d. copies — the random design of the neighborhood-regression procedure.
--   - **`IsNeighborhoodLassoSolution Xdes j ω lam θhat`**: $\hat\theta$ solves the
--     neighborhood-regression Lasso program (11.22) at vertex $j$ for the design realized at
--     $\omega$.
--   - **`estimatedNeighborhood θhat`**, **`orRuleEdges Nhat`**, **`andRuleEdges Nhat`**: the
--     estimated neighborhood read off a Lasso solution's support, and the OR/AND rules
--     (p. 361) combining per-vertex neighborhood estimates into a single estimated edge set.
--
--   **Formalization Note** `IsAlphaIncoherent`'s ambient set `T` plays the role of the book's
--   $\Sigma^*_{\backslash\{j\}}$'s own index set ($V$ minus $j$), realized as a subset of the
--   full index type rather than a literal sub-matrix, since no entry indexed outside $T$ is
--   ever referenced by the definition. The Gaussian design is characterized via linear
--   combinations (avoiding a dependency on Mathlib's multivariate-Gaussian machinery) rather
--   than via an explicit density.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, pp. 359-361 (PDF pp. 379-381), Eqs. (11.20), (11.21), (11.22), (11.23)

import Mathlib

namespace HighDimStat.GraphicalModels

open MeasureTheory ProbabilityTheory

/-- The submatrix of `Γ` on the index set `S` (a `Finset`), viewed as a square matrix indexed
by the subtype `{i // i ∈ S}`. -/
def submatrixOn {I : Type*} (Γ : Matrix I I ℝ) (S : Finset I) :
    Matrix {i // i ∈ S} {i // i ∈ S} ℝ :=
  fun a b => Γ a.1 b.1

/-- `Γ` is `α`-incoherent, over the ambient index set `T`, with respect to `S ⊆ T`
(Eq. (11.23), p. 361): `max_{k∈T∖S} ‖Γ_{kS}(Γ_{SS})^{-1}‖₁ ≤ 1 − α`, where `Γ_{kS}(Γ_{SS})^{-1}`
is the row vector of optimal linear-prediction coefficients. `T` plays the role of the book's
`Σ*_{\{j}}`'s own index set (all of `V` except `j`), realized here directly as a subset of
`Γ`'s full index set rather than as a literal sub-matrix, since no entry indexed outside `T`
is ever referenced. -/
def IsAlphaIncoherent {I : Type*} [Fintype I] [DecidableEq I] (Γ : Matrix I I ℝ)
    (T S : Finset I) (α : ℝ) : Prop :=
  ∀ k ∈ T, k ∉ S →
    (∑ a : {i // i ∈ S}, |Matrix.vecMul (fun b : {i // i ∈ S} => Γ k b.1) (submatrixOn Γ S)⁻¹ a|)
      ≤ 1 - α

/-- The `ℓ∞`-matrix-operator norm `|||A|||∞ := max_i Σⱼ |A_{ij}|` (p. 361, just before
Theorem 11.12): the maximum absolute row sum. -/
noncomputable def opNormInfty {I : Type*} [Fintype I] (A : Matrix I I ℝ) : ℝ :=
  ⨆ i, ∑ j, |A i j|

/-- `X` is a zero-mean Gaussian random vector on `V` with covariance `Σ` (used throughout
§11.2): every linear combination `⟨w, X⟩` is Gaussian with mean `0` and variance
`wᵀΣw` — the standard characterization of a multivariate Gaussian law via its
one-dimensional projections. -/
def IsZeroMeanGaussianVector {V Ω : Type*} [Fintype V] [MeasurableSpace Ω] (X : Ω → V → ℝ)
    (P : Measure Ω) (Sig : Matrix V V ℝ) : Prop :=
  ∀ w : V → ℝ, Measure.map (fun ω => ∑ j, w j * X ω j) P =
    gaussianReal 0 (Real.toNNReal (∑ j, ∑ k, w j * w k * Sig j k))

/-- `n` i.i.d. copies `Xdes : Fin n → Ω → V → ℝ` of a zero-mean Gaussian vector with
covariance `Σ` — the random design of §11.2.2's neighborhood-regression procedure. -/
def IsIIDGaussianDesign {V Ω : Type*} [Fintype V] [MeasurableSpace Ω] {n : ℕ}
    (Xdes : Fin n → Ω → V → ℝ) (P : Measure Ω) (Sig : Matrix V V ℝ) : Prop :=
  (∀ i, Measurable (Xdes i)) ∧ iIndepFun Xdes P ∧ ∀ i, IsZeroMeanGaussianVector (Xdes i) P Sig

/-- `θhat` solves the neighborhood-regression Lasso program (11.22) at vertex `j` for the
random design realized at `ω`: `θhat` minimizes
`(1/(2n))‖X_j − X_{\{j\}}θ‖₂² + λₙ‖θ‖₁` over `θ ∈ ℝ^{V∖{j}}`. -/
def IsNeighborhoodLassoSolution {V Ω : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (Xdes : Fin n → Ω → V → ℝ) (j : V) (ω : Ω) (lam : ℝ) (θhat : {k : V // k ≠ j} → ℝ) : Prop :=
  ∀ β : {k : V // k ≠ j} → ℝ,
    (1 / (2 * (n : ℝ))) * (∑ i, (Xdes i ω j - ∑ k, θhat k * Xdes i ω k.1) ^ 2)
        + lam * (∑ k, |θhat k|) ≤
    (1 / (2 * (n : ℝ))) * (∑ i, (Xdes i ω j - ∑ k, β k * Xdes i ω k.1) ^ 2)
        + lam * (∑ k, |β k|)

/-- The estimated neighborhood of `j`, read off the Lasso solution's support (§11.2.2, step
1(c)): `k ≠ j` is included in `N̂(j)` iff `θhat k ≠ 0`. -/
def estimatedNeighborhood {V : Type*} [DecidableEq V] {j : V} (θhat : {k : V // k ≠ j} → ℝ) :
    Set V :=
  {k : V | ∃ h : k ≠ j, θhat ⟨k, h⟩ ≠ 0}

/-- The OR-rule estimated edge set (p. 361): `(j,k) ∈ Ê_OR` iff `k ∈ N̂(j)` or `j ∈ N̂(k)`. -/
def orRuleEdges {V : Type*} [DecidableEq V] (Nhat : ∀ j : V, Set V) : Set (V × V) :=
  {p : V × V | p.1 ≠ p.2 ∧ (p.2 ∈ Nhat p.1 ∨ p.1 ∈ Nhat p.2)}

/-- The AND-rule estimated edge set (p. 361): `(j,k) ∈ Ê_AND` iff `k ∈ N̂(j)` and `j ∈ N̂(k)`. -/
def andRuleEdges {V : Type*} [DecidableEq V] (Nhat : ∀ j : V, Set V) : Set (V × V) :=
  {p : V × V | p.1 ≠ p.2 ∧ p.2 ∈ Nhat p.1 ∧ p.1 ∈ Nhat p.2}

end HighDimStat.GraphicalModels


