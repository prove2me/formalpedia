-- Prove2me | Definitions.Def_ProdMixedTomo_Weights
-- name    : ProdMixedTomo_Weights
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:17:33.371239+00:00
-- url     : https://prove2.me/theorems/9006e5f3-965c-4d7a-9703-61e532bda3e2
-- title:
--   Weights $\Gamma_N$, $w(S)$, $\mathcal W_{N,\epsilon}$, weighted mean $\mu(w)$ and covariance $\Sigma(w)$
-- statement:
--   For a list of points $X_1,\dots,X_N\in\mathbb R^n$ (§4.1):
--   $$
--   \Gamma_N=\Bigl\{w\in\mathbb R^N:\ \sum_iw_i\le1,\ w_i\ge0\Bigr\},\qquad w(T)_i=\tfrac1N\mathbf 1_{i\in T},
--   $$
--   $w\le w'$ coordinatewise, and for $w\in\Gamma_N\setminus\{0\}$
--   $$
--   \mu(w)=\frac1{\|w\|_1}\sum_iw_iX_i,\qquad \Sigma(w)=\frac1{\|w\|_1}\sum_iw_i(X_i-\mu(w))(X_i-\mu(w))^\top .
--   $$
--   The filter's weights are $\mathcal W_{N,\epsilon}=\{w\in\Gamma_N:\ w\le w(S),\ \|w-w(S)\|_1\le3\epsilon\}$, and $\mathrm{nnz}(w)$ counts the nonzero entries. The empirical mean and covariance of the list are $\mu(T)=\frac1N\sum_iX_i$ and $\frac1N\sum_i(X_i-\mu(T))(X_i-\mu(T))^\top$, and the covariance of $\mathrm{Bern}(\mu)$ is $\mathbb E_{X\sim\mathrm{Bern}(\mu)}(X-\mu)(X-\mu)^\top$.
--
--   **Formalization Note** $\mu(w)$ and $\Sigma(w)$ are total ($0$ at $w=0$ by Lean's $0^{-1}=0$), a value no theorem uses. The covariance of $\mathrm{Bern}(\mu)$ is the finite expectation sum, not its closed form.
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), §4.1, pp.21–22 (PDF pp.23–24); §2 Notation, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_ProdMixedTomo_States
import Definitions.Def_ProdMixedTomo_BinaryProduct

namespace ProdMixedTomo

/-!
# Weights `Γ_N`, `w(T)`, `𝒲_{N,ϵ}`, weighted mean and covariance, empirical moments

Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*,
arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), §4.1 "The set 𝒲_{N,ϵ}",
pp.21–22 (PDF pp.23–24):
`Γ_N = {w ∈ ℝ^N : Σ wᵢ ≤ 1, wᵢ ≥ 0}`; `w(T)ᵢ = (1/N)·1[i ∈ T]`; `w ≤ w'` coordinatewise;
`μ(w) = ‖w‖₁⁻¹ Σ wᵢ Xᵢ`, `Σ(w) = ‖w‖₁⁻¹ Σ wᵢ (Xᵢ − μ(w))(Xᵢ − μ(w))ᵀ` for `w ∈ Γ_N \ {0}`;
`𝒲_{N,ϵ} = {w ∈ Γ_N : w ≤ w(S), ‖w − w(S)‖₁ ≤ 3ϵ}`; `nnz(w)` the number of nonzero entries.
§2 Notation, p.13: `μ(S)` is the empirical mean, `E[f(S)]` the uniform average over `S`.

**Formalization Note.** A sample set is a list `X : Fin N → ℝⁿ` of points (indices are
associated with points, p.21). `μ(w)` and `Σ(w)` are defined for every `w` (Lean's `0⁻¹ = 0`
makes them `0` at `w = 0`, a value never used by the theorems, which only evaluate them at
`w ≠ 0`). `w(S) = wAll N` is the uniform weight `1/N`. The covariance of `Bern(μ)` is the
expectation `E_{X∼Bern μ}(X − μ)(X − μ)ᵀ`, written as a finite sum.
-/

open Matrix

/-- The allowable weights `Γ_N`. -/
def Gamma (N : ℕ) : Set (Fin N → ℝ) := {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i ≤ 1}

/-- `w(T)`: weight `1/N` on the indices in `T`, `0` elsewhere. -/
noncomputable def wOf {N : ℕ} (T : Finset (Fin N)) : Fin N → ℝ :=
  fun i => if i ∈ T then 1 / (N : ℝ) else 0

/-- `w(S)`, the uniform weight `1/N` on all `N` points. -/
noncomputable def wAll (N : ℕ) : Fin N → ℝ := wOf Finset.univ

/-- `𝒲_{N,ϵ}`. -/
noncomputable def Wset (N : ℕ) (ϵ : ℝ) : Set (Fin N → ℝ) :=
  {w | w ∈ Gamma N ∧ (∀ i, w i ≤ wAll N i) ∧ ∑ i, |w i - wAll N i| ≤ 3 * ϵ}

/-- The weighted mean `μ(w) = ‖w‖₁⁻¹ Σ wᵢ Xᵢ`. -/
noncomputable def wMean {n N : ℕ} (X : Fin N → Fin n → ℝ) (w : Fin N → ℝ) : Fin n → ℝ :=
  (∑ i, w i)⁻¹ • ∑ i, w i • X i

/-- The weighted covariance `Σ(w) = ‖w‖₁⁻¹ Σ wᵢ (Xᵢ − μ(w))(Xᵢ − μ(w))ᵀ`. -/
noncomputable def wCov {n N : ℕ} (X : Fin N → Fin n → ℝ) (w : Fin N → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (∑ i, w i)⁻¹ • ∑ i, w i • vecMulVec (X i - wMean X w) (X i - wMean X w)

/-- `nnz(w)`, the number of nonzero entries. -/
noncomputable def nnz {N : ℕ} (w : Fin N → ℝ) : ℕ :=
  (Finset.univ.filter fun i => w i ≠ 0).card

/-- The empirical mean `μ(T) = (1/N) Σ Xᵢ`. -/
noncomputable def empMean {n N : ℕ} (X : Fin N → Fin n → ℝ) : Fin n → ℝ :=
  (N : ℝ)⁻¹ • ∑ i, X i

/-- The empirical covariance `E_{X∼T}(X − μ(T))(X − μ(T))ᵀ`. -/
noncomputable def empCov {n N : ℕ} (X : Fin N → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (N : ℝ)⁻¹ • ∑ i, vecMulVec (X i - empMean X) (X i - empMean X)

/-- The covariance `E_{X∼Bern μ}(X − μ)(X − μ)ᵀ` of the binary product distribution. -/
noncomputable def popCov {n : ℕ} (μ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ x : Cube n, bern μ x • vecMulVec (bitVec x - μ) (bitVec x - μ)

/-- A list of cube points as real vectors. -/
def pts {n N : ℕ} (S : Fin N → Cube n) : Fin N → Fin n → ℝ := fun i => bitVec (S i)

end ProdMixedTomo


