-- Prove2me | Definitions.Def_ConjGrad_ErrorDecrease_Supplement_cfConv
-- name    : ConjGrad_ErrorDecrease_Supplement_cfConv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T01:53:19.397743+00:00
-- url     : https://prove2.me/theorems/a049eefb-1c9d-4eea-8620-db37c253337a
-- title:
--   Convergents of the continued fraction (18:2) and the characteristic polynomial of $A$ with respect to $r_0$
-- statement:
--   Given numbers $a_0,a_1,\dots$ and $c_1,c_2,\dots$ (with $c_0=0$), put $d_i=1+c_i$ and consider the continued fraction (18:2)
--
--   $$-\cfrac{1}{d_0-a_0\lambda-\cfrac{c_1}{d_1-a_1\lambda-\cfrac{c_2}{\ddots-\cfrac{c_{n-1}}{d_{n-1}-a_{n-1}\lambda}}}} .$$
--
--   Its $i$-th convergent is $N_i/R_i$: the denominators satisfy (18:3), $R_0=1$, $R_1=1-a_0\lambda$, $R_{i+1}=(1+c_i-a_i\lambda)R_i-c_iR_{i-1}$, and the numerators satisfy the same recursion from $N_0=0$, $N_1=-1$. The normalization $d_i=1+c_i$ is the one the paper imposes on p. 432 so that $R_i(0)=1$, in agreement with (14:3) and (15:1)–(15:2).
--
--   The **characteristic polynomial of $A$ with respect to $r_0$** (p. 432) is
--
--   $$Q_{n-1}(\lambda)=r_0^{\mathsf T}\,\operatorname{adj}(\lambda I-A)\,r_0 ,$$
--
--   which for symmetric $A$ with orthonormal eigenvectors $e_j$, eigenvalues $\lambda_j$ and $m_j=(r_0,e_j)^2$ equals $\sum_{i=1}^n m_i\prod_{j\ne i}(\lambda-\lambda_j)$, the numerator of $F(\lambda)=\sum_j m_j/(\lambda-\lambda_j)=Q_{n-1}(\lambda)/\det(\lambda I-A)$ (18:1).
--
--   Finally, for the cg-process the numbers $c_i$ of (15:4) are $c_0=0$ and $c_i=b_{i-1}a_i/a_{i-1}$ for $i\ge1$.
--
--   **Formalization Note** `cfConv a c i` is the pair $(N_i,R_i)$ of real polynomials; `relCharPoly A r₀` is $Q_{n-1}$ written with the adjugate of the characteristic matrix $\lambda I-A$ (coordinate free, equal to the paper's weighted sum for symmetric $A$); `cgCoeffC A k x₀ i` is $c_i$ computed from the published iteration (with $t/0=0$).
--
--   `spectralFunction lam w t` is the partial fraction sum $\sum_j w_j/(t-\lambda_j)$ of (18:1), used away from the nodes; the source has distinct positive nodes and positive weights.
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 431, §18, eqs. (18:1)–(18:3); p. 432, definition of $Q_{n-1}$; eq. (15:4) on p. 430 (PDF p. 23)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter

open Matrix Polynomial

namespace ConjGrad.ErrorDecrease.Supplement

/-- Numerator and denominator `(Nᵢ, Rᵢ)` of the `i`-th convergent of the continued fraction
(18:2) (p. 431)
`−1/((d₀ − a₀λ) − c₁/((d₁ − a₁λ) − ⋯ − cₙ₋₁/(dₙ₋₁ − aₙ₋₁λ)))` with `c₀ = 0` and the
normalization `dᵢ = 1 + cᵢ` (p. 432, from (15:2)). The denominators satisfy (18:3):
`R₀ = 1`, `R₁ = 1 − a₀λ`, `Rᵢ₊₁ = (1 + cᵢ − aᵢλ)Rᵢ − cᵢRᵢ₋₁`; the numerators satisfy the same
recursion from `N₀ = 0`, `N₁ = −1`. The `n`-th convergent is `Nₙ/Rₙ`. -/
noncomputable def cfConv (a c : ℕ → ℝ) : ℕ → Polynomial ℝ × Polynomial ℝ
  | 0 => (0, 1)
  | 1 => (-1, 1 - C (a 0) * X)
  | i + 2 =>
    let s := cfConv a c (i + 1)
    let t := cfConv a c i
    let q := C (1 + c (i + 1)) - C (a (i + 1)) * X
    (q * s.1 - C (c (i + 1)) * t.1, q * s.2 - C (c (i + 1)) * t.2)

/-- The spectral rational function (18:1), away from its poles; total division is used at poles.
The source domain has distinct positive nodes and positive weights. -/
noncomputable def spectralFunction {n : ℕ} (lam w : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ j, w j / (t - lam j)

/-- The characteristic polynomial of `A` with respect to `r₀` (p. 432):
`Qₙ₋₁(λ) = r₀ᵀ adj(λI − A) r₀`. For symmetric `A` with orthonormal eigenvectors `eⱼ`,
eigenvalues `λⱼ` and `mⱼ = (r₀, eⱼ)²` this is `∑ⱼ mⱼ ∏_{k ≠ j} (λ − λₖ)`. -/
noncomputable def relCharPoly {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (r₀ : Fin n → ℝ) :
    Polynomial ℝ :=
  ∑ i, ∑ j, C (r₀ i * r₀ j) * (adjugate (charmatrix A)) i j

/-- The numbers `cᵢ` of (15:4) attached to the cg-process: `c₀ = 0` and
`cᵢ = bᵢ₋₁aᵢ/aᵢ₋₁` for `i ≥ 1`, with `aᵢ`, `bᵢ` the scalars (5:1b), (5:1e) of the cg-method
started at `x₀`. -/
noncomputable def cgCoeffC {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k x₀ : Fin n → ℝ) : ℕ → ℝ
  | 0 => 0
  | i + 1 =>
    ((cgIter A k x₀ (i + 1)).r ⬝ᵥ (cgIter A k x₀ (i + 1)).r) /
        ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) *
      cgAlpha A (cgIter A k x₀ (i + 1)) / cgAlpha A (cgIter A k x₀ i)

end ConjGrad.ErrorDecrease.Supplement


