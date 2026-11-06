-- Prove2me | Definitions.Def_FeedbackSwitching_IsBalancedEstimator
-- name    : FeedbackSwitching_IsBalancedEstimator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:41:49.231751+00:00
-- url     : https://prove2.me/theorems/952a01a1-2572-4146-8e2f-7afdb96aec1f
-- title:
--   $L_0$-balanced estimator (Definition 5)
-- statement:
--   Let $w$ be a positive probability vector, $(p,x)$ as in Definition 2 with $\lambda_s=x_s/p_s$, and $L_0\ge1$. Matrices $\Psi_s$, $s\in[K]$, form an **$L_0$-balanced estimator** for $(w,p,x)$ if
--
--   1. each product $\Psi_s\ell$ is computable from the comparisons observed when $s$ is played;
--   2. $\Psi_s\mathbf 1=0$ for every $s$, and $\sum_sp_s\Psi_s=C_w$;
--   3. the error matrices $E_s=\Psi_s-C_w$ satisfy, for every $f$,
--   $$
--   \sum_s\frac{p_s}{\lambda_s}\|E_sf\|_w^2\le L_0\,\mathrm{Var}_p(f),\qquad\sum_sp_s\|E_sf\|_w^2\le L_0\,\mathrm{Var}_x(f);
--   $$
--   4. $\|\Psi_s\ell\|_\infty\le L_0\lambda_s$ for every $s$ and every $\ell\in[0,1]^K$.
--
--   **Formalization Note** (1) is invariance under loss vectors in $[0,1]^K$ with the same comparisons at $s$; $\|\cdot\|_\infty$ is written coordinatewise.
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Definition 5, Eq. (35), p.29 (PDF p.31)

import Mathlib
import Definitions.Def_FeedbackSwitching_tScore
import Definitions.Def_FeedbackSwitching_holdingP
open Matrix

namespace FeedbackSwitching

/-- Cesa-Bianchi et al., arXiv:2606.03851 (held version, sha256 ded8f8bc…).

**Balanced estimator** (Definition 5, Eq. (35), p.29 = PDF p.31). Matrices `Ψ_s` form an
`L₀`-balanced estimator for `(w, p, x)` (tournament `A`) if
(i) each `Ψ_s ℓ` is computable from the comparisons observed when `s` is played;
(ii) `Ψ_s 1 = 0` for every `s`, and `∑_s p_s Ψ_s = C_w`;
(iii) the error matrices `E_s = Ψ_s − C_w` satisfy, for every `f`,
`∑_s (p_s/λ_s) ‖E_s f‖²_w ≤ L₀ Var_p(f)` and `∑_s p_s ‖E_s f‖²_w ≤ L₀ Var_x(f)`;
(iv) `‖Ψ_s ℓ‖_∞ ≤ L₀ λ_s` for every `s` and every `ℓ ∈ [0,1]^K`.

**Formalization Note.** (i) is invariance under loss vectors in `[0,1]^K` with the same
comparisons at `s`; `‖·‖_∞` is written coordinatewise. -/
def IsBalancedEstimator {K : ℕ} (A : Fin K → Fin K → Prop) (w p x : Fin K → ℝ)
    (Ψ : Fin K → Matrix (Fin K) (Fin K) ℝ) (L₀ : ℝ) : Prop :=
  (∀ s ℓ ℓ', InUnitCube ℓ → InUnitCube ℓ' → sameComparisons A s ℓ ℓ' → Ψ s *ᵥ ℓ = Ψ s *ᵥ ℓ') ∧
  (∀ s, Ψ s *ᵥ (fun _ => (1 : ℝ)) = 0) ∧ ∑ s, p s • Ψ s = centering w ∧
  (∀ f, ∑ s, p s / lam p x s * wNormSq w ((Ψ s - centering w) *ᵥ f) ≤ L₀ * wVar p f) ∧
  (∀ f, ∑ s, p s * wNormSq w ((Ψ s - centering w) *ᵥ f) ≤ L₀ * wVar x f) ∧
  ∀ s ℓ, InUnitCube ℓ → ∀ i, |(Ψ s *ᵥ ℓ) i| ≤ L₀ * lam p x s

end FeedbackSwitching


