-- Prove2me | Definitions.Def_DynChoiceJEO_Supplement_weightedRegretAgainst
-- name    : DynChoiceJEO_Supplement_weightedRegretAgainst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:12:31.844802+00:00
-- url     : https://prove2.me/theorems/5702d5f8-29a0-5a71-9a38-90c6fd797bc2
-- title:
--   Weighted regret (14) of $z_1,\dots,z_T$ against a comparator $u$
-- statement:
--   In online convex optimization over rounds $t=1,\dots,T$, decisions $z_t$ are charged real losses $h_t(z_t)$ with weights $\theta_t$. With $\Theta_T=\sum_{t\in[T]}\theta_t$, the **weighted regret against a comparator** $u$ is
--
--   $$
--   \mathcal R_T(u):=\frac1{\Theta_T}\sum_{t\in[T]}\theta_th_t(z_t)-\frac1{\Theta_T}\sum_{t\in[T]}\theta_th_t(u).
--   $$
--
--   The weighted regret (14) of the paper on a set $Z$,
--
--   $$
--   \frac1{\Theta_T}\sum_{t\in[T]}\theta_th_t(z_t)-\min_{z\in Z}\frac1{\Theta_T}\sum_{t\in[T]}\theta_th_t(z),
--   $$
--
--   is the supremum of $\mathcal R_T(u)$ over $u\in Z$. With $Z=Y$ and $h_t=-\Psi(x_t,\cdot;p_t)$ it becomes the dual regret $\mathcal R_y$ of the saddle-point framework.
--
--   **Formalization Note** A bound $B$ on the weighted regret (14) is stated as $\mathcal R_T(u)\le B$ for every $u\in Z$, which does not depend on the minimum being attained or finite. Rounds are the natural numbers $1,\dots,T$ and index $0$ is unused. For $\Theta_T=0$ the value is $0$; the theorems using the definition have $\Theta_T>0$.
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Dynamic Data-Driven Estimation of Non-Parametric Choice Models, arXiv:1702.05702v5, eq. (14), p.15; eq. (EC.11), p.ec7 (PDF 29)

import Mathlib

namespace DynChoiceJEO.Supplement

/-- **Weighted regret (14) against a comparator `u`.**
Ho-Nguyen & Kılınç-Karzan, *Dynamic Data-Driven Estimation of Non-Parametric Choice Models*,
arXiv:1702.05702v5, eq. (14), p.15: "(1/Θ_T) ∑_{t∈[T]} θ_t h_t(z_t) − min_{z∈Z} (1/Θ_T) ∑_{t∈[T]} θ_t h_t(z)",
with `Θ_T = ∑_{t∈[T]} θ_t` (also (EC.11), p.ec7, PDF 29).

`weightedRegretAgainst T θ h z u` is the same difference with the fixed decision `u` in place of
the minimizer: the weighted average loss of `z_1, …, z_T` minus that of `u`.

**Formalization Note** The weighted regret (14) on `Z` is the supremum of this quantity over
`u ∈ Z`, so "weighted regret `≤ B`" is `∀ u ∈ Z, weightedRegretAgainst T θ h z u ≤ B`. This form
does not depend on the minimum being attained or finite. Rounds are numbered `1, …, T`
(`Finset.Icc 1 T`); index `0` is unused. When `Θ_T = 0` the value is `0`; the theorems using it
have `Θ_T > 0`. -/
noncomputable def weightedRegretAgainst {E : Type*} (T : ℕ) (θ : ℕ → ℝ) (h : ℕ → E → ℝ)
    (z : ℕ → E) (u : E) : ℝ :=
  (∑ t ∈ Finset.Icc 1 T, θ t)⁻¹ * ∑ t ∈ Finset.Icc 1 T, θ t * h t (z t)
    - (∑ t ∈ Finset.Icc 1 T, θ t)⁻¹ * ∑ t ∈ Finset.Icc 1 T, θ t * h t u

end DynChoiceJEO.Supplement


