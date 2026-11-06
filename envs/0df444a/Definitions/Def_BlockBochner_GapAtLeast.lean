-- Prove2me | Definitions.Def_BlockBochner_GapAtLeast
-- name    : BlockBochner_GapAtLeast
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:25.70784+00:00
-- url     : https://prove2.me/theorems/97b033aa-cb0d-4522-95ba-1950b9a751dc
-- title:
--   Spectral gap at least $\gamma$: $\lambda_2(L)\ge\gamma$
-- statement:
--   For a bounded operator $L$ on a real inner product space, the paper defines the spectral gap $\lambda_2(L)$ as the maximal $\lambda\ge0$ with $L^2-\lambda L\succeq0$, and sets $\lambda_2(L)=0$ when $\dim\ker L\ge2$. The predicate "$\lambda_2(L)\ge\gamma$" is
--   $$\gamma\,\langle f,Lf\rangle\le\|Lf\|^2\ \text{ for all }f\qquad\text{and}\qquad\dim\ker L\le1 .$$
--
--   For self-adjoint $L$ and $\gamma>0$ this is exactly $\lambda_2(L)\ge\gamma$: the admissible $\lambda$ form a closed interval containing $0$, so the maximum is at least $\gamma$ iff $L^2-\gamma L\succeq0$.
--
--   **Formalization Note** The kernel dimension is `Module.rank` (a cardinal), so an infinite-dimensional kernel violates the bound. No real-valued $\lambda_2$ is defined.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 1.1, pp.2–3

import Mathlib

namespace BlockBochner

/-- **Spectral gap at least `γ`: `λ₂(L) ≥ γ`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 1.1, pp.2–3: for a Laplacian `L` the
spectral gap `λ₂(L)` is the maximal `λ ≥ 0` with `L² − λL ⪰ 0`, set to `0` when `dim ker L ≥ 2`.
`GapAtLeast L γ` says `⟨f, L f⟩ γ ≤ ‖L f‖²` for every `f` (i.e. `L² − γL ⪰ 0` for self-adjoint `L`)
and `dim ker L ≤ 1`.

**Formalization Note** For `γ > 0` and self-adjoint `L` this is exactly `λ₂(L) ≥ γ`: the set of
`λ ≥ 0` with `L² − λL ⪰ 0` is a closed interval containing `0`, so its maximum is at least `γ` iff
`L² − γL ⪰ 0`, and `λ₂(L) = 0 < γ` whenever `dim ker L ≥ 2`. The kernel dimension is
`Module.rank` (a cardinal), so an infinite-dimensional kernel violates the bound. No real-valued
`λ₂` is defined (a real supremum would take a junk value when the set is unbounded). -/
def GapAtLeast {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : E →L[ℝ] E) (γ : ℝ) :
    Prop :=
  (∀ f, γ * inner ℝ f (L f) ≤ ‖L f‖ ^ 2) ∧ Module.rank ℝ (LinearMap.ker L.toLinearMap) ≤ 1

end BlockBochner


