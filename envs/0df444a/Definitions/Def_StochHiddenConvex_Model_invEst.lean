-- Prove2me | Definitions.Def_StochHiddenConvex_Model_invEst
-- name    : StochHiddenConvex_Model_invEst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:52:41.345598+00:00
-- url     : https://prove2.me/theorems/51249dd0-b0c6-4daa-b686-538a2c6d47bf
-- title:
--   The randomized Neumann-series estimator (9) of $[\nabla g(x)]^{-1}$
-- statement:
--   Fix an integer $K>0$ and a constant $c>1$. Draw $k$ uniformly from $\{0,\dots,K-1\}$ and i.i.d. samples $\xi^1,\dots,\xi^k$ from $\mathbb P(\xi)$, and set
--   $$[\nabla\hat g(x)]^{-1}=\begin{cases}\dfrac{K}{cL_\phi}\displaystyle\prod_{i=1}^{k}\Big(I-\frac{\nabla\phi(x,\xi^i)}{cL_\phi}\Big)&k\ge1,\\[2mm]\dfrac{K}{cL_\phi}I&k=0.\end{cases}\qquad(9)$$
--   The definition gives the $i$-th diagonal entry of this diagonal matrix as a function of $k$ and the samples, together with the law of $(k,\text{samples})$. Its expectation truncates the Neumann series $[\nabla g(x)]^{-1}=\frac1{cL_\phi}\sum_{k\ge0}(I-\nabla g(x)/(cL_\phi))^k$ after $K$ terms (Lemma 2.2).
--
--   **Formalization Note** Drawing $k$ and then $k$ samples is encoded as drawing $k$ uniform on `Fin K` and $K-1$ i.i.d. samples of which the first $k$ are used; this changes no law.
-- source:
--   X. Chen, N. He, Y. Hu, Z. Ye, Efficient Algorithms for A Class of Stochastic Hidden Convex Optimization and Its Applications in Network Revenue Management, arXiv:2205.01774v3, Eq. (9), p.13

import Mathlib
import Definitions.Def_StochHiddenConvex_Model_gradG

open MeasureTheory ProbabilityTheory

namespace StochHiddenConvex

namespace Model

variable {d : ℕ} (M : Model d)

/-- The randomized Neumann-series estimator (9) of `[∇g(x)]⁻¹` (Chen, He, Hu & Ye,
arXiv:2205.01774v3, (9), p.13): for an integer `K > 0` and `c > 1`, draw `k` uniformly from
`{0, …, K − 1}` and i.i.d. samples `ξ¹, …, ξᵏ` from `ℙ(ξ)`, and form
`[∇ĝ(x)]⁻¹ = (K/(cL_ϕ)) ∏_{i=1}^{k} (I − ∇ϕ(x, ξⁱ)/(cL_ϕ))` (`= (K/(cL_ϕ)) I` for `k = 0`).
This is the `i`-th diagonal entry of that (diagonal) matrix, for `k : Fin K` and a block
`ss : Fin (K − 1) → ℝ^d` of samples of which the first `k` are used.

**Formalization Note.** Drawing `k` and then `k` samples is encoded as drawing `k` and `K − 1`
i.i.d. samples, of which the first `k` are used (`estMeasure`); this changes no law. -/
noncomputable def invEst (c Lphi : ℝ) (K : ℕ) (x : Vec d) (k : Fin K)
    (ss : Fin (K - 1) → Fin d → ℝ) (i : Fin d) : ℝ :=
  (K : ℝ) / (c * Lphi) *
    ∏ j ∈ Finset.univ.filter (fun j : Fin (K - 1) => (j : ℕ) < (k : ℕ)),
      (1 - M.dphi i (x i) (ss j i) / (c * Lphi))

/-- The law of the randomness of estimator (9) (arXiv:2205.01774v3, p.13): `k` uniform on
`{0, …, K − 1}`, independent of `K − 1` i.i.d. samples from `ℙ(ξ)`. -/
noncomputable def estMeasure [IsProbabilityMeasure M.P] (K : ℕ) :
    Measure (Fin K × (Fin (K - 1) → Fin d → ℝ)) :=
  (uniformOn (Set.univ : Set (Fin K))).prod (Measure.pi fun _ : Fin (K - 1) => M.P)

end Model

end StochHiddenConvex


