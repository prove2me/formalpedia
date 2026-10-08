-- Prove2me | Definitions.Def_SAGA_Convex_sagaStep
-- name    : SAGA_Convex_sagaStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T13:24:46.997365+00:00
-- url     : https://prove2.me/theorems/f46b37bc-b311-4495-93a3-8761d5b61a22
-- title:
--   One SAGA step, the point $w^{k+1}$ and the gradient error $\Delta$
-- statement:
--   The SAGA method keeps a current iterate $x^k\in\mathbb R^d$ and a table of points $\phi_1^k,\dots,\phi_n^k$ (equivalently, the stored gradients $f_i'(\phi_i^k)$). Given a step size $\gamma$, a map $P$ (the proximal operator $\mathrm{prox}^h_\gamma$) and a sampled index $j$, one iteration is:
--
--   1. the gradient step
--   $$
--   w^{k+1}=x^k-\gamma\Big[f_j'(x^k)-f_j'(\phi_j^k)+\frac1n\sum_{i=1}^n f_i'(\phi_i^k)\Big],
--   $$
--   where the table average uses the **old** table $\phi^k$;
--   2. the proximal step $x^{k+1}=P(w^{k+1})$;
--   3. the table update $\phi_j^{k+1}=x^k$ and $\phi_i^{k+1}=\phi_i^k$ for $i\ne j$.
--
--   The **gradient error** at this step is
--   $$
--   \Delta=-\frac1\gamma\big(w^{k+1}-x^k\big)-f'(x^k),
--   $$
--   the difference between the SAGA estimate of the gradient at $x^k$ and the true gradient $f'(x^k)$.
--
--   These are the update (1)–(2) of the paper (p. 2) and the quantity $\Delta$ of the proof of Theorem 2 (p. 11).
--
--   **Formalization Note** The state is the pair $(x^k,\phi^k)$ with $\phi^k$ a function `Fin n → E`; storing the points $\phi_i$ is equivalent to storing $f_i'(\phi_i)$. `sagaW` is $w^{k+1}$, `sagaStep` returns $(x^{k+1},\phi^{k+1})$, `sagaDelta` is $\Delta$. Indices are 0-based.
-- source:
--   Defazio, Bach & Lacoste-Julien, SAGA, arXiv:1407.0202v3, p. 2, SAGA Algorithm, eqs. (1)-(2); p. 11, definition of Delta in the proof of Theorem 2

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum

namespace SAGA.Convex

/-- The point `w^{k+1}` of eq. (1) (p. 2) for the state `s = (x^k, φ^k)` and the sampled index
`j`: `w = x^k - γ (f′_j(x^k) - f′_j(φ_j^k) + (1/n) ∑ᵢ f′ᵢ(φᵢ^k))`. The table average uses the old
table `φ^k`. -/
noncomputable def sagaW {d n : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℝ)
    (s : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d))) (j : Fin n) :
    EuclideanSpace ℝ (Fin d) :=
  s.1 - γ • (f' j s.1 - f' j (s.2 j) + (1 / (n : ℝ)) • ∑ i, f' i (s.2 i))

/-- One SAGA iteration (p. 2, steps 1–3 and eqs. (1)–(2)) from the state `s = (x^k, φ^k)` with
the index `j`: the new iterate is `x^{k+1} = P(w^{k+1})`, where `P` plays the role of
`prox_γ^h`, and the table entry `j` is overwritten by `x^k`, all other entries unchanged. -/
noncomputable def sagaStep {d n : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℝ)
    (s : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d))) (j : Fin n) :
    EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d)) :=
  (P (sagaW f' γ s j), Function.update s.2 j s.1)

/-- The gradient-estimation error `Δ = -(1/γ)(w^{k+1} - x^k) - f′(x^k)` (Appendix C, p. 11) for
the state `s = (x^k, φ^k)` and the index `j`. -/
noncomputable def sagaDelta {d n : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℝ)
    (s : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d))) (j : Fin n) :
    EuclideanSpace ℝ (Fin d) :=
  -(1 / γ) • (sagaW f' γ s j - s.1) - gradAvg f' s.1

end SAGA.Convex


