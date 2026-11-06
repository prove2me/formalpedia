-- Prove2me | Definitions.Def_MatchedUCLB_baseSeq
-- name    : MatchedUCLB_baseSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:31:32.216772+00:00
-- url     : https://prove2.me/theorems/37373f49-0bc8-4edb-9f90-046dfa610421
-- title:
--   The partial bases $B_j$ of the uniformly convex base
-- statement:
--   Fix $q$, $\mu>0$ and phase displacements $h_0,h_1,\dots\in\mathbb R^d$, with centers $c_j=\sum_{k<j}h_k$ and $R_j=\|h_j\|$. The **partial bases** $B_j:\mathbb R^d\to\mathbb R$ are defined by $B_0(x)=\frac{\mu}{q}\|x\|^q$ and
--
--   $$
--   B_{j+1}(x)=\begin{cases}M_{\delta^B_j}\bigl(B_j(x),\,N^B_j(x)\bigr),&\|x-c_{j+1}\|<\theta R_j,\\ B_j(x),&\|x-c_{j+1}\|\ge\theta R_j,\end{cases}
--   $$
--
--   where
--
--   $$
--   N^B_j(x)=B_j(c_{j+1})+C_j+\langle\nabla B_j(c_{j+1}),x-c_{j+1}\rangle+\frac{\mu}{q}\|x-c_{j+1}\|^q,\qquad C_j=a_{\mathrm{lift}}\mu\theta^2R_j^q,\quad \delta^B_j=\frac{C_j}{4}.
--   $$
--
--   The base of the construction is $B=B_L$. Each step reproduces the Euclidean $q$th-power geometry at the next center by a local replacement inside the ball of radius $\theta R_j$.
--
--   **Formalization Note** $\langle\nabla B_j(c),x-c\rangle$ is `fderiv ℝ (B_j) c (x - c)`. No differentiability is built in; Lemma 4.3 asserts that every $B_j$ is $p$ times continuously differentiable.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Step 1, Eqs. (4.3), (4.4), (4.6), pp.5–6

import Mathlib
import Definitions.Def_MatchedUCLB_center
import Definitions.Def_MatchedUCLB_smoothMax
import Definitions.Def_MatchedUCLB_aLift
import Definitions.Def_MatchedUCLB_theta

namespace MatchedUCLB

/-- **The partial bases `B_j`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Step 1, pp.5–6: "we begin with `B_0(x) = (μ/q)‖x‖^q`";
Eq. (4.3): `N^B_j(x) = B_j(c_{j+1}) + C_j + ⟨∇B_j(c_{j+1}), x − c_{j+1}⟩ + (μ/q)‖x − c_{j+1}‖^q`;
Eq. (4.4): `B_{j+1}(x) = M_{δ^B_j}(B_j(x), N^B_j(x))` if `‖x − c_{j+1}‖ < θR_j` and `B_{j+1}(x) = B_j(x)`
if `‖x − c_{j+1}‖ ≥ θR_j`; Eq. (4.6): `C_j = a_lift μ θ² R_j^q`, `δ^B_j = C_j/4`; `R_j = ‖h_j‖`.

`baseSeq q μ h j` is `B_j`; the base of the construction is `B = B_L = baseSeq q μ h L`.

**Formalization Note.** `⟨∇B_j(c), x − c⟩` is `fderiv ℝ B_j c (x − c)`. No differentiability is
built into the definition: by Lemma 4.3 every `B_j` is `C^p`, so the derivative is genuine. The
strict `<` of (4.4) is kept. -/
noncomputable def baseSeq (q μ : ℝ) {d : ℕ} (h : ℕ → EuclideanSpace ℝ (Fin d)) : ℕ → EuclideanSpace ℝ (Fin d) → ℝ
  | 0 => fun x => μ / q * ‖x‖ ^ q
  | j + 1 => fun x =>
      if ‖x - center h (j + 1)‖ < theta q * ‖h j‖ then
        smoothMax (aLift q * μ * theta q ^ 2 * ‖h j‖ ^ q / 4) (baseSeq q μ h j x)
          (baseSeq q μ h j (center h (j + 1)) + aLift q * μ * theta q ^ 2 * ‖h j‖ ^ q +
            fderiv ℝ (baseSeq q μ h j) (center h (j + 1)) (x - center h (j + 1)) +
            μ / q * ‖x - center h (j + 1)‖ ^ q)
      else baseSeq q μ h j x

end MatchedUCLB


