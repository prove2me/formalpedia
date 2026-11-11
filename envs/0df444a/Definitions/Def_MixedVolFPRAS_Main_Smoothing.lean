-- Prove2me | Definitions.Def_MixedVolFPRAS_Main_Smoothing
-- name    : MixedVolFPRAS_Main_Smoothing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:29:44.14243+00:00
-- url     : https://prove2.me/theorems/c35a24e1-81fa-4c66-8e5b-cf544c7df899
-- title:
--   The (t, λ)-smoothing of a support function (Definition 4.2)
-- statement:
--   Let $K\subseteq\mathbb{R}^n$ be a convex body and $t,\lambda>0$. The **$(t,\lambda)$-smoothing** of $h_K$ is
--
--   $$\tilde h(x)=\mathbb{E}\big[h_K(x+t\|x\|_2Z)\big]+\lambda\|x\|_2,\qquad Z\sim\mathcal{N}(0,I_n).$$
--
--   It is a Gaussian variant of the Schneider transform; Propositions 4.3 and 4.4 show it is the support function of a slightly larger, smooth body.
--
--   **Formalization Note.** `smoothing K t lam x` is `∫ z, supportFunction K (x + (t * ‖x‖) • z) ∂(stdGaussian (E n)) + lam * ‖x‖`, with Mathlib's standard Gaussian measure on `E n`. For compact $K$ the integrand is Lipschitz in $z$, so the integral is a genuine finite expectation.
-- source:
--   Chen, Liu, An FPRAS for Mixed Volumes, STOC 2027 submission (manuscript sha256 0acf8d97…), p. 17, Definition 4.2

import Mathlib
import Definitions.Def_MixedVolFPRAS_Main_ConvexGeometry

noncomputable section

namespace MixedVolFPRAS.Main

/-!
# The `(t, λ)`-smoothing of a support function (Definition 4.2)

Chen, Liu, *An FPRAS for Mixed Volumes*, p. 17, Definition 4.2:
`h̃(x) = E[h_K(x + t‖x‖₂ Z)] + λ‖x‖₂` with `Z ∼ N(0, Iₙ)` (Mathlib's `stdGaussian` on `ℝⁿ`).
The integrand is Lipschitz in `Z` for compact `K`, so the expectation is a genuine (finite)
Gaussian integral.
-/

/-- The `(t, λ)`-smoothing `h̃` of `h_K` (Definition 4.2); `lam` stands for `λ`. -/
def smoothing {n : ℕ} (K : Set (E n)) (t lam : ℝ) (x : E n) : ℝ :=
  (∫ z, supportFunction K (x + (t * ‖x‖) • z) ∂(ProbabilityTheory.stdGaussian (E n))) +
    lam * ‖x‖

end MixedVolFPRAS.Main


