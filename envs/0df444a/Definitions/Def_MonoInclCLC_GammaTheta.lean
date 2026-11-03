-- Prove2me | Definitions.Def_MonoInclCLC_GammaTheta
-- name    : MonoInclCLC_GammaTheta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:19:20.529149+00:00
-- url     : https://prove2.me/theorems/ca4d1457-5561-482b-894b-c48247e4c6a0
-- title:
--   Lemma 2.5, p.6 — the function $\Gamma_\theta$
-- statement:
--   For an integer $p\ge 2$ and $\theta>0$, the function $\Gamma_\theta:\mathcal H\to\mathbb R$ is
--   $$
--   \Gamma_\theta(x)=\Big(\inf\big\{\alpha>0:\ \|x-(I+\alpha^{-1}A)^{-1}x\|\le\alpha^{\frac{1}{p-1}}\theta^{\frac{1}{p-1}}\big\}\Big)^{\frac{1}{p-1}}.
--   $$
--   It rewrites the implicitly defined feedback law as an explicit infimum, and its Lipschitz continuity is what makes the feedback law well behaved.
--
--   **Formalization Note** The paper prints the codomain $(0,+\infty)$; here $\Gamma_\theta$ is real-valued, because it vanishes on $A^{-1}(0)$ by the paper's own Lemma 2.5. The infimum is a real infimum over a nonempty set bounded below by $0$, so no default value occurs.
-- source:
--   Lin, Jordan, Monotone Inclusions, Acceleration and Closed-Loop Control, arXiv:2111.08093v4, Lemma 2.5, p.6 (the display defining Γθ)

import Mathlib

namespace MonoInclCLC

/-- **The function `Γθ`** (Lin, Jordan, *Monotone Inclusions, Acceleration and Closed-Loop Control*, arXiv:2111.08093v4, Lemma 2.5, p.6): for `p ≥ 2`,
`Γθ(x) = (inf {α > 0 : ‖x - (I + α⁻¹A)⁻¹x‖ ≤ α^(1/(p-1)) θ^(1/(p-1))})^(1/(p-1))`.

**Formalization Note.** `J l` is the resolvent `(I + l A)⁻¹` for `l > 0`, used here at `l = α⁻¹`.
The value is real, not in `(0, +∞)` as printed: at a zero of `A` every `α > 0` qualifies, so the
infimum is `0` (the lemma's own second case). `sInf` is the real infimum: for `p ≥ 2`, `θ > 0` and
maximal monotone `A` the set is nonempty (every `α > 0` at a zero of `A`, large `α` elsewhere, by
Proposition 2.3) and bounded below by `0`, so no junk value occurs. -/
noncomputable def GammaTheta {H : Type*} [NormedAddCommGroup H]
    (J : ℝ → H → H) (p : ℕ) (θ : ℝ) (x : H) : ℝ :=
  (sInf {α : ℝ | 0 < α ∧
      ‖x - J α⁻¹ x‖ ≤ α ^ (1 / ((p : ℝ) - 1)) * θ ^ (1 / ((p : ℝ) - 1))}) ^ (1 / ((p : ℝ) - 1))

end MonoInclCLC


