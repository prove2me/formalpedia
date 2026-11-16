-- Prove2me | Definitions.Def_MetricMatchingDistortion_Supplement_IsAlphaStar
-- name    : MetricMatchingDistortion_Supplement_IsAlphaStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:02:51.594736+00:00
-- url     : https://prove2.me/theorems/e2e6bcec-9139-4314-b608-1fc355043e30
-- title:
--   The critical exponent $\alpha_\star\approx0.95084$: root in $(0,1)$ of equation (12)
-- statement:
--   A real number $\alpha$ **solves (12)** if $0<\alpha<1$ and
--   $$\Big(1-\big(\tfrac29\big)^{1/\alpha}\Big)^{-\alpha}+\alpha\Big(1-\big(\tfrac29\big)^{1/\alpha}\Big)=2.$$
--   Definition 4.6 calls the unique such $\alpha$ the critical exponent $\alpha_\star$; Appendix B shows uniqueness and $0.95<\alpha_\star<0.951$.
--
--   It is the exponent of the distortion bound $2n^{\alpha_\star}-1$ of Coordinated Merging (Theorem 5).
--
--   **Formalization Note** All powers are real powers of numbers in $(0,1)$.
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), Definition 4.6, equation (12), p.27 (PDF p.29); Appendix B, p.84 (PDF p.86)

import Mathlib

namespace MetricMatchingDistortion.Supplement

/-- **The critical exponent `α⋆` (Definition 4.6, equation (12)).** Charikar et al., *Sublinear
Metric Distortion for Matching*, arXiv:2611.05777 (held version, sha256 fdf3452b…), Definition 4.6,
p.27 (PDF p.29): "Let α⋆ be the unique solution in (0, 1) of
(1 − (2/9)^{1/α⋆})^{−α⋆} + α⋆ (1 − (2/9)^{1/α⋆}) = 2." (12)

`IsAlphaStar α` says that `α ∈ (0, 1)` solves (12). Appendix B (p.84, PDF p.86) shows the solution
is unique, with `0.95 < α⋆ < 0.951`.

**Formalization Note.** Powers are real powers (`Real.rpow`) of the positive base `2/9` and of
`1 − (2/9)^{1/α} ∈ (0, 1)`, so no junk value arises for `α ∈ (0, 1)`. -/
def IsAlphaStar (α : ℝ) : Prop :=
  0 < α ∧ α < 1 ∧
    (1 - (2 / 9 : ℝ) ^ (1 / α)) ^ (-α) + α * (1 - (2 / 9 : ℝ) ^ (1 / α)) = 2

end MetricMatchingDistortion.Supplement


