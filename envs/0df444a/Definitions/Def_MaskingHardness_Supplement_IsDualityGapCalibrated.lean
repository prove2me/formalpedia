-- Prove2me | Definitions.Def_MaskingHardness_Supplement_IsDualityGapCalibrated
-- name    : MaskingHardness_Supplement_IsDualityGapCalibrated
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:31:58.229694+00:00
-- url     : https://prove2.me/theorems/de2d371e-06ea-4bea-8340-b8895d494fbd
-- title:
--   $\varepsilon$-duality gap calibration (Definition 6.3)
-- statement:
--   A model $p:\mathcal X\to\Delta_k$ is **$\varepsilon$-duality gap calibrated** (for given $g,h,\hat c_g,\widehat W_h$) if
--
--   $$
--   \mathbb E\big[\langle \mathrm{Gap}(p(x)),\ y-p(x)\rangle\big]\le\varepsilon .
--   $$
--
--   It asks that the true labels do not see the duality gap differently from labels simulated from $p(x)$.
--
--   **Formalization Note** The expectation and inner product are computed in `EReal`: $\sum_{x,y}\mathcal D(x,y)\sum_i \mathrm{Gap}(p(x))_i\,([i=y]-p(x)_i)$, with $0\cdot(\pm\infty)=0$ and $(+\infty)+(-\infty)=-\infty$.
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Definition 6.3, p.30 (PDF p.32)

import Mathlib
import Definitions.Def_MaskingHardness_Supplement_dualityGap

namespace MaskingHardness.Supplement

/-- **Duality gap calibration** (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Definition 6.3, printed p.30 = PDF p.32): a model
`p : X → Δ_k` is `ε`-duality gap calibrated if `E[⟨Gap(p(x)), y − p(x)⟩] ≤ ε`.

**Formalization Note** The expectation and the inner product are computed in `EReal`:
`∑ₓ ∑_y D(x, y) · ∑_i Gap(p(x))_i · ((e_y)_i − p(x)_i)`, with `(e_y)_i = [i = y]`. In `EReal`,
`0 · (±∞) = 0` and `(+∞) + (−∞) = −∞`. -/
def IsDualityGapCalibrated {X : Type*} [Fintype X] {k : ℕ} (D : X → Fin k → ℝ)
    (g : Fin k → (Fin k → ℝ) → ℝ) (h : Fin k → (Fin k → ℝ) → EReal)
    (chat : (Fin k → ℝ) → (Fin k → ℝ)) (What : (Fin k → ℝ) → Matrix (Fin k) (Fin k) ℝ)
    (ε : ℝ) (p : X → Fin k → ℝ) : Prop :=
  (∑ x, ∑ y, ((D x y : ℝ) : EReal) *
      ∑ i, dualityGap g h chat What (p x) i *
        ((((if i = y then (1 : ℝ) else 0) - p x i : ℝ)) : EReal)) ≤ (ε : EReal)

end MaskingHardness.Supplement


