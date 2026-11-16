-- Prove2me | Definitions.Def_MaskingHardness_Supplement_dualityGap
-- name    : MaskingHardness_Supplement_dualityGap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:31:27.773251+00:00
-- url     : https://prove2.me/theorems/cc657390-9748-4e66-bd60-78317956ad71
-- title:
--   Duality gap vector $\mathrm{Gap}(z)\in\overline{\mathbb R}^k$ (Definition 6.3)
-- statement:
--   Given a loss $g$, a fidelity function $h$, a lowest-loss response $\hat c_g$ and a highest-fidelity response $\widehat W_h$, the **duality gap** at $z$ is the vector $\mathrm{Gap}(z)\in\overline{\mathbb R}^k$ with
--
--   $$
--   \mathrm{Gap}(z)_i=g\big(e_i,\hat c_g(z)\big)-h\big(e_i,\widehat W_h(z)e_i\big).
--   $$
--
--   **Formalization Note** $g$ is real-valued and $h$ is `EReal`-valued, so $\mathrm{Gap}(z)_i=+\infty$ exactly when $h(e_i,\widehat W_h(z)e_i)=-\infty$. No boundedness is assumed (the paper's "for applications, we will typically assume that Gap(z) is bounded" is not part of the definition).
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Definition 6.3, p.30 (PDF p.32)

import Mathlib

namespace MaskingHardness.Supplement

/-- **The duality gap vector** (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Definition 6.3, printed p.30 = PDF p.32):
`Gap(z) ∈ ℝ̄ᵏ`, `Gap(z)_i = g(e_i, ĉ_g(z)) − h(e_i, Ŵ_h(z) e_i)`.

**Formalization Note** ℝ̄ is `EReal`; `g` is real-valued and `h` is `ℝ̄`-valued, so `Gap(z)_i` is
`+∞` exactly when `h(e_i, Ŵ_h(z)e_i) = −∞`. `Ŵ_h(z) e_i` is column `i`, `fun j => What z j i`.
No boundedness of `Gap` is assumed. -/
noncomputable def dualityGap {k : ℕ} (g : Fin k → (Fin k → ℝ) → ℝ)
    (h : Fin k → (Fin k → ℝ) → EReal) (chat : (Fin k → ℝ) → (Fin k → ℝ))
    (What : (Fin k → ℝ) → Matrix (Fin k) (Fin k) ℝ) (z : Fin k → ℝ) : Fin k → EReal :=
  fun i => ((g i (chat z) : ℝ) : EReal) - h i (fun j => What z j i)

end MaskingHardness.Supplement


