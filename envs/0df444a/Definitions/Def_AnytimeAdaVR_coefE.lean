-- Prove2me | Definitions.Def_AnytimeAdaVR_coefE
-- name    : AnytimeAdaVR_coefE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:27:02.361911+00:00
-- url     : https://prove2.me/theorems/7494d1ae-42a6-4c18-85e1-f03dd450999f
-- title:
--   Constant $E_\Lambda=4\sqrt{\sigma^2+\Lambda^2}$
-- statement:
--   $$
--   E_\Lambda=4\sqrt{\sigma^2+\Lambda^2},
--   $$
--   with $\Lambda=L$ for the S path and $\Lambda=\bar L$ for the M path. It bounds the block estimation error (Lemma B.1).
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), App. B, p.16; eq. (63), p.30

import Mathlib

namespace AnytimeAdaVR

/-- **The constant `E_Λ = 4√(σ² + Λ²)`.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), App. B, p.16 ("set E = 4√(σ² + Λ²), where Λ = L for
S and Λ = L̄ for M") and App. G.1, p.30, eq. (63). -/
noncomputable def coefE (σ Λ : ℝ) : ℝ :=
  4 * Real.sqrt (σ ^ 2 + Λ ^ 2)

end AnytimeAdaVR


