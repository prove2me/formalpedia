-- Prove2me | Definitions.Def_CK_CKLaneC3_TAxis
-- name    : CK_CKLaneC3_TAxis
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T02:44:38.040904+00:00
-- url     : https://prove2.me/theorems/16e6aedf-fb1d-4ef0-b29b-a16dc859956e
-- title:
--   Courtade–Kumar proof module `CKLaneC3.TAxis` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC3.TAxis` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC3.TAxis` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC3.TAxis (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC3/TAxis.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisFullBridge_All
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0038Root__19
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0057Root__18

-- ===== source module CKLaneC3.TAxis =====
section

/-!
# Lane C3 — the E8 t-axis owner field

`E8TAxisFullBridge.e8_taxis_derivative_bound` (compiled, provider root) proves
`E8TAxisDerivativeBound` from the historical 773-leaf tree
(`qValid tree qDomain` and `qLeaves tree qDomain ⊆ cells`, both `decide +kernel`),
the 766 already-compiled leaf certificates, and seven explicit premises: the seven
zero-t cells with `s ∈ [2.898…, 63/20]`, `t ∈ [0, 0.00125]` (geometry indices
661, 677, 693, 709, 725, 741, 757).

The seven premises are discharged by the compiled repaired roots
`E8TAxisZero0057Root … E8TAxisZero0051Root` (index map 661 ← 0057, 677 ← 0056,
693 ← 0055, 709 ← 0054, 725 ← 0053, 741 ← 0052, 757 ← 0051).

The final declaration has the exact type of the `tAxis` field of
`GeneralCK.E8CertificateOwners`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneC3.TAxis

open GeneralCK GeneralCK.Certificates
open E8TAxisPartitionKernel E8TAxisGeneratedGeometry

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-- The numerical t-axis input `E8TAxisDerivativeBound`, unconditionally. -/
theorem e8TAxisDerivativeBound : E8TAxisDerivativeBound := by
  apply E8TAxisFullBridge.e8_taxis_derivative_bound
  · simpa only [RatRect.real, E8TAxisZero0057Root.rectangle,
      E8TAxisZero0057Root.rationalRectangle, zero_div] using E8TAxisZero0057Root.cellPositive
  · simpa only [RatRect.real, E8TAxisZero0056Root.rectangle,
      E8TAxisZero0056Root.rationalRectangle, zero_div] using E8TAxisZero0056Root.cellPositive
  · simpa only [RatRect.real, E8TAxisZero0055Root.rectangle,
      E8TAxisZero0055Root.rationalRectangle, zero_div] using E8TAxisZero0055Root.cellPositive
  · simpa only [RatRect.real, E8TAxisZero0054Root.rectangle,
      E8TAxisZero0054Root.rationalRectangle, zero_div] using E8TAxisZero0054Root.cellPositive
  · simpa only [RatRect.real, E8TAxisZero0053Root.rectangle,
      E8TAxisZero0053Root.rationalRectangle, zero_div] using E8TAxisZero0053Root.cellPositive
  · simpa only [RatRect.real, E8TAxisZero0052Root.rectangle,
      E8TAxisZero0052Root.rationalRectangle, zero_div] using E8TAxisZero0052Root.cellPositive
  · simpa only [RatRect.real, E8TAxisZero0051Root.rectangle,
      E8TAxisZero0051Root.rationalRectangle, zero_div] using E8TAxisZero0051Root.cellPositive

/-- The `tAxis` field of `GeneralCK.E8CertificateOwners`, with its exact type. -/
theorem tAxis :
    E8PositiveOn fun s t => (3 / 50 : ℝ) ≤ s ∧ s ≤ 63 / 20 ∧ t ≤ 1 / 50 :=
  e8_tAxis_of_derivative_bound e8TAxisDerivativeBound

end CKLaneC3.TAxis

end


