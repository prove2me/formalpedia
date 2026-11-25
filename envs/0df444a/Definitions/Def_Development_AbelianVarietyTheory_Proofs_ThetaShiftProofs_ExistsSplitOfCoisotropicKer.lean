-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSplitOfCoisotropicKer
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSplitOfCoisotropicKer
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:01:08.284662+00:00
-- url     : https://prove2.me/theorems/d99c6e8d-e3aa-4933-a007-f319ff2e741c
-- title:
--   Exists Split Of Coisotropic Ker
-- statement:
--   Definitions and structural lemmas for Exists Split Of Coisotropic Ker, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSplitOfCoisotropicKer.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SmulPeriodMapMkZeroFstEqNegForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory
namespace KerPerp
variable {O L Y : Type} [CommRing O] [StarRing O] [AddCommGroup L] [Module O L] [AddCommGroup Y] [Module O Y]
  {EF : LinearMap.BilinForm ℤ L} {y : L →ₗ[O] Y}
end KerPerp
end GlobalTheory


