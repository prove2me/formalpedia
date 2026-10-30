-- Prove2me | Definitions.Def_DerivativeChainPrivate_SixthSepticInverse
-- name    : DerivativeChainPrivate_SixthSepticInverse
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-27T00:31:48.631284+00:00
-- url     : https://prove2.me/theorems/1994ab48-7190-4ac8-9f9a-afda33130fbb
-- title:
--   The selected seventh-row inverse correction
-- statement:
--   Define $L_7=17/192-18037\sqrt{15145}/52117440$ and $E_7(z)=L_7/z+E^{\rm odd}_7(z^{-1})$. The selected inverse later has the form $\beta/z=\alpha_7z^2-b_7+E_7(z)/z$, where $\alpha_7=(455-3\sqrt{15145})/2720$ and $b_7=13/32-77\sqrt{15145}/37280$.
-- source:
--   Local frozen formal commit 824c42957a59765fe3d9f7d6d32554cff9dbeba8 (not asserted pushed), submission_sync/new_formal/sixth_power/join67/SixthSepticInverse.lean, lines 8-8, SHA-256 2c3f171bfd66de793ef115f9a4443a15f5dcaadf4951d4c3b3c1102da5203f95.; Local frozen formal commit 824c42957a59765fe3d9f7d6d32554cff9dbeba8 (not asserted pushed), submission_sync/new_formal/sixth_power/join67/SixthSepticInverse.lean, lines 9-10, SHA-256 2c3f171bfd66de793ef115f9a4443a15f5dcaadf4951d4c3b3c1102da5203f95.

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthSepticAlgebra
import Definitions.Def_DerivativeChainPrivate_SixthSepticErrorDerivative
import Definitions.Def_DerivativeChainPrivate_SixthSepticTail
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators

noncomputable def sixthSepticLeadingError : ℝ := 17/192-18037*Real.sqrt 15145/52117440
noncomputable def sixthSepticRemainder (z : ℂ) : ℂ :=
  (sixthSepticLeadingError:ℂ)*z⁻¹+sixthSepticError z⁻¹










end DerivativeChainPrivate


