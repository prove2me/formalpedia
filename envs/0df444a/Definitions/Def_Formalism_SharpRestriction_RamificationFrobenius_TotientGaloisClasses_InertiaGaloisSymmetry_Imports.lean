-- Prove2me | Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_Imports
-- name    : Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_Imports
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T05:11:18.097121+00:00
-- url     : https://prove2.me/theorems/f0612729-e968-4dd0-81b5-3f265efb9f02
-- title:
--   Imports
-- statement:
--   Definitions and structural lemmas for Imports, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/Imports.lean

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcEqOfPowEqOne
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_splitK
import Theorems.Thm_Formalism_HC_Der_diffSupport
import Theorems.Thm_Formalism_HC_Der_discr_sq
import Theorems.Thm_Formalism_HC_Der_eta
import Theorems.Thm_Formalism_HC_Der_norm_mu
import Theorems.Thm_Formalism_HC_Der_ordinary
import Theorems.Thm_Formalism_HC_Der_principal
import Theorems.Thm_Formalism_HC_Der_splitK
import Theorems.Thm_Formalism_HC_Der_unimodular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
namespace Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
example (D : HostDer H) : type_of% D.splitK := splitK H
example (C : HostCore H) (D : HostDer H) : type_of% D.ordinary := ordinary H C
example (C : HostCore H) (D : HostDer H) : type_of% D.eta := eta H C
example (C : HostCore H) (D : HostDer H) : type_of% D.diffSupport := diffSupport H C
example (C : HostCore H) (D : HostDer H) : type_of% D.principal := principal H C
example (D : HostDer H) : type_of% D.unimodular := unimodular H
example (C : HostCore H) (D : HostDer H) : type_of% D.discr_sq := discr_sq H C
example (C : HostCore H) (D : HostDer H) : type_of% D.norm_mu := norm_mu H C
end Formalism.HC.Der
end


