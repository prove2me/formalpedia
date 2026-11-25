-- Prove2me | Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfRawToHostRaw
-- name    : Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfRawToHostRaw
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T06:01:38.443707+00:00
-- url     : https://prove2.me/theorems/363e0371-9b6a-476d-9dbc-2e04f7aeb486
-- title:
--   Of Raw To Host Raw
-- statement:
--   Definitions and structural lemmas for Of Raw To Host Raw, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/OfRawToHostRaw.lean

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycAll
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_Imports
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_cmType
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_frob
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_splitK
import Theorems.Thm_Formalism_HC_D7_inertia_d
import Theorems.Thm_Formalism_HC_Der_art_ch
import Theorems.Thm_Formalism_HC_Der_art_surj
import Theorems.Thm_Formalism_HC_Der_cm
import Theorems.Thm_Formalism_HC_Der_cmType
import Theorems.Thm_Formalism_HC_Der_conj_iff
import Theorems.Thm_Formalism_HC_Der_decomp
import Theorems.Thm_Formalism_HC_Der_decompConj
import Theorems.Thm_Formalism_HC_Der_decomp_typeI
import Theorems.Thm_Formalism_HC_Der_diffSupport
import Theorems.Thm_Formalism_HC_Der_discr_primes
import Theorems.Thm_Formalism_HC_Der_discr_sq
import Theorems.Thm_Formalism_HC_Der_eta
import Theorems.Thm_Formalism_HC_Der_finrank_E
import Theorems.Thm_Formalism_HC_Der_finrank_F
import Theorems.Thm_Formalism_HC_Der_frob
import Theorems.Thm_Formalism_HC_Der_frob_any
import Theorems.Thm_Formalism_HC_Der_hostCore
import Theorems.Thm_Formalism_HC_Der_inertia
import Theorems.Thm_Formalism_HC_Der_inertia_d
import Theorems.Thm_Formalism_HC_Der_mem_F
import Theorems.Thm_Formalism_HC_Der_norm_mu
import Theorems.Thm_Formalism_HC_Der_ordinary
import Theorems.Thm_Formalism_HC_Der_principal
import Theorems.Thm_Formalism_HC_Der_ps_d
import Theorems.Thm_Formalism_HC_Der_ps_root
import Theorems.Thm_Formalism_HC_Der_rd_ge
import Theorems.Thm_Formalism_HC_Der_rd_le
import Theorems.Thm_Formalism_HC_Der_rd_sq_ge
import Theorems.Thm_Formalism_HC_Der_splitK
import Theorems.Thm_Formalism_HC_Der_unimodular
import Theorems.Thm_Formalism_HC_Der_unramEF
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_UnitConjugation_conj_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.HC
theorem HostRaw.der {φ : Frame} (H : HostRaw φ) : HostDer H :=
  have C := Der.hostCore H
  { art_surj := C.art_surj
    cm := C.cm
    conj_iff := C.conj_iff
    finrank_E := C.finrank_E
    finrank_F := C.finrank_F
    mem_F := C.mem_F
    cmType := Der.cmType H
    ps_root := Der.ps_root H
    art_ch := C.art_ch
    ps_d := C.ps_d
    frob := C.frob
    frob_any := C.frob_any
    inertia := C.inertia
    decomp := C.decomp
    inertia_d := C.inertia_d
    decomp_typeI := C.decomp_typeI
    decompConj := C.decompConj
    unramEF := C.unramEF
    splitK := Der.splitK H
    ordinary := Der.ordinary H C
    eta := Der.eta H C
    diffSupport := Der.diffSupport H C
    principal := Der.principal H C
    unimodular := Der.unimodular H
    discr_sq := Der.discr_sq H C
    discr_primes := Der.discr_primes H C
    rd_ge := Der.rd_ge H C
    rd_le := Der.rd_le H
    rd_sq_ge := Der.rd_sq_ge H C
    norm_mu := Der.norm_mu H C }
def HostAx.ofRaw {φ : Frame} (H : HostRaw φ) : HostAx φ := ⟨H, H.der⟩
end Formalism.HC
end


