-- Prove2me | solution 1 for AutomorphicForm.isFactorizableTestFn_conj_comp_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/a81a06c5-db8b-5fc0-99ff-896c26bccb60

import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_isFactorizableTestFn_flat
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isFactorizableTestFn_conj_comp_inv
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm

theorem solution
    (K : Type) [Field K] [NumberField K]
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : IsFactorizableTestFn K f) :
    IsFactorizableTestFn K (fun y : AdelicGL2 (𝓞 K) K => conj (f y⁻¹)) := by
  have h := AutomorphicForm.CuspidalSpectrum.isFactorizableTestFn_flat K 0 f _hf
  have heq : AutomorphicForm.CuspidalSpectrum.flat K 0 f = fun y : AdelicGL2 (𝓞 K) K => conj (f y⁻¹) := by
    funext y
    simp only [AutomorphicForm.CuspidalSpectrum.flat, neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one]
  rw [heq] at h
  exact h

end S_AutomorphicForm_isFactorizableTestFn_conj_comp_inv
end P2MW
export P2MW.S_AutomorphicForm_isFactorizableTestFn_conj_comp_inv (solution)
