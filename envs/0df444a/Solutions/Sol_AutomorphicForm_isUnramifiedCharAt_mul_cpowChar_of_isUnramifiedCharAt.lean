-- Prove2me | solution 1 for AutomorphicForm.isUnramifiedCharAt_mul_cpowChar_of_isUnramifiedCharAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/27e24ec4-8fc6-5469-b091-4ea6880bd8b8

import Mathlib
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
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isUnramifiedCharAt_mul_cpowChar_of_isUnramifiedCharAt
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

noncomputable section

namespace UnramTwist

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.TateGlobal
open IsDedekindDomain AutomorphicForm
open scoped NNReal

variable {K : Type} [Field K] [NumberField K]

def idl (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t)

theorem idl_fst (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    ((idl K v t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := rfl

theorem idl_snd_self (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    ((idl K v t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = t := by
  show ((localUnit (𝓞 K) K v t : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v = t
  exact localUnit_apply_self (𝓞 K) K v t

theorem idl_snd_of_ne (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) {w : HeightOneSpectrum (𝓞 K)}
    (hw : w ≠ v) : ((idl K v t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w = 1 := by
  show ((localUnit (𝓞 K) K v t : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w = 1
  exact localUnit_apply_of_ne (𝓞 K) K v t hw

theorem localChar_eq_idl (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (t : (v.adicCompletion K)ˣ) : TateGlobal.localChar χ v t = χ (idl K v t) := rfl

theorem distribHaarChar_idl_of_valued_eq_one (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ)
    (ht : Valued.v (t : v.adicCompletion K) = 1) :
    ((distribHaarChar (AdeleRing (𝓞 K) K) (idl K v t) : ℝ≥0) : ℝ) = 1 := by
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm K (idl K v t)]
  have h1 : ∏ w : InfinitePlace K,
      ‖((idl K v t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w‖ ^ w.mult = 1 := by
    refine Finset.prod_eq_one fun w _ => ?_
    rw [idl_fst, show (1 : InfiniteAdeleRing K) w = 1 from rfl, norm_one, one_pow]
  have h2 : ∏ᶠ u : HeightOneSpectrum (𝓞 K),
      ‖((idl K v t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 u‖ = ‖(t : v.adicCompletion K)‖ := by
    rw [finprod_eq_single _ v fun u hu => by rw [idl_snd_of_ne v t hu, norm_one], idl_snd_self]
  rw [h1, one_mul, h2, NumberField.FinitePlace.norm_def, ht, map_one, NNReal.coe_one]

theorem valued_eq_one_of_mem_of_inv_mem (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ)
    (ht : (t : v.adicCompletion K) ∈ v.adicCompletionIntegers K)
    (hti : ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K) :
    Valued.v (t : v.adicCompletion K) = 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ht hti
  have ht0 : Valued.v (t : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).mpr t.ne_zero
  rw [Units.val_inv_eq_inv_val, map_inv₀] at hti
  have h1 : 1 ≤ Valued.v (t : v.adicCompletion K) := by
    have := mul_le_mul_left hti (Valued.v (t : v.adicCompletion K))
    rwa [inv_mul_cancel₀ ht0, one_mul] at this
  exact le_antisymm ht h1

end UnramTwist

end

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open AutomorphicForm UnramTwist
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (K : Type) [Field K] [NumberField K] :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) (v : HeightOneSpectrum (𝓞 K)),
      NumberField.TateGlobal.IsUnramifiedCharAt χ v →
      NumberField.TateGlobal.IsUnramifiedCharAt (χ * cpowChar αm hαm s) v := by
  intro αm hαm χ s v hχ t ht hti
  have h1 : χ (idl K v t) = 1 := hχ t ht hti
  have h2 : cpowChar αm hαm s (idl K v t) = 1 := by
    apply Units.ext
    rw [cpowChar_apply_val, Units.val_one,
      show ((αm (idl K v t) : ℝˣ) : ℝ) = ((distribHaarChar (AdeleRing (𝓞 K) K) (idl K v t) : ℝ≥0) : ℝ)
        from rfl,
      distribHaarChar_idl_of_valued_eq_one v t (valued_eq_one_of_mem_of_inv_mem v t ht hti),
      Complex.ofReal_one, Complex.one_cpow]
  show (χ * cpowChar αm hαm s) (idl K v t) = 1
  rw [MonoidHom.mul_apply, h1, h2, mul_one]

end S_AutomorphicForm_isUnramifiedCharAt_mul_cpowChar_of_isUnramifiedCharAt
end P2MW
export P2MW.S_AutomorphicForm_isUnramifiedCharAt_mul_cpowChar_of_isUnramifiedCharAt (solution)
