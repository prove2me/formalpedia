-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Degree
-- name    : GroundTheory_GlobalFields_CompletionAtPlace_Degree
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:38:31.482796+00:00
-- url     : https://prove2.me/theorems/40385a9a-9347-4b8e-9831-02af8d644113
-- title:
--   Degree
-- statement:
--   Definitions and structural lemmas for Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Degree.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Theorems.Thm_GroundTheory_Global_mem_maximalIdeal_iff_valued_lt_one
import Theorems.Thm_GroundTheory_Global_mem_valuationInteger_iff
import Theorems.Thm_GroundTheory_Global_ramificationIdx_integer
import Theorems.Thm_GroundTheory_Global_ramificationIdx_mul_inertiaDeg_integer
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk


set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
open scoped WithZero
namespace GroundTheory.Global
section Residue
variable {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))
def ringOfIntegersToInteger : 𝓞 F →+* 𝒪[u.adicCompletion F] :=
  ((algebraMap F (u.adicCompletion F)).comp (algebraMap (𝓞 F) F)).codRestrict
    𝒪[u.adicCompletion F] fun r ↦ (mem_valuationInteger_iff u _).2 (coe_algebraMap_mem (𝓞 F) F u r)
@[simp]
theorem coe_ringOfIntegersToInteger (r : 𝓞 F) :
    (ringOfIntegersToInteger u r : u.adicCompletion F) =
      algebraMap F (u.adicCompletion F) (algebraMap (𝓞 F) F r) :=
  rfl
def toResidueInteger : 𝓞 F →+* 𝒪[u.adicCompletion F] ⧸ 𝓂[u.adicCompletion F] :=
  (Ideal.Quotient.mk _).comp (ringOfIntegersToInteger u)
theorem ker_toResidueInteger : RingHom.ker (toResidueInteger u) = u.asIdeal := by
  ext r
  rw [RingHom.mem_ker, toResidueInteger, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
    mem_maximalIdeal_iff_valued_lt_one, coe_ringOfIntegersToInteger]
  erw [valuedAdicCompletion_eq_valuation' u]
  exact valuation_lt_one_iff_mem u r
theorem toResidueInteger_surjective : Function.Surjective (toResidueInteger u) := by
  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hy : (y : u.adicCompletion F) ∈ u.adicCompletionIntegers F :=
    (mem_valuationInteger_iff u _).1 y.2
  have hn : {z : u.adicCompletion F | Valued.v.restrict (z - y) <
      ((1 : (MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v :
        Valuation (u.adicCompletion F) ℤᵐ⁰)))ˣ) : _)} ∈ nhds (y : u.adicCompletion F) :=
    Valued.mem_nhds.2 ⟨1, subset_rfl⟩
  obtain ⟨_, hz, r, rfl⟩ := mem_closure_iff_nhds.1
    (adicCompletionIntegers_subset_closure_ringOfIntegers u hy) _ hn
  refine ⟨r, (Ideal.Quotient.eq.2 ?_)⟩
  rw [mem_maximalIdeal_iff_valued_lt_one]
  change Valued.v ((ringOfIntegersToInteger u r : u.adicCompletion F) - (y : u.adicCompletion F)) < 1
  rw [coe_ringOfIntegersToInteger]
  simpa [Valuation.restrict_lt_one_iff] using hz
def residueEquivInteger : (𝓞 F ⧸ u.asIdeal) ≃+* (𝒪[u.adicCompletion F] ⧸ 𝓂[u.adicCompletion F]) :=
  (Ideal.quotEquivOfEq (ker_toResidueInteger u).symm).trans
    (RingHom.quotientKerEquivOfSurjective (toResidueInteger_surjective u))
@[simp]
theorem residueEquivInteger_mk (r : 𝓞 F) :
    residueEquivInteger u (Ideal.Quotient.mk u.asIdeal r) =
      Ideal.Quotient.mk _ (ringOfIntegersToInteger u r) :=
  rfl
end Residue
section Degree
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]
theorem algebraMap_ringOfIntegersToInteger (r : 𝓞 K) :
    algebraMap 𝒪[v.adicCompletion K] 𝒪[w.adicCompletion L] (ringOfIntegersToInteger v r) =
      ringOfIntegersToInteger w (algebraMap (𝓞 K) (𝓞 L) r) := by
  apply Subtype.ext
  rw [GroundTheory.LocalField.coe_algebraMap_integer, coe_ringOfIntegersToInteger,
    coe_ringOfIntegersToInteger, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply K L (w.adicCompletion L)]
  rfl
theorem inertiaDeg_integer :
    𝓂[w.adicCompletion L].inertiaDeg 𝒪[v.adicCompletion K] = w.asIdeal.inertiaDeg (𝓞 K) := by
  have := w.isMaximal
  have := v.isMaximal
  rw [Ideal.inertiaDeg_eq_of_isMaximal 𝓂[v.adicCompletion K] 𝓂[w.adicCompletion L],
    Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal w.asIdeal]
  refine (Algebra.finrank_eq_of_equiv_equiv (residueEquivInteger v) (residueEquivInteger w)
    ?_).symm
  apply Ideal.Quotient.ringHom_ext
  ext r
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    residueEquivInteger_mk]
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver, Ideal.Quotient.algebraMap_mk_of_liesOver,
    residueEquivInteger_mk, algebraMap_ringOfIntegersToInteger]
theorem finrank_adicCompletion :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) =
      w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) := by
  rw [← ramificationIdx_mul_inertiaDeg_integer v w, ramificationIdx_integer v w,
    inertiaDeg_integer v w]
end Degree
section Check
open AdicLiesOver
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
example : Module.finrank (v.adicCompletion K) (w.adicCompletion L) =
    w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) :=
  finrank_adicCompletion v w
end Check
end GroundTheory.Global


