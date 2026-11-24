-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_StdChar
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_StdChar
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T14:18:05.757794+00:00
-- url     : https://prove2.me/theorems/2007fb2c-0e7d-49e1-b48f-026b0d8f796f
-- title:
--   Std Char
-- statement:
--   Definitions and structural lemmas for Std Char, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/StdChar.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_MeasCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_FundamentalContinuity_AdelicIsomorphismStatement
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Topology Filter
namespace Formalism.L2.SG.Pf.StdChar
variable (F : Type) [Field F] [NumberField F]
def psiA (x : Ainf F) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I *
    ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))
theorem psiA_add (x y : Ainf F) : psiA F (x + y) = psiA F x * psiA F y := by
  have h : ∀ w : InfinitePlace F, (x + y) w = x w + y w := fun w => rfl
  simp only [psiA, h, map_add, Complex.add_re, Finset.sum_add_distrib]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring
theorem psiA_zero : psiA F 0 = 1 := by
  have h : ∀ w : InfinitePlace F, (0 : Ainf F) w = 0 := fun w => rfl
  simp [psiA, h]
def trR : F →+ ℝ :=
  AddMonoidHom.mk' (fun a => ∑ w : InfinitePlace F, (w.embedding a).re) (by
    intro a b
    simp only [map_add, Complex.add_re, Finset.sum_add_distrib])
theorem trR_int [IsTotallyReal F] (d : 𝓞 F) : ∃ n : ℤ, trR F (algebraMap (𝓞 F) F d) = n := by
  have hsurj : Function.Surjective (InfinitePlace.mk : (F →+* ℂ) → InfinitePlace F) :=
    fun w => ⟨w.embedding, InfinitePlace.mk_embedding w⟩
  have hreal : ∀ φ : F →+* ℂ, ComplexEmbedding.IsReal φ := fun φ =>
    InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal _)
  have hinj : Function.Injective (InfinitePlace.mk : (F →+* ℂ) → InfinitePlace F) := by
    intro φ ψ h
    rcases InfinitePlace.mk_eq_iff.mp h with h' | h'
    · exact h'
    · exact (ComplexEmbedding.isReal_iff.mp (hreal φ)).symm.trans h'
  have hsum : ∀ a : F, trR F a = ∑ φ : F →+* ℂ, (φ a).re := by
    intro a
    show (∑ w : InfinitePlace F, (w.embedding a).re) = _
    symm
    refine Fintype.sum_bijective _ ⟨hinj, hsurj⟩ _ _ (fun φ => ?_)
    rw [InfinitePlace.embedding_mk_eq_of_isReal (hreal φ)]
  have htr : ∀ a : F, trR F a = ((Algebra.trace ℚ F a : ℚ) : ℝ) := by
    intro a
    rw [hsum, ← Complex.re_sum]
    have h' : (∑ φ : F →+* ℂ, φ a) = ∑ σ : F →ₐ[ℚ] ℂ, σ a :=
      Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) _ _ (fun φ => rfl)
    rw [h']
    first
      | rw [← trace_eq_sum_embeddings (E := ℂ) (x := a)]
      | rw [← Algebra.trace_eq_sum_embeddings (E := ℂ) (x := a)]
    first
      | rw [eq_ratCast (algebraMap ℚ ℂ), Complex.ratCast_re]
      | simp
  have hint : IsIntegral ℤ (Algebra.trace ℚ F (algebraMap (𝓞 F) F d)) := by
    apply Algebra.isIntegral_trace
    first
      | exact RingOfIntegers.isIntegral_coe d
      | exact d.2
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨n, ?_⟩
  rw [htr, ← hn]
  simp
theorem exists_psiF [IsTotallyReal F] : ∃ f : Af F →+ AddCircle (1 : ℝ),
    (∀ z ∈ Formalism.UG.intAd F, f z = 0) ∧ ∀ a : F, f (algebraMap F (Af F) a) = ((trR F a : ℝ) : AddCircle (1 : ℝ)) := by
  let U : AddSubgroup (Af F) := (Formalism.UG.intAd F).toAddSubgroup
  let j : F →+ Af F ⧸ U := (QuotientAddGroup.mk' U).comp (algebraMap F (Af F)).toAddMonoidHom
  let h : F →+ AddCircle (1 : ℝ) := (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp (trR F)
  have hker : j.ker ≤ h.ker := by
    intro a ha
    rw [AddMonoidHom.mem_ker] at ha ⊢
    have hmem : algebraMap F (Af F) a ∈ Formalism.UG.intAd F :=
      (QuotientAddGroup.eq_zero_iff (algebraMap F (Af F) a)).mp ha
    have hmem' : ∀ v : HeightOneSpectrum (𝓞 F),
        (algebraMap F (Af F) a) v ∈ v.adicCompletionIntegers F := hmem
    have hval : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F a ≤ 1 := by
      intro v
      have h1 : (a : v.adicCompletion F) ∈ v.adicCompletionIntegers F := hmem' v
      rw [HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
      exact h1
    obtain ⟨d, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (K := F) (x := a) hval
    obtain ⟨n, hn⟩ := trR_int F d
    show ((trR F (algebraMap (𝓞 F) F d) : ℝ) : AddCircle (1 : ℝ)) = 0
    rw [hn]
    first
      | exact (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.intCast_mem_zmultiples_one n)
      | (rw [AddCircle.coe_eq_zero_iff]; exact ⟨n, by simp⟩)
  have hj : Function.Injective (QuotientAddGroup.kerLift j) := QuotientAddGroup.kerLift_injective j
  have hB : Module.Baer ℤ (AddCircle (1 : ℝ)) := by
    first
      | exact Module.Baer.of_divisible _
      | exact @Module.Baer.of_divisible _ _ (QuotientAddGroup.divisibleBy _)
  obtain ⟨g, hg⟩ := hB.extension_property (QuotientAddGroup.kerLift j).toIntLinearMap hj
    (QuotientAddGroup.lift j.ker h hker).toIntLinearMap
  refine ⟨g.toAddMonoidHom.comp (QuotientAddGroup.mk' U), ?_, ?_⟩
  · intro z hz
    have hz0 : (QuotientAddGroup.mk' U) z = 0 := (QuotientAddGroup.eq_zero_iff z).mpr hz
    show g.toAddMonoidHom ((QuotientAddGroup.mk' U) z) = 0
    rw [hz0, map_zero]
  · intro a
    exact LinearMap.congr_fun hg (QuotientAddGroup.mk a)
end Formalism.L2.SG.Pf.StdChar
namespace Formalism.L2.SG.Pf.StdChar
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
def psiFin (z : Af F) : ℂ := ((AddCircle.toCircle (-((exists_psiF F).choose z)) : Circle) : ℂ)
theorem psiFin_add (z w : Af F) : psiFin F (z + w) = psiFin F z * psiFin F w := by
  unfold psiFin
  rw [map_add, neg_add, AddCircle.toCircle_add]
  first | rfl | simp
theorem psiFin_int (z : Af F) (hz : z ∈ Formalism.UG.intAd F) : psiFin F z = 1 := by
  have h0 := (exists_psiF F).choose_spec.1 z hz
  first
    | simp [psiFin, h0, AddCircle.toCircle_zero]
    | simp [psiFin, h0]
theorem psiFin_zero : psiFin F 0 = 1 := psiFin_int F 0 (Formalism.UG.intAd F).zero_mem
def psiStd : AddChar (AF F) ℂ where
  toFun x := psiA F x.1 * psiFin F x.2
  map_zero_eq_one' := by
    show psiA F 0 * psiFin F 0 = 1
    rw [psiA_zero, psiFin_zero, one_mul]
  map_add_eq_mul' x y := by
    show psiA F (x.1 + y.1) * psiFin F (x.2 + y.2) = psiA F x.1 * psiFin F x.2 * (psiA F y.1 * psiFin F y.2)
    rw [psiA_add, psiFin_add]
    ring
end Formalism.L2.SG.Pf.StdChar
namespace Formalism.L2.SG.Pf
end Formalism.L2.SG.Pf


