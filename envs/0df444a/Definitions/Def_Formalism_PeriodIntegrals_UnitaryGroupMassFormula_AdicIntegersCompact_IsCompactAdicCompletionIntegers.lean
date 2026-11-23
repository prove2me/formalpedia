-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicIntegersCompact_IsCompactAdicCompletionIntegers
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicIntegersCompact_IsCompactAdicCompletionIntegers
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:02:32.921364+00:00
-- url     : https://prove2.me/theorems/96bc0117-537c-49e0-8610-151b0381954f
-- title:
--   Is Compact Adic Completion Integers
-- statement:
--   Definitions and structural lemmas for Is Compact Adic Completion Integers, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdicIntegersCompact/IsCompactAdicCompletionIntegers.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_IntAdelesCompactOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.IntAdCpctOpenWork
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
theorem isOpen_lt_one (x : v.adicCompletion F) :
    IsOpen {y : v.adicCompletion F | Valued.v (y - x) < 1} := by
  have h1 : IsOpen {z : v.adicCompletion F | Valued.v z < 1} := by
    have := Valued.isOpen_ball (v.adicCompletion F) 1
    simpa only [Valuation.restrict_lt_one_iff] using this
  exact h1.preimage (continuous_id.sub continuous_const)
theorem valued_algebraMap (k : F) :
    Valued.v (algebraMap F (v.adicCompletion F) k) = v.valuation F k := by
  first
  | exact valuedAdicCompletion_eq_valuation' v k
  | rfl
theorem denseRange : DenseRange (algebraMap F (v.adicCompletion F)) := by
  exact denseRange_algebraMap F v
theorem exists_close (x : v.adicCompletion F) (hx : Valued.v x ≤ 1) :
    ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < 1 := by
  obtain ⟨k, hk⟩ : ∃ k : F, algebraMap F (v.adicCompletion F) k ∈
      {y : v.adicCompletion F | Valued.v (y - x) < 1} :=
    (denseRange v).exists_mem_open (isOpen_lt_one v x) ⟨x, by simp⟩
  simp only [Set.mem_setOf_eq] at hk
  have hk1 : v.valuation F k ≤ 1 := by
    rw [← valued_algebraMap]
    have e : algebraMap F (v.adicCompletion F) k = (algebraMap F (v.adicCompletion F) k - x) + x := by ring
    rw [e]
    exact Valuation.map_add_le _ hk.le hx
  obtain ⟨r, s, hs, hrs⟩ : ∃ r s : 𝓞 F, s ∉ v.asIdeal ∧
      algebraMap (𝓞 F) F s * k = algebraMap (𝓞 F) F r := by
    have hmem : k ∈ valuationSubringAtPrime F v := by
      rw [valuationSubringAtPrime_eq_valuationSubring]
      exact (Valuation.mem_valuationSubring_iff _ _).mpr hk1
    obtain ⟨⟨r, s⟩, h⟩ := IsLocalization.surj v.asIdeal.primeCompl
      (⟨k, hmem⟩ : valuationSubringAtPrime F v)
    refine ⟨r, s, s.2, ?_⟩
    have e : ∀ y : 𝓞 F, ((algebraMap (𝓞 F) (valuationSubringAtPrime F v) y :
        valuationSubringAtPrime F v) : F) = algebraMap (𝓞 F) F y := by
      intro y
      first
      | rfl
      | simp
      | exact (IsScalarTower.algebraMap_apply (𝓞 F) (valuationSubringAtPrime F v) F y).symm
    have h' := congrArg Subtype.val h
    have h'' : k * ((algebraMap (𝓞 F) (valuationSubringAtPrime F v) s : valuationSubringAtPrime F v) : F) =
        ((algebraMap (𝓞 F) (valuationSubringAtPrime F v) r : valuationSubringAtPrime F v) : F) := by
      simpa using h'
    rw [e, e] at h''
    rw [mul_comm]
    exact h''
  obtain ⟨t, ht⟩ : ∃ t : 𝓞 F, s * t - 1 ∈ v.asIdeal := by
    haveI := v.isMaximal
    have hs0 : (Ideal.Quotient.mk v.asIdeal s) ≠ 0 := by
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv hs0
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨t, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hb, map_one, sub_self]
  refine ⟨r * t, ?_⟩
  have hkrt : v.valuation F (k - algebraMap (𝓞 F) F (r * t)) < 1 := by
    have e : k - algebraMap (𝓞 F) F (r * t) = k * (1 - algebraMap (𝓞 F) F (s * t)) := by
      rw [map_mul, map_mul, ← hrs]; ring
    rw [e, map_mul]
    have h1 : v.valuation F (1 - algebraMap (𝓞 F) F (s * t)) < 1 := by
      have e1 : (1 : F) - algebraMap (𝓞 F) F (s * t) = algebraMap (𝓞 F) F (-(s * t - 1)) := by
        rw [map_neg, map_sub, map_one]; ring
      rw [e1, valuation_lt_one_iff_mem]
      exact v.asIdeal.neg_mem_iff.mpr ht
    calc v.valuation F k * v.valuation F (1 - algebraMap (𝓞 F) F (s * t))
        ≤ 1 * v.valuation F (1 - algebraMap (𝓞 F) F (s * t)) := by
          first
          | exact mul_le_mul_of_nonneg_right hk1 zero_le'
          | gcongr
      _ < 1 := by rw [one_mul]; exact h1
  have e2 : x - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (r * t)) =
      (x - algebraMap F (v.adicCompletion F) k) +
        algebraMap F (v.adicCompletion F) (k - algebraMap (𝓞 F) F (r * t)) := by
    rw [map_sub]; ring
  rw [e2]
  apply Valuation.map_add_lt
  · rw [Valuation.map_sub_swap]; exact hk
  · rw [valued_algebraMap]; exact hkrt
theorem mem_maximalIdeal_iff (x : Valued.integer (v.adicCompletion F)) :
    x ∈ IsLocalRing.maximalIdeal (Valued.integer (v.adicCompletion F)) ↔
      Valued.v (x : v.adicCompletion F) < 1 := by
  show ¬IsUnit x ↔ _
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one
noncomputable def toInt : 𝓞 F →+* Valued.integer (v.adicCompletion F) :=
  ((algebraMap F (v.adicCompletion F)).comp (algebraMap (𝓞 F) F)).codRestrict
    (Valued.integer (v.adicCompletion F)) (fun a => by
      show Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) ≤ 1
      rw [valued_algebraMap]
      exact valuation_le_one v a)
noncomputable def resHom :
    𝓞 F →+* IsLocalRing.ResidueField (Valued.integer (v.adicCompletion F)) :=
  (IsLocalRing.residue _).comp (toInt v)
theorem resHom_surjective : Function.Surjective (resHom v) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨a, ha⟩ := exists_close v x x.2
  refine ⟨a, ?_⟩
  unfold resHom
  rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff]
  have e : ((toInt v a - x : Valued.integer (v.adicCompletion F)) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) - x := rfl
  rw [e, Valuation.map_sub_swap]
  exact ha
theorem resHom_eq_zero (a : 𝓞 F) (ha : a ∈ v.asIdeal) : resHom v a = 0 := by
  unfold resHom
  rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff]
  show Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < 1
  rw [valued_algebraMap]
  exact (valuation_lt_one_iff_mem v a).mpr ha
theorem finite_residueField : Finite (Valued.ResidueField (v.adicCompletion F)) := by
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  let g := Ideal.Quotient.lift v.asIdeal (resHom v) (fun a ha => resHom_eq_zero v a ha)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨a, rfl⟩ := resHom_surjective v y
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  exact Finite.of_surjective g hg
theorem compactSpace_integer : CompactSpace (Valued.integer (v.adicCompletion F)) := by
  rw [Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]
  refine ⟨?_, ?_, finite_residueField v⟩
  · exact ((Valued.v.integer.toAddSubgroup).isClosed_of_isOpen (Valued.isOpen_integer _)).completeSpace_coe
  · exact (inferInstance : IsDiscreteValuationRing (v.adicCompletionIntegers F))
theorem isCompact_adicCompletionIntegers :
    IsCompact ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  haveI := compactSpace_integer v
  exact isCompact_iff_compactSpace.mpr this
instance compactSpace_set : CompactSpace ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
  isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers v)
instance compactSpace_sub : CompactSpace (v.adicCompletionIntegers F) :=
  isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers v)
end PI.IntAdCpctOpenWork


