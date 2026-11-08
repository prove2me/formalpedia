-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
-- name    : QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T12:16:15.496944+00:00
-- url     : https://prove2.me/theorems/f1dfb88f-4d70-4071-a4a5-24a486142ca0
-- title:
--   LPSModular Fundamental Domain
-- statement:
--   Definitions and structural lemmas for LPSModular Fundamental Domain, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean

import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.Modular
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Data.Countable.Basic
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section
def lpsEffectiveModularGroup : Subgroup (Equiv.Perm ℍ) :=
  (MulAction.toPermHom SL(2,ℤ) ℍ).range
@[instance] lemma lpsEffectiveModularGroup_countable : Countable lpsEffectiveModularGroup := by
  let : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  let : Countable SL(2,ℤ) := (show Function.Injective (fun g : SL(2,ℤ) => g.val) from
    fun g h he => Subtype.ext he).countable
  exact (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict_surjective.countable
lemma lpsEffectiveRepresentative (g : lpsEffectiveModularGroup) :
    ∃ h : SL(2,ℤ), (g : Equiv.Perm ℍ) = MulAction.toPerm h := by
  rcases g.property with ⟨h,hh⟩
  exact ⟨h,hh.symm⟩
lemma lpsEffectiveMeasurePreserving (g : lpsEffectiveModularGroup) :
    MeasurePreserving (fun τ : ℍ => g • τ) volume volume := by
  obtain ⟨h,hh⟩ := lpsEffectiveRepresentative g
  have he : (fun τ : ℍ => g • τ) = (fun τ => (h : GL (Fin 2) ℝ) • τ) := by
    funext τ
    change (g : Equiv.Perm ℍ) τ = _
    rw [hh]
    exact ModularGroup.sl_moeb h τ
  rw [he]
  exact measurePreserving_smul _ _
@[instance] lemma lpsEffectiveMeasurableConstSMul : MeasurableConstSMul lpsEffectiveModularGroup ℍ where
  measurable_const_smul g := (lpsEffectiveMeasurePreserving g).measurable
@[instance] lemma lpsEffectiveSMulInvariantMeasure :
    SMulInvariantMeasure lpsEffectiveModularGroup ℍ volume where
  measure_preimage_smul g _ hs := (lpsEffectiveMeasurePreserving g).measure_preimage hs.nullMeasurableSet
lemma lpsEffectiveKernel (h : SL(2,ℤ)) :
    (MulAction.toPermHom SL(2,ℤ) ℍ) h = 1 ↔ h = 1 ∨ h = -1 := by
  constructor
  · intro hh
    let z : ℍ := ⟨⟨0,2⟩,by norm_num⟩
    have hz : z ∈ ModularGroup.fdo := by norm_num [z,ModularGroup.fdo,Complex.normSq_apply]
    have he : h • z = z := by
      have := congrArg (fun e : Equiv.Perm ℍ => e z) hh
      exact this
    exact ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fdo hz (by simpa only [he] using hz)
  · rintro (rfl | rfl) <;> ext z <;> simp [-ModularGroup.sl_moeb]
lemma lpsEffectiveKernel_le_Gamma0 (N : ℕ) :
    (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict.ker ≤ CongruenceSubgroup.Gamma0 N := by
  intro h hh
  have he : (MulAction.toPermHom SL(2,ℤ) ℍ) h = 1 :=
    congrArg (fun e : lpsEffectiveModularGroup => (e : Equiv.Perm ℍ)) hh
  rcases (lpsEffectiveKernel h).mp he with rfl | rfl <;> simp
def lpsEffectiveGamma0 (N : ℕ) : Subgroup lpsEffectiveModularGroup :=
  (CongruenceSubgroup.Gamma0 N).map (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict
lemma lpsEffectiveGamma0_comap (N : ℕ) :
    (lpsEffectiveGamma0 N).comap (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict =
      CongruenceSubgroup.Gamma0 N :=
  Subgroup.comap_map_eq_self (lpsEffectiveKernel_le_Gamma0 N)
def lpsEffectiveGamma0CosetEquiv (N : ℕ) :
    SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N ≃ lpsEffectiveModularGroup ⧸ lpsEffectiveGamma0 N := by
  let φ : SL(2,ℤ) →* lpsEffectiveModularGroup :=
    (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict
  let f : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N →
      lpsEffectiveModularGroup ⧸ lpsEffectiveGamma0 N :=
    Quotient.map' φ (by
      intro x y hxy
      rw [QuotientGroup.leftRel_apply] at hxy ⊢
      have hm := Subgroup.mem_map_of_mem φ hxy
      rw [map_mul,map_inv] at hm
      exact hm)
  apply Equiv.ofBijective f
  constructor
  · intro x y hxy
    induction x using QuotientGroup.induction_on with | H x =>
      induction y using QuotientGroup.induction_on with | H y =>
        apply Quotient.sound'
        rw [QuotientGroup.leftRel_apply]
        have hh : x⁻¹*y ∈ (lpsEffectiveGamma0 N).comap φ := by
          simpa only [f,Quotient.map'_mk'',QuotientGroup.eq,map_mul,map_inv,
            Subgroup.mem_comap] using hxy
        change x⁻¹*y ∈ (lpsEffectiveGamma0 N).comap
          (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict at hh
        rw [lpsEffectiveGamma0_comap] at hh
        exact hh
  · intro y
    induction y using QuotientGroup.induction_on with | H y =>
      obtain ⟨x,rfl⟩ := (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict_surjective y
      exact ⟨QuotientGroup.mk x,rfl⟩
def lpsCongruenceDomain (H : Subgroup lpsEffectiveModularGroup) : Set ℍ :=
  ⋃ c : lpsEffectiveModularGroup ⧸ H, (Quotient.out c)⁻¹ • ModularGroup.fd
end
end QEC.Coding.TannerLiftedProduct


