-- Prove2me | solution 1 for AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_bifiber_defect
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/37fda448-68c9-52f2-9b57-212b0c90e6fc

import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Basic
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_Place_exists_restrict_eq
import Theorems.Thm_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq
import Theorems.Thm_AlgebraicCurve_Place_restrict_ofAlgAut_smul
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_eq_of_restrict_eq
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_eq_of_restrict_eq
import Theorems.Thm_AlgebraicCurve_Place_card_fiberOver_mul_ramificationIndex_mul_inertiaDeg
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndexAlong_comp
import Theorems.Thm_AlgebraicCurve_Place_inertiaDegAlong_comp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber_defect
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open MulAction

namespace WK2ADev2

section Helpers

private theorem card_eq_mul_of_card_fiber {α β : Type*} [Finite α] [Finite β] (f : α → β) (c : ℕ)
    (hc : ∀ b, Nat.card {a // f a = b} = c) : Nat.card α = Nat.card β * c := by
  classical
  haveI := Fintype.ofFinite β
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv f).symm, Nat.card_sigma, Finset.sum_congr rfl
    (fun b _ => hc b), Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

private theorem card_eq_sum_card_fiber {α β : Type*} [Finite α] [Fintype β] (f : α → β) :
    Nat.card α = ∑ b : β, Nat.card {a // f a = b} := by
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv f).symm, Nat.card_sigma]

private theorem card_preimage_eq_mul_of_card_fiber {α β : Type*} [Finite α] [Finite β] (f : α → β) (c : ℕ)
    (hc : ∀ b, Nat.card {a // f a = b} = c) (t : Set β) :
    Nat.card {a // f a ∈ t} = Nat.card t * c := by
  refine card_eq_mul_of_card_fiber (fun a : {a // f a ∈ t} => (⟨f a.1, a.2⟩ : t)) c ?_
  rintro ⟨b, hb⟩
  rw [← hc b]
  exact Nat.card_congr
    { toFun := fun a => ⟨a.1.1, congrArg Subtype.val a.2⟩
      invFun := fun a => ⟨⟨a.1, show f a.1 ∈ t by rw [a.2]; exact hb⟩, Subtype.ext a.2⟩
      left_inv := fun a => by ext; rfl
      right_inv := fun a => by ext; rfl }

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]

private theorem card_fiber_smul_eq (x : X) (g₀ : G) :
    Nat.card {g : G // g • x = g₀ • x} = Nat.card (stabilizer G x) := by
  refine Nat.card_congr
    { toFun := fun g => ⟨g₀⁻¹ * g.1, by rw [mem_stabilizer_iff, mul_smul, g.2, inv_smul_smul]⟩
      invFun := fun s => ⟨g₀ * s.1, by rw [mul_smul, s.2]⟩
      left_inv := fun g => by ext; simp
      right_inv := fun s => by ext; simp }

private theorem card_smul_mem_eq [Finite G] (H : Subgroup G) (x : X) (B : Set X) :
    Nat.card {h : H // (h : G) • x ∈ B} = (orbit H x ∩ B).ncard * Nat.card (stabilizer H x) := by
  haveI : Finite (orbit H x) := Set.finite_range _ |>.to_subtype
  have hfib : ∀ o : orbit H x, Nat.card {h : H // (⟨h • x, mem_orbit x h⟩ : orbit H x) = o} =
      Nat.card (stabilizer H x) := by
    rintro ⟨_, ⟨h₀, rfl⟩⟩
    rw [← card_fiber_smul_eq x h₀]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun h => by simp [Subtype.ext_iff])
  have := card_preimage_eq_mul_of_card_fiber (fun h : H => (⟨h • x, mem_orbit x h⟩ : orbit H x))
    (Nat.card (stabilizer H x)) hfib {o | (o : X) ∈ B}
  rw [← Nat.card_coe_set_eq]
  have E : ↥(orbit H x ∩ B) ≃ ↥{o : orbit H x | (o : X) ∈ B} :=
    { toFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
      invFun := fun o => ⟨o.1.1, o.1.2, o.2⟩
      left_inv := fun y => rfl
      right_inv := fun o => rfl }
  rw [Nat.card_congr E]
  exact this

private theorem card_pair_set [Finite G] (H₁ H₂ : Subgroup G) (x₁ x₂ : X) :
    Nat.card {p : H₁ × H₂ // (p.1 : G) • x₁ = (p.2 : G) • x₂} =
      (orbit H₁ x₁ ∩ orbit H₂ x₂).ncard * Nat.card (stabilizer H₂ x₂)
        * Nat.card (stabilizer H₁ x₁) := by
  let M := {h₂ : H₂ // (h₂ : G) • x₂ ∈ orbit H₁ x₁}
  have hM : Nat.card M = (orbit H₁ x₁ ∩ orbit H₂ x₂).ncard * Nat.card (stabilizer H₂ x₂) := by
    rw [Set.inter_comm]; exact card_smul_mem_eq H₂ x₂ (orbit H₁ x₁)
  rw [← hM]
  refine card_eq_mul_of_card_fiber
    (fun a : {p : H₁ × H₂ // (p.1 : G) • x₁ = (p.2 : G) • x₂} =>
      (⟨a.1.2, ⟨a.1.1, a.2⟩⟩ : M)) _ ?_
  rintro ⟨h₂, ⟨h₁, hh⟩⟩
  have hh' : (h₁ : G) • x₁ = (h₂ : G) • x₂ := hh
  rw [← card_fiber_smul_eq x₁ (h₁ : H₁)]
  refine Nat.card_congr
    { toFun := fun a => ⟨a.1.1.1, ?_⟩
      invFun := fun h => ⟨⟨(h.1, h₂), ?_⟩, rfl⟩
      left_inv := ?_
      right_inv := ?_ }
  · have e2 : a.1.1.2 = h₂ := congrArg (fun m : M => (m : H₂)) a.2
    show ((a.1.1.1 : H₁) : G) • x₁ = ((h₁ : H₁) : G) • x₁
    rw [hh']
    exact a.1.2.trans (by rw [e2])
  · show ((h.1 : H₁) : G) • x₁ = (h₂ : G) • x₂
    rw [← hh']; exact h.2
  · rintro ⟨⟨⟨a₁, a₂⟩, ha⟩, ha'⟩
    have e2 : a₂ = h₂ := congrArg (fun m : M => (m : H₂)) ha'
    subst e2; rfl
  · intro h; rfl

end Helpers

section Psi

variable {G : Type*} [Group G]

private theorem card_fiber_psi_eq_of_base (H₁ H₂ : Subgroup G) {g : G} (a₁ : H₁) (a₂ : H₂)
    (hbase : (a₂ : G)⁻¹ * a₁ = g) :
    Nat.card {p : H₁ × H₂ // (p.2 : G)⁻¹ * p.1 = g} = Nat.card (H₁ ⊓ H₂ : Subgroup G) := by
  have key : ∀ p : {p : H₁ × H₂ // (p.2 : G)⁻¹ * p.1 = g},
      (p.1.1 : G) * (a₁ : G)⁻¹ = (p.1.2 : G) * (a₂ : G)⁻¹ := by
    rintro ⟨⟨p₁, p₂⟩, hp⟩
    have h1 : (p₂ : G)⁻¹ * p₁ = (a₂ : G)⁻¹ * a₁ := by rw [hp, hbase]
    calc (p₁ : G) * (a₁ : G)⁻¹
        = (p₂ : G) * ((p₂ : G)⁻¹ * p₁) * (a₁ : G)⁻¹ := by group
      _ = (p₂ : G) * ((a₂ : G)⁻¹ * a₁) * (a₁ : G)⁻¹ := by rw [h1]
      _ = (p₂ : G) * (a₂ : G)⁻¹ := by group
  refine Nat.card_congr
    { toFun := fun p => ⟨(p.1.1 : G) * (a₁ : G)⁻¹,
        Subgroup.mem_inf.mpr ⟨H₁.mul_mem p.1.1.2 (H₁.inv_mem a₁.2),
          key p ▸ H₂.mul_mem p.1.2.2 (H₂.inv_mem a₂.2)⟩⟩
      invFun := fun k => ⟨(⟨(k : G) * a₁, H₁.mul_mem (Subgroup.mem_inf.mp k.2).1 a₁.2⟩,
        ⟨(k : G) * a₂, H₂.mul_mem (Subgroup.mem_inf.mp k.2).2 a₂.2⟩), by
          show ((k : G) * a₂)⁻¹ * ((k : G) * a₁) = g
          rw [← hbase]; group⟩
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨⟨p₁, p₂⟩, hp⟩
    have hk := key ⟨⟨p₁, p₂⟩, hp⟩
    refine Subtype.ext (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
    · show (p₁ : G) * (a₁ : G)⁻¹ * a₁ = p₁
      group
    · show (p₁ : G) * (a₁ : G)⁻¹ * a₂ = p₂
      calc (p₁ : G) * (a₁ : G)⁻¹ * a₂ = (p₂ : G) * (a₂ : G)⁻¹ * a₂ := by
            rw [show (p₁ : G) * (a₁ : G)⁻¹ = (p₂ : G) * (a₂ : G)⁻¹ from hk]
        _ = p₂ := by group
  · intro k
    refine Subtype.ext ?_
    show (k : G) * a₁ * (a₁ : G)⁻¹ = k
    group

private theorem card_fiber_psi_eq_zero (H₁ H₂ : Subgroup G) {g : G}
    (h : ¬ ∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = (h₂ : G) * h₁) :
    Nat.card {p : H₁ × H₂ // (p.2 : G)⁻¹ * p.1 = g} = 0 := by
  haveI : IsEmpty {p : H₁ × H₂ // (p.2 : G)⁻¹ * p.1 = g} :=
    ⟨fun p => h ⟨(p.1.2 : G)⁻¹, H₂.inv_mem p.1.2.2, p.1.1, p.1.1.2, p.2.symm⟩⟩
  exact Nat.card_of_isEmpty

variable (s : G)

private theorem card_fiber_psi'_eq_of_base (H₁ H₂ : Subgroup G)
    (hconj : ∀ h : G, h ∈ H₁ ↔ s⁻¹ * h * s ∈ H₂) {g : G} (a₁ : H₁) (a₂ : H₂)
    (hbase : (a₂ : G)⁻¹ * s⁻¹ * a₁ = g) :
    Nat.card {p : H₁ × H₂ // (p.2 : G)⁻¹ * s⁻¹ * p.1 = g} = Nat.card H₂ := by
  have hmem : ∀ t : H₂, s * (t : G) * s⁻¹ * a₁ ∈ H₁ := by
    intro t
    refine H₁.mul_mem ((hconj (s * (t : G) * s⁻¹)).mpr ?_) a₁.2
    have he : s⁻¹ * (s * (t : G) * s⁻¹) * s = (t : G) := by group
    rw [he]
    exact t.2
  refine Nat.card_congr
    { toFun := fun p => ⟨(p.1.2 : G) * (a₂ : G)⁻¹, H₂.mul_mem p.1.2.2 (H₂.inv_mem a₂.2)⟩
      invFun := fun t => ⟨(⟨s * (t : G) * s⁻¹ * a₁, hmem t⟩, ⟨(t : G) * a₂, H₂.mul_mem t.2 a₂.2⟩),
        by
          show ((t : G) * a₂)⁻¹ * s⁻¹ * (s * (t : G) * s⁻¹ * a₁) = g
          rw [← hbase]; group⟩
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨⟨p₁, p₂⟩, hp⟩
    have h1 : (p₁ : G) = s * ((p₂ : G) * (a₂ : G)⁻¹) * s⁻¹ * a₁ := by
      have h0 : (p₂ : G)⁻¹ * s⁻¹ * p₁ = (a₂ : G)⁻¹ * s⁻¹ * a₁ := by rw [hp, hbase]
      calc (p₁ : G) = s * (p₂ : G) * ((p₂ : G)⁻¹ * s⁻¹ * p₁) := by group
        _ = s * (p₂ : G) * ((a₂ : G)⁻¹ * s⁻¹ * a₁) := by rw [h0]
        _ = s * ((p₂ : G) * (a₂ : G)⁻¹) * s⁻¹ * a₁ := by group
    refine Subtype.ext (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
    · show s * ((p₂ : G) * (a₂ : G)⁻¹) * s⁻¹ * a₁ = p₁
      exact h1.symm
    · show (p₂ : G) * (a₂ : G)⁻¹ * a₂ = p₂
      group
  · intro t
    refine Subtype.ext ?_
    show (t : G) * a₂ * (a₂ : G)⁻¹ = t
    group

private theorem card_fiber_psi'_eq_zero (H₁ H₂ : Subgroup G) {g : G}
    (h : ¬ ∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = (h₂ : G) * s⁻¹ * h₁) :
    Nat.card {p : H₁ × H₂ // (p.2 : G)⁻¹ * s⁻¹ * p.1 = g} = 0 := by
  haveI : IsEmpty {p : H₁ × H₂ // (p.2 : G)⁻¹ * s⁻¹ * p.1 = g} :=
    ⟨fun p => h ⟨(p.1.2 : G)⁻¹, H₂.inv_mem p.1.2.2, p.1.1, p.1.1.2, p.2.symm⟩⟩
  exact Nat.card_of_isEmpty

end Psi

section Count

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]

open Classical in

private theorem card_subtype_mul_eq_sum {α : Type*} [Fintype α] (Q : α → Prop) (c : ℕ) :
    Nat.card {a : α // Q a} * c = ∑ a : α, if Q a then c else 0 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← Finset.sum_filter, Finset.sum_const,
    smul_eq_mul]

open Classical in

private theorem card_subtype_eq_sum' {α : Type*} [Fintype α] (Q : α → Prop) :
    Nat.card {a : α // Q a} = ∑ a : α, if Q a then 1 else 0 := by
  simpa using card_subtype_mul_eq_sum Q 1

private theorem card_pairA_eq [Finite G] (H₁ H₂ : Subgroup G) (x₁ x₂ : X) :
    Nat.card {p : H₁ × H₂ // (p.1 : G) • x₁ = (p.2 : G) • x₂}
      = Nat.card {g : G // (g • x₁ = x₂) ∧ ∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * h₁}
          * Nat.card (H₁ ⊓ H₂ : Subgroup G) := by
  classical
  haveI := Fintype.ofFinite G
  have hiff : ∀ p : H₁ × H₂, (((p.1 : G)) • x₁ = ((p.2 : G)) • x₂) ↔
      (((p.2 : G)⁻¹ * p.1) • x₁ = x₂) := by
    intro p
    rw [mul_smul, inv_smul_eq_iff]
  rw [card_eq_sum_card_fiber
    (fun p : {p : H₁ × H₂ // (p.1 : G) • x₁ = (p.2 : G) • x₂} => (p.1.2 : G)⁻¹ * p.1.1),
    card_subtype_mul_eq_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases ht : g • x₁ = x₂
  · by_cases hP : ∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * h₁
    · rw [if_pos ⟨ht, hP⟩]
      obtain ⟨h₂, hh₂, h₁, hh₁, hg⟩ := hP
      have hbase : ((⟨h₂⁻¹, H₂.inv_mem hh₂⟩ : H₂) : G)⁻¹ * ((⟨h₁, hh₁⟩ : H₁) : G) = g := by
        simp [hg]
      rw [← card_fiber_psi_eq_of_base H₁ H₂ ⟨h₁, hh₁⟩ ⟨h₂⁻¹, H₂.inv_mem hh₂⟩ hbase]
      refine Nat.card_congr
        { toFun := fun a => ⟨a.1.1, a.2⟩
          invFun := fun p => ⟨⟨p.1, (hiff p.1).mpr (by rw [p.2]; exact ht)⟩, p.2⟩
          left_inv := fun a => rfl
          right_inv := fun p => rfl }
    · rw [if_neg (fun hc => hP hc.2)]
      haveI : IsEmpty {a : {p : H₁ × H₂ // (p.1 : G) • x₁ = (p.2 : G) • x₂} //
          (a.1.2 : G)⁻¹ * a.1.1 = g} := by
        refine ⟨fun a => hP ?_⟩
        exact ⟨(a.1.1.2 : G)⁻¹, H₂.inv_mem a.1.1.2.2, a.1.1.1, a.1.1.1.2, a.2.symm⟩
      exact Nat.card_of_isEmpty
  · rw [if_neg (fun hc => ht hc.1)]
    haveI : IsEmpty {a : {p : H₁ × H₂ // (p.1 : G) • x₁ = (p.2 : G) • x₂} //
        (a.1.2 : G)⁻¹ * a.1.1 = g} := by
      refine ⟨fun a => ht ?_⟩
      rw [← a.2]
      exact (hiff a.1.1).mp a.1.2
    exact Nat.card_of_isEmpty

variable (s : G)

private theorem card_pairA'_eq [Finite G] (H₁ H₂ : Subgroup G)
    (hconj : ∀ h : G, h ∈ H₁ ↔ s⁻¹ * h * s ∈ H₂) (x₁ x₂ : X) :
    Nat.card {p : H₁ × H₂ // (((p.2 : G)⁻¹ * s⁻¹ * p.1) • x₁ = x₂)}
      = Nat.card {g : G // (g • x₁ = x₂) ∧ ∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * s⁻¹ * h₁}
          * Nat.card H₂ := by
  classical
  haveI := Fintype.ofFinite G
  rw [card_eq_sum_card_fiber
    (fun p : {p : H₁ × H₂ // (((p.2 : G)⁻¹ * s⁻¹ * p.1) • x₁ = x₂)} =>
      (p.1.2 : G)⁻¹ * s⁻¹ * p.1.1),
    card_subtype_mul_eq_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases ht : g • x₁ = x₂
  · by_cases hP : ∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * s⁻¹ * h₁
    · rw [if_pos ⟨ht, hP⟩]
      obtain ⟨h₂, hh₂, h₁, hh₁, hg⟩ := hP
      have hbase : ((⟨h₂⁻¹, H₂.inv_mem hh₂⟩ : H₂) : G)⁻¹ * s⁻¹ * ((⟨h₁, hh₁⟩ : H₁) : G) = g := by
        simp [hg, mul_assoc]
      rw [← card_fiber_psi'_eq_of_base s H₁ H₂ hconj ⟨h₁, hh₁⟩ ⟨h₂⁻¹, H₂.inv_mem hh₂⟩ hbase]
      refine Nat.card_congr
        { toFun := fun a => ⟨a.1.1, a.2⟩
          invFun := fun p => ⟨⟨p.1, by rw [p.2]; exact ht⟩, p.2⟩
          left_inv := fun a => rfl
          right_inv := fun p => rfl }
    · rw [if_neg (fun hc => hP hc.2)]
      haveI : IsEmpty {a : {p : H₁ × H₂ // (((p.2 : G)⁻¹ * s⁻¹ * p.1) • x₁ = x₂)} //
          (a.1.2 : G)⁻¹ * s⁻¹ * a.1.1 = g} := by
        refine ⟨fun a => hP ?_⟩
        exact ⟨(a.1.1.2 : G)⁻¹, H₂.inv_mem a.1.1.2.2, a.1.1.1, a.1.1.1.2, a.2.symm⟩
      exact Nat.card_of_isEmpty
  · rw [if_neg (fun hc => ht hc.1)]
    haveI : IsEmpty {a : {p : H₁ × H₂ // (((p.2 : G)⁻¹ * s⁻¹ * p.1) • x₁ = x₂)} //
        (a.1.2 : G)⁻¹ * s⁻¹ * a.1.1 = g} := by
      refine ⟨fun a => ht ?_⟩
      rw [← a.2]
      exact a.1.2
    exact Nat.card_of_isEmpty

private theorem card_pairA'_transmute (H₁ H₂ : Subgroup G)
    (hconj : ∀ h : G, h ∈ H₁ ↔ s⁻¹ * h * s ∈ H₂) (x₁ x₂ : X) :
    Nat.card {p : H₁ × H₂ // (((p.2 : G)⁻¹ * s⁻¹ * p.1) • x₁ = x₂)}
      = Nat.card {q : H₂ × H₂ // (q.1 : G) • (s⁻¹ • x₁) = (q.2 : G) • x₂} := by
  have hmem₂ : ∀ k : H₂, s * (k : G) * s⁻¹ ∈ H₁ := by
    intro k
    refine (hconj (s * (k : G) * s⁻¹)).mpr ?_
    have he : s⁻¹ * (s * (k : G) * s⁻¹) * s = (k : G) := by group
    rw [he]
    exact k.2
  have hcond : ∀ a b : G, ((b⁻¹ * s⁻¹ * a) • x₁ = x₂) ↔
      ((s⁻¹ * a * s) • (s⁻¹ • x₁) = b • x₂) := by
    intro a b
    rw [smul_smul, show s⁻¹ * a * s * s⁻¹ = s⁻¹ * a by group, ← inv_smul_eq_iff (g := b),
      smul_smul, show b⁻¹ * (s⁻¹ * a) = b⁻¹ * s⁻¹ * a by group]
  refine Nat.card_congr
    { toFun := fun p => ⟨(⟨s⁻¹ * p.1.1 * s, (hconj p.1.1).mp p.1.1.2⟩, p.1.2),
        (hcond p.1.1 p.1.2).mp p.2⟩
      invFun := fun q => ⟨(⟨s * q.1.1 * s⁻¹, hmem₂ q.1.1⟩, q.1.2), by
        refine (hcond (s * q.1.1 * s⁻¹) q.1.2).mpr ?_
        have he : s⁻¹ * (s * (q.1.1 : G) * s⁻¹) * s = (q.1.1 : G) := by group
        rw [he]
        exact q.2⟩
      left_inv := by
        rintro ⟨⟨p₁, p₂⟩, hp⟩
        refine Subtype.ext (Prod.ext (Subtype.ext ?_) rfl)
        show s * (s⁻¹ * (p₁ : G) * s) * s⁻¹ = p₁
        group
      right_inv := by
        rintro ⟨⟨q₁, q₂⟩, hq⟩
        refine Subtype.ext (Prod.ext (Subtype.ext ?_) rfl)
        show s⁻¹ * (s * (q₁ : G) * s⁻¹) * s = q₁
        group }

private theorem card_t_split [Finite G]
    (P₁ P₂ : G → Prop) (hcover : ∀ g : G, P₁ g ∨ P₂ g) (hdisj : ∀ g : G, ¬(P₁ g ∧ P₂ g))
    (x₁ x₂ : X) :
    Nat.card {g : G // (g • x₁ = x₂) ∧ P₁ g} + Nat.card {g : G // (g • x₁ = x₂) ∧ P₂ g}
      = Nat.card {g : G // g • x₁ = x₂} := by
  classical
  haveI := Fintype.ofFinite G
  rw [card_subtype_eq_sum', card_subtype_eq_sum', card_subtype_eq_sum', ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases ht : g • x₁ = x₂
  · rcases hcover g with hP | hP
    · rw [if_pos ⟨ht, hP⟩, if_neg (fun hc => hdisj g ⟨hP, hc.2⟩), if_pos ht]
    · rw [if_neg (fun hc => hdisj g ⟨hc.2, hP⟩), if_pos ⟨ht, hP⟩, if_pos ht]
  · rw [if_neg (fun hc => ht hc.1), if_neg (fun hc => ht hc.1), if_neg ht]

private theorem card_t_eq [IsPretransitive G X] (x₁ x₂ : X) :
    Nat.card {g : G // g • x₁ = x₂} = Nat.card (stabilizer G x₁) := by
  obtain ⟨g₀, hg₀⟩ := exists_smul_eq G x₁ x₂
  rw [← card_fiber_smul_eq x₁ g₀]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by rw [hg₀])

end Count

section Main

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]

open Classical in

private theorem ncard_orbit_inter_orbit_defect [Finite G] [IsPretransitive G X]
    (H₁ H₂ : Subgroup G) (s : G)
    (hconj : ∀ h : G, h ∈ H₁ ↔ s⁻¹ * h * s ∈ H₂)
    (hcover : ∀ g : G,
      (∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * h₁) ∨ (∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * s⁻¹ * h₁))
    (hdisj : ∀ g : G,
      ¬((∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * h₁) ∧ (∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * s⁻¹ * h₁)))
    (x₁ x₂ : X) :
    (H₁ ⊓ H₂ : Subgroup G).index * ((orbit H₁ x₁ ∩ orbit H₂ x₂).ncard * Nat.card X)
      + (if x₂ ∈ orbit H₂ (s⁻¹ • x₁) then H₁.index * ((orbit H₁ x₁).ncard * Nat.card X) else 0)
      = H₁.index * H₂.index * ((orbit H₁ x₁).ncard * (orbit H₂ x₂).ncard) := by
  classical
  haveI : Finite X := Finite.of_surjective (fun g : G => g • x₁) (surjective_smul G x₁)
  have hA₂ := card_pair_set H₁ H₂ x₁ x₂
  have hA₁ := card_pairA_eq H₁ H₂ x₁ x₂
  have hA'' := (card_pairA'_transmute s H₁ H₂ hconj x₁ x₂).symm.trans
    (card_pairA'_eq s H₁ H₂ hconj x₁ x₂)
  have hA''₂ := card_pair_set H₂ H₂ (s⁻¹ • x₁) x₂
  have hsplit : Nat.card {g : G // (g • x₁ = x₂) ∧ ∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * h₁}
      + Nat.card {g : G // (g • x₁ = x₂) ∧ ∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * s⁻¹ * h₁}
      = Nat.card {g : G // g • x₁ = x₂} :=
    card_t_split (X := X) _ _ hcover hdisj x₁ x₂
  have hT := card_t_eq (G := G) x₁ x₂
  set c₁ := Nat.card (stabilizer H₁ x₁) with hc₁
  set c₂ := Nat.card (stabilizer H₂ x₂) with hc₂
  set c₂' := Nat.card (stabilizer H₂ (s⁻¹ • x₁)) with hc₂'
  set d := Nat.card (H₁ ⊓ H₂ : Subgroup G) with hd
  set S := Nat.card (stabilizer G x₁) with hS
  set nO₁ := (orbit H₁ x₁).ncard with hnO₁
  set nO₂ := (orbit H₂ x₂).ncard with hnO₂
  set nI := (orbit H₁ x₁ ∩ orbit H₂ x₂).ncard with hnI
  set nI' := (orbit H₂ (s⁻¹ • x₁) ∩ orbit H₂ x₂).ncard with hnI'

  have hdiam : (nI * c₂ * c₁) * Nat.card H₂ + (nI' * c₂ * c₂') * d = S * d * Nat.card H₂ := by
    rw [← hA₂, ← hA''₂, hA₁, hA'', ← hT, ← hsplit]
    ring
  have hO₁ : nO₁ * c₁ = Nat.card H₁ := by
    rw [hnO₁, hc₁, ← MulAction.index_stabilizer H₁ x₁, mul_comm, Subgroup.card_mul_index]
  have hO₂ : nO₂ * c₂ = Nat.card H₂ := by
    rw [hnO₂, hc₂, ← MulAction.index_stabilizer H₂ x₂, mul_comm, Subgroup.card_mul_index]
  have hX : Nat.card X * S = Nat.card G := by
    rw [hS, ← MulAction.index_stabilizer_of_transitive G x₁, mul_comm, Subgroup.card_mul_index]
  have hL₁ : Nat.card H₁ * H₁.index = Nat.card G := Subgroup.card_mul_index H₁
  have hL₂ : Nat.card H₂ * H₂.index = Nat.card G := Subgroup.card_mul_index H₂
  have hLd : d * (H₁ ⊓ H₂ : Subgroup G).index = Nat.card G := by
    rw [hd]; exact Subgroup.card_mul_index _
  have hpos : 0 < c₁ * c₂ * d * S :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos Nat.card_pos Nat.card_pos) Nat.card_pos) Nat.card_pos
  by_cases hm : x₂ ∈ orbit H₂ (s⁻¹ • x₁)
  ·
    have horb : orbit H₂ (s⁻¹ • x₁) = orbit H₂ x₂ := by
      obtain ⟨k, hk⟩ := hm
      have hk' : (k : G) • (s⁻¹ • x₁) = x₂ := hk
      ext y
      constructor
      · rintro ⟨h, rfl⟩
        refine ⟨h * k⁻¹, ?_⟩
        show ((h * k⁻¹ : H₂) : G) • x₂ = (h : G) • (s⁻¹ • x₁)
        push_cast
        rw [mul_smul, ← hk', inv_smul_smul]
      · rintro ⟨h, rfl⟩
        refine ⟨h * k, ?_⟩
        show ((h * k : H₂) : G) • (s⁻¹ • x₁) = (h : G) • x₂
        push_cast
        rw [mul_smul, hk']
    have hI' : nI' = nO₂ := by rw [hnI', horb, Set.inter_self, hnO₂]
    have hc₂'₂ : nO₂ * c₂' = Nat.card H₂ := by
      have h1 : (orbit H₂ (s⁻¹ • x₁)).ncard * c₂' = Nat.card H₂ := by
        rw [hc₂', ← MulAction.index_stabilizer H₂ (s⁻¹ • x₁), mul_comm,
          Subgroup.card_mul_index]
      rwa [horb, ← hnO₂] at h1
    have hO₂pos : 0 < nO₂ := by
      rw [hnO₂]
      exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨x₂, MulAction.mem_orbit_self x₂⟩
    have hcc : c₂' = c₂ := Nat.eq_of_mul_eq_mul_left hO₂pos (hc₂'₂.trans hO₂.symm)
    rw [if_pos hm]
    have key : nI * c₂ * c₁ + c₂ * d = S * d := by
      refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := H₂)) ?_
      have e3 : (nI' * c₂ * c₂') * d = (c₂ * d) * Nat.card H₂ := by
        rw [hI', hcc]
        calc nO₂ * c₂ * c₂ * d = (nO₂ * c₂) * (c₂ * d) := by ring
          _ = Nat.card H₂ * (c₂ * d) := by rw [hO₂]
          _ = (c₂ * d) * Nat.card H₂ := by ring
      calc (nI * c₂ * c₁ + c₂ * d) * Nat.card H₂
          = (nI * c₂ * c₁) * Nat.card H₂ + (c₂ * d) * Nat.card H₂ := by ring
        _ = (nI * c₂ * c₁) * Nat.card H₂ + (nI' * c₂ * c₂') * d := by rw [e3]
        _ = S * d * Nat.card H₂ := hdiam
        _ = (S * d) * Nat.card H₂ := by ring
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    calc ((H₁ ⊓ H₂ : Subgroup G).index * (nI * Nat.card X)
          + H₁.index * (nO₁ * Nat.card X)) * (c₁ * c₂ * d * S)
        = (d * (H₁ ⊓ H₂ : Subgroup G).index) * (Nat.card X * S) * (nI * c₂ * c₁)
            + (nO₁ * c₁ * H₁.index) * (Nat.card X * S) * (c₂ * d) := by ring
      _ = Nat.card G * Nat.card G * (nI * c₂ * c₁)
            + (Nat.card H₁ * H₁.index) * Nat.card G * (c₂ * d) := by rw [hLd, hX, hO₁]
      _ = Nat.card G * Nat.card G * (nI * c₂ * c₁ + c₂ * d) := by rw [hL₁]; ring
      _ = Nat.card G * Nat.card G * (S * d) := by rw [key]
      _ = (Nat.card H₁ * H₁.index) * (Nat.card H₂ * H₂.index) * (S * d) := by rw [hL₁, hL₂]
      _ = (nO₁ * c₁ * H₁.index) * (nO₂ * c₂ * H₂.index) * (S * d) := by rw [hO₁, hO₂]
      _ = (H₁.index * H₂.index * (nO₁ * nO₂)) * (c₁ * c₂ * d * S) := by ring
  ·
    have hI' : nI' = 0 := by
      rw [hnI', Set.ncard_eq_zero (Set.toFinite _)]
      ext y
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      rintro ⟨h, rfl⟩ ⟨k, hk⟩
      have hk' : (k : G) • x₂ = (h : G) • (s⁻¹ • x₁) := hk
      refine hm ⟨k⁻¹ * h, ?_⟩
      show ((k⁻¹ * h : H₂) : G) • (s⁻¹ • x₁) = x₂
      push_cast
      rw [mul_smul, ← hk', inv_smul_smul]
    rw [if_neg hm, add_zero]
    have key : nI * c₂ * c₁ = S * d := by
      refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := H₂)) ?_
      have h2 := hdiam
      rw [hI'] at h2
      simpa using h2
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    calc ((H₁ ⊓ H₂ : Subgroup G).index * (nI * Nat.card X)) * (c₁ * c₂ * d * S)
        = (d * (H₁ ⊓ H₂ : Subgroup G).index) * (Nat.card X * S) * (nI * c₂ * c₁) := by ring
      _ = Nat.card G * Nat.card G * (nI * c₂ * c₁) := by rw [hLd, hX]
      _ = Nat.card G * Nat.card G * (S * d) := by rw [key]
      _ = (Nat.card H₁ * H₁.index) * (Nat.card H₂ * H₂.index) * (S * d) := by rw [hL₁, hL₂]
      _ = (nO₁ * c₁ * H₁.index) * (nO₂ * c₂ * H₂.index) * (S * d) := by rw [hO₁, hO₂]
      _ = (H₁.index * H₂.index * (nO₁ * nO₂)) * (c₁ * c₂ * d * S) := by ring

end Main

section Companion

variable {G : Type*} [Group G]

open Classical in

private theorem cover_disjoint_of_index [Finite G] (H₁ H₂ : Subgroup G) (s : G)
    (hconj : ∀ h : G, h ∈ H₁ ↔ s⁻¹ * h * s ∈ H₂)
    (hidx : (H₁ ⊓ H₂ : Subgroup G).index + H₁.index = H₁.index * H₂.index)
    (hn : H₂.index ≠ 2) :
    (∀ g : G,
      (∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * h₁) ∨ (∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * s⁻¹ * h₁))
      ∧ (∀ g : G,
        ¬((∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * h₁) ∧ (∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * s⁻¹ * h₁))) := by
  classical
  haveI := Fintype.ofFinite G

  have hcard12 : Nat.card H₁ = Nat.card H₂ := by
    refine Nat.card_congr
      { toFun := fun h => ⟨s⁻¹ * (h : G) * s, (hconj h).mp h.2⟩
        invFun := fun k => ⟨s * (k : G) * s⁻¹, (hconj (s * (k : G) * s⁻¹)).mpr (by
          have he : s⁻¹ * (s * (k : G) * s⁻¹) * s = (k : G) := by group
          rw [he]; exact k.2)⟩
        left_inv := fun h => Subtype.ext (by show s * (s⁻¹ * (h : G) * s) * s⁻¹ = h; group)
        right_inv := fun k => Subtype.ext (by show s⁻¹ * (s * (k : G) * s⁻¹) * s = k; group) }
  have hidx12 : H₁.index = H₂.index := by
    have h1 : Nat.card H₁ * H₁.index = Nat.card H₁ * H₂.index := by
      rw [Subgroup.card_mul_index, hcard12, Subgroup.card_mul_index]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1

  have hdisj : ∀ g : G,
      ¬((∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * h₁) ∧ (∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * s⁻¹ * h₁)) := by
    rintro g ⟨⟨h₂, hh₂, h₁, hh₁, he₁⟩, ⟨k₂, hk₂, k₁, hk₁, he₂⟩⟩

    have hs : s⁻¹ = (k₂⁻¹ * h₂) * (h₁ * k₁⁻¹) := by
      have h0 : h₂ * h₁ = k₂ * s⁻¹ * k₁ := he₁.symm.trans he₂
      have h1 : k₂⁻¹ * (h₂ * h₁) * k₁⁻¹ = s⁻¹ := by rw [h0]; group
      rw [← h1]; group
    set u := k₂⁻¹ * h₂ with hu
    set v := h₁ * k₁⁻¹ with hv
    have hu₂ : u ∈ H₂ := H₂.mul_mem (H₂.inv_mem hk₂) hh₂
    have hv₁ : v ∈ H₁ := H₁.mul_mem hh₁ (H₁.inv_mem hk₁)

    have hs' : s = (u * v)⁻¹ := by rw [← hs, inv_inv]
    have hconj_u : ∀ w : G, u * w * u⁻¹ ∈ H₂ ↔ w ∈ H₂ := by
      intro w
      constructor
      · intro hw
        have he : w = u⁻¹ * (u * w * u⁻¹) * u := by group
        rw [he]
        exact H₂.mul_mem (H₂.mul_mem (H₂.inv_mem hu₂) hw) hu₂
      · intro hw
        exact H₂.mul_mem (H₂.mul_mem hu₂ hw) (H₂.inv_mem hu₂)
    have key : ∀ h : G, h ∈ H₁ ↔ v * h * v⁻¹ ∈ H₂ := by
      intro h
      rw [hconj h]
      have he : s⁻¹ * h * s = u * (v * h * v⁻¹) * u⁻¹ := by
        rw [hs, hs']; group
      rw [he, hconj_u]
    have hHH : H₁ = H₂ := by
      apply le_antisymm
      · intro k hk
        have hk' : v⁻¹ * k * v ∈ H₁ :=
          H₁.mul_mem (H₁.mul_mem (H₁.inv_mem hv₁) hk) hv₁
        have := (key (v⁻¹ * k * v)).mp hk'
        have he : v * (v⁻¹ * k * v) * v⁻¹ = k := by group
        rwa [he] at this
      · intro k hk
        have hk' : v * (v⁻¹ * k * v) * v⁻¹ ∈ H₂ := by
          have he : v * (v⁻¹ * k * v) * v⁻¹ = k := by group
          rwa [he]
        have := (key (v⁻¹ * k * v)).mpr hk'
        have he : k = v * (v⁻¹ * k * v) * v⁻¹ := by group
        rw [he]
        exact H₁.mul_mem (H₁.mul_mem hv₁ this) (H₁.inv_mem hv₁)

    have hinf : (H₁ ⊓ H₂ : Subgroup G) = H₁ := by rw [hHH, inf_idem]
    rw [hinf, hidx12] at hidx
    have hne : H₂.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h2 : H₂.index * 2 = H₂.index * H₂.index := by omega
    exact hn ((Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) h2).symm)
  refine ⟨?_, hdisj⟩

  have hD1 : Nat.card {g : G // ∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * h₁}
      * Nat.card (H₁ ⊓ H₂ : Subgroup G)
      = Nat.card H₁ * Nat.card H₂ := by
    conv_rhs => rw [← Nat.card_prod]
    rw [card_eq_sum_card_fiber
      (fun p : H₁ × H₂ => (p.2 : G)⁻¹ * p.1), card_subtype_mul_eq_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hP : ∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * h₁
    · rw [if_pos hP]
      obtain ⟨h₂, hh₂, h₁, hh₁, hg⟩ := hP
      exact (card_fiber_psi_eq_of_base (g := g) H₁ H₂ ⟨h₁, hh₁⟩ ⟨h₂⁻¹, H₂.inv_mem hh₂⟩
        (by simp [hg])).symm
    · rw [if_neg hP]
      exact (card_fiber_psi_eq_zero H₁ H₂ hP).symm
  have hD2 : Nat.card {g : G // ∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * s⁻¹ * h₁} * Nat.card H₂
      = Nat.card H₁ * Nat.card H₂ := by
    conv_rhs => rw [← Nat.card_prod]
    rw [card_eq_sum_card_fiber
      (fun p : H₁ × H₂ => (p.2 : G)⁻¹ * s⁻¹ * p.1), card_subtype_mul_eq_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hP : ∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * s⁻¹ * h₁
    · rw [if_pos hP]
      obtain ⟨h₂, hh₂, h₁, hh₁, hg⟩ := hP
      exact (card_fiber_psi'_eq_of_base (g := g) s H₁ H₂ hconj ⟨h₁, hh₁⟩ ⟨h₂⁻¹, H₂.inv_mem hh₂⟩
        (by simp [hg, mul_assoc])).symm
    · rw [if_neg hP]
      exact (card_fiber_psi'_eq_zero s H₁ H₂ hP).symm

  set d := Nat.card (H₁ ⊓ H₂ : Subgroup G) with hd
  have hn₁ : Nat.card H₁ * H₁.index = Nat.card G := Subgroup.card_mul_index H₁
  have hn₂ : Nat.card H₂ * H₂.index = Nat.card G := Subgroup.card_mul_index H₂
  have hnd : d * (H₁ ⊓ H₂ : Subgroup G).index = Nat.card G := Subgroup.card_mul_index _
  have hE : Nat.card H₂ + d = H₁.index * d := by
    have h1 : H₂.index * (Nat.card H₂ + d) = H₂.index * (H₁.index * d) := by
      have h2 : H₂.index * Nat.card H₂ = Nat.card G := by rw [mul_comm]; exact hn₂
      have h3 : H₂.index * (H₁.index * d) = ((H₁ ⊓ H₂ : Subgroup G).index + H₁.index) * d := by
        rw [hidx]; ring
      rw [mul_add, h2, h3, add_mul, mul_comm (H₁ ⊓ H₂ : Subgroup G).index d, hnd, hidx12]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h1
  have hsum : (Nat.card {g : G // ∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * h₁}
      + Nat.card {g : G // ∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * s⁻¹ * h₁}) * (d * Nat.card H₂)
      = Nat.card G * (d * Nat.card H₂) := by
    calc (Nat.card {g : G // ∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * h₁}
          + Nat.card {g : G // ∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * s⁻¹ * h₁}) * (d * Nat.card H₂)
        = (Nat.card {g : G // ∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * h₁} * d) * Nat.card H₂
            + (Nat.card {g : G // ∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * s⁻¹ * h₁} * Nat.card H₂) * d := by
          ring
      _ = (Nat.card H₁ * Nat.card H₂) * Nat.card H₂ + (Nat.card H₁ * Nat.card H₂) * d := by
          rw [hD1, hD2]
      _ = Nat.card H₁ * (Nat.card H₂ + d) * Nat.card H₂ := by ring
      _ = Nat.card H₁ * (H₁.index * d) * Nat.card H₂ := by rw [hE]
      _ = Nat.card G * (d * Nat.card H₂) := by rw [← hn₁]; ring
  have hcards : Nat.card {g : G // (∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * h₁)
      ∨ (∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * s⁻¹ * h₁)} = Nat.card G := by
    have hpos : 0 < d * Nat.card H₂ := Nat.mul_pos Nat.card_pos Nat.card_pos
    have hsplit : Nat.card {g : G // (∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * h₁)
        ∨ (∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * s⁻¹ * h₁)}
        = Nat.card {g : G // ∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * h₁}
          + Nat.card {g : G // ∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * s⁻¹ * h₁} := by
      rw [card_subtype_eq_sum', card_subtype_eq_sum', card_subtype_eq_sum',
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun g _ => ?_
      by_cases hP : ∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * h₁
      · rw [if_pos (Or.inl hP), if_pos hP, if_neg (fun hc => hdisj g ⟨hP, hc⟩)]
      · by_cases hP' : ∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, g = h₂ * s⁻¹ * h₁
        · rw [if_pos (Or.inr hP'), if_neg hP, if_pos hP']
        · rw [if_neg (fun hc => hc.elim hP hP'), if_neg hP, if_neg hP']
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [hsplit]
    exact hsum

  intro g
  by_contra hg
  have hssub : {x : G | (∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, x = h₂ * h₁)
      ∨ (∃ h₂ ∈ H₂, ∃ h₁ ∈ H₁, x = h₂ * s⁻¹ * h₁)} = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
    rw [Set.ncard_univ, ← Nat.card_coe_set_eq]
    exact le_of_eq hcards.symm
  exact hg (Set.eq_univ_iff_forall.mp hssub g)

end Companion

section GaloisFramework

open AlgebraicCurve
section AlongBridge

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

private theorem inertiaDegAlong_congr {φ φ' : F →ₐ[K] F'} (h : φ = φ') (hφ : φ.toRingHom.IsIntegral)
    (hφ' : φ'.toRingHom.IsIntegral) (w : Place K F') :
    w.inertiaDegAlong φ hφ = w.inertiaDegAlong φ' hφ' := by
  subst h; rfl

variable [Algebra F F'] [IsScalarTower K F F']

private theorem isIntegral_toAlgHom [Algebra.IsIntegral F F'] :
    (IsScalarTower.toAlgHom K F F').toRingHom.IsIntegral :=
  fun x => Algebra.IsIntegral.isIntegral (R := F) x

end AlongBridge

section Tower

variable {K F E M : Type*} [Field K] [Field F] [Field E] [Field M]
    [Algebra K F] [Algebra K E] [Algebra K M] [Algebra F E] [Algebra E M] [Algebra F M]
    [IsScalarTower F E M] [IsScalarTower K F E] [IsScalarTower K E M] [IsScalarTower K F M]

private theorem toAlgHom_comp_toAlgHom :
    (IsScalarTower.toAlgHom K E M).comp (IsScalarTower.toAlgHom K F E) =
      IsScalarTower.toAlgHom K F M :=
  AlgHom.ext fun x => (IsScalarTower.algebraMap_apply F E M x).symm

private theorem restrict_restrict [Algebra.IsIntegral F E] [Algebra.IsIntegral E M]
    [Algebra.IsIntegral F M] (W : Place K M) : (W.restrict E).restrict F = W.restrict F :=
  Place.ext (by
    simp only [Place.restrict_toValuationSubring, ValuationSubring.comap_comap,
      ← IsScalarTower.algebraMap_eq])

end Tower

section TowerRows

variable {K F E M : Type*} [Field K] [Field F] [Field E] [Field M]
    [Algebra K F] [Algebra K E] [Algebra K M] [Algebra F E] [Algebra E M] [Algebra F M]
    [IsScalarTower F E M] [IsScalarTower K F E] [IsScalarTower K E M] [IsScalarTower K F M]

private theorem ramificationIndex_eq_mul_restrict
    [Algebra.IsIntegral F E] [Algebra.IsIntegral E M] (W : Place K M) :
    W.ramificationIndex F = W.ramificationIndex E * (W.restrict E).ramificationIndex F := by
  have h := Place.ramificationIndexAlong_comp (IsScalarTower.toAlgHom K F E)
    (IsScalarTower.toAlgHom K E M) isIntegral_toAlgHom isIntegral_toAlgHom
    (by rw [toAlgHom_comp_toAlgHom]
        haveI : Algebra.IsIntegral F M := Algebra.IsIntegral.trans E
        exact isIntegral_toAlgHom) W
  rw [toAlgHom_comp_toAlgHom] at h
  exact h

private theorem inertiaDeg_eq_mul_restrict
    [Algebra.IsIntegral F E] [Algebra.IsIntegral E M] [Algebra.IsIntegral F M] (W : Place K M) :
    W.inertiaDeg F = W.inertiaDeg E * (W.restrict E).inertiaDeg F := by
  have h := Place.inertiaDegAlong_comp (IsScalarTower.toAlgHom K F E)
    (IsScalarTower.toAlgHom K E M) isIntegral_toAlgHom isIntegral_toAlgHom
    (by rw [toAlgHom_comp_toAlgHom]; exact isIntegral_toAlgHom) W
  rw [inertiaDegAlong_congr toAlgHom_comp_toAlgHom _
    isIntegral_toAlgHom] at h
  exact h

end TowerRows

section Action

variable (F M : Type*) [Field F] [Field M] [Algebra F M]

private def resHom (L : Type*) [Field L] [Algebra F L] [Algebra L M] [IsScalarTower F L M] :
    (M ≃ₐ[L] M) →* (M ≃ₐ[F] M) where
  toFun σ := σ.restrictScalars F
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

variable (K : Type*) [Field K] [Algebra K F] [Algebra K M] [IsScalarTower K F M]

@[reducible] private noncomputable def galAction : MulAction (M ≃ₐ[F] M) (Place K M) :=
  MulAction.compHom (Place K M)
    ((SemilinearAut.ofAlgAut (K := K) (F := M)).comp (resHom K M F))

attribute [local instance] galAction

variable {K F M}

private theorem gal_smul_def (g : M ≃ₐ[F] M) (W : Place K M) :
    g • W = SemilinearAut.ofAlgAut (g.restrictScalars K) • W := rfl

variable {L : Type*} [Field L] [Algebra F L] [Algebra L M] [IsScalarTower F L M]

private theorem mem_range_resHom_iff {g : M ≃ₐ[F] M} :
    g ∈ (resHom F M L).range ↔ ∀ x : L, g (algebraMap L M x) = algebraMap L M x := by
  constructor
  · rintro ⟨τ, rfl⟩ x
    exact τ.commutes x
  · intro h
    exact ⟨AlgEquiv.ofRingEquiv (f := (g : M ≃+* M)) h, AlgEquiv.ext fun _ => rfl⟩

private theorem card_range_resHom : Nat.card (resHom F M L).range = Nat.card (M ≃ₐ[L] M) :=
  (Nat.card_congr (MonoidHom.ofInjective (f := resHom F M L)
    (fun _ _ h => AlgEquiv.restrictScalars_injective F h)).toEquiv).symm

private theorem index_range_resHom [FiniteDimensional F M] [IsGalois F M] [FiniteDimensional L M]
    [IsGalois L M] : (resHom F M L).range.index = Module.finrank F L := by
  have h1 := Subgroup.card_mul_index (resHom F M L).range
  rw [card_range_resHom, IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank] at h1
  have h2 := Module.finrank_mul_finrank F L M
  have hpos : 0 < Module.finrank L M := Module.finrank_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h1, ← h2, mul_comm]

variable [Algebra K L] [IsScalarTower K L M]

private theorem orbit_range_resHom_eq [FiniteDimensional L M] [IsGalois L M] (P : Place K M) :
    MulAction.orbit (resHom F M L).range P = ↑((P.restrict L).fiberOver M) := by
  ext Q
  rw [MulAction.mem_orbit_iff, Finset.mem_coe, Place.mem_fiberOver]
  constructor
  · rintro ⟨⟨_, τ, rfl⟩, rfl⟩
    exact Place.restrict_ofAlgAut_smul τ P
  · intro h
    obtain ⟨σ, hσ⟩ := Place.exists_algEquiv_smul_eq_of_restrict_eq P Q h
    exact ⟨⟨σ.restrictScalars F, σ, rfl⟩, hσ⟩

omit [Algebra F L] [Algebra L M] [IsScalarTower F L M] [Algebra K L] [IsScalarTower K L M] in

private theorem orbit_gal_eq [FiniteDimensional F M] [IsGalois F M] (P : Place K M) :
    MulAction.orbit (M ≃ₐ[F] M) P = ↑((P.restrict F).fiberOver M) := by
  ext Q
  rw [MulAction.mem_orbit_iff, Finset.mem_coe, Place.mem_fiberOver]
  constructor
  · rintro ⟨g, rfl⟩
    exact Place.restrict_ofAlgAut_smul g P
  · intro h
    exact Place.exists_algEquiv_smul_eq_of_restrict_eq P Q h

omit [Algebra F L] [Algebra L M] [IsScalarTower F L M] [Algebra K L] [IsScalarTower K L M] in

private theorem image_val_orbit {G X : Type*} [Group G] [MulAction G X] (H : Subgroup G) (a : X)
    (x : MulAction.orbit G a) :
    Subtype.val '' MulAction.orbit H x = MulAction.orbit H (x : X) :=
  (Set.range_comp _ _).symm

end Action

section Compositum

variable {F F₁ F₂ E M : Type*} [Field F] [Field F₁] [Field F₂] [Field E] [Field M]
    [Algebra F E] [Algebra F M] [Algebra F₁ E] [Algebra F₂ E] [Algebra F₁ M] [Algebra F₂ M]
    [Algebra E M] [IsScalarTower F E M] [IsScalarTower F₁ E M] [IsScalarTower F₂ E M]

private theorem forall_apply_algebraMap_eq_of_adjoin_eq_top
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ E) ∪ Set.range (algebraMap F₂ E)) = ⊤)
    (g : M ≃ₐ[F] M) (h₁ : ∀ x : F₁, g (algebraMap F₁ M x) = algebraMap F₁ M x)
    (h₂ : ∀ x : F₂, g (algebraMap F₂ M x) = algebraMap F₂ M x) (z : E) :
    g (algebraMap E M z) = algebraMap E M z := by
  let φ : E →ₐ[F] M := (g : M →ₐ[F] M).comp (IsScalarTower.toAlgHom F E M)
  let ψ : E →ₐ[F] M := IsScalarTower.toAlgHom F E M
  have htop : AlgHom.equalizer φ ψ = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine Algebra.adjoin_le ?_
    rintro x (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · show g (algebraMap E M (algebraMap F₁ E y)) = algebraMap E M (algebraMap F₁ E y)
      rw [← IsScalarTower.algebraMap_apply]
      exact h₁ y
    · show g (algebraMap E M (algebraMap F₂ E y)) = algebraMap E M (algebraMap F₂ E y)
      rw [← IsScalarTower.algebraMap_apply]
      exact h₂ y
  have hz : z ∈ AlgHom.equalizer φ ψ := htop ▸ Algebra.mem_top
  exact hz

end Compositum

end GaloisFramework

section Bifibre

open AlgebraicCurve Pointwise

attribute [local instance] galAction

private theorem mem_smul_valuationSubring_iff {K F : Type*} [Field K] [Field F] [Algebra K F]
    (g : SemilinearAut K F) (O : ValuationSubring F) (x : F) :
    x ∈ g • O ↔ g⁻¹ • x ∈ O := by
  constructor
  · intro hx
    have h := ValuationSubring.smul_mem_pointwise_smul g⁻¹ x (g • O) hx
    rwa [inv_smul_smul] at h
  · intro hx
    have h := ValuationSubring.smul_mem_pointwise_smul g (g⁻¹ • x) O hx
    rwa [smul_inv_smul] at h

open scoped Classical in

private theorem bifiber_defect {K F F₁ F₂ E : Type*} (M : Type*) [Field K] [Field F] [Field F₁]
    [Field F₂] [Field E] [Field M] [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K E]
    [Algebra K M] [Algebra F F₁] [Algebra F F₂] [Algebra F E] [Algebra F M] [Algebra F₁ E]
    [Algebra F₂ E] [Algebra F₁ M] [Algebra F₂ M] [Algebra E M] [IsScalarTower K F F₁]
    [IsScalarTower K F F₂] [IsScalarTower K F E] [IsScalarTower K F M] [IsScalarTower K F₁ E]
    [IsScalarTower K F₂ E] [IsScalarTower K F₁ M] [IsScalarTower K F₂ M] [IsScalarTower K E M]
    [IsScalarTower F F₁ M] [IsScalarTower F F₂ M] [IsScalarTower F E M] [IsScalarTower F₁ E M]
    [IsScalarTower F₂ E M] [FiniteDimensional F F₁] [FiniteDimensional F F₂]
    [FiniteDimensional F E] [FiniteDimensional F₁ E] [FiniteDimensional F₂ E]
    [FiniteDimensional F M] [IsGalois F M]
    [Algebra F₂ F₁] [IsScalarTower F F₂ F₁] [IsScalarTower K F₂ F₁] [Algebra.IsIntegral F₂ F₁]
    (hθ : Function.Surjective (algebraMap F₂ F₁))
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ E) ∪ Set.range (algebraMap F₂ E)) = ⊤)
    (hLD2 : Module.finrank F E + Module.finrank F F₁ = Module.finrank F F₁ * Module.finrank F F₂)
    (hn : Module.finrank F F₂ ≠ 2)
    (v : Place K F) (w₁ : Place K F₁) (w₂ : Place K F₂) (hw₁ : w₁.restrict F = v)
    (hw₂ : w₂.restrict F = v)
    (T : Finset (Place K E)) (hT : ∀ W, W ∈ T ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂) :
    ∑ W ∈ T, W.ramificationIndex F * W.inertiaDeg F
        + (if w₁.restrict F₂ = w₂ then w₁.ramificationIndex F * w₁.inertiaDeg F else 0) =
      (w₁.ramificationIndex F * w₁.inertiaDeg F) * (w₂.ramificationIndex F * w₂.inertiaDeg F) := by
  classical

  haveI : FiniteDimensional F₁ M := Module.Finite.of_restrictScalars_finite F F₁ M
  haveI : FiniteDimensional F₂ M := Module.Finite.of_restrictScalars_finite F F₂ M
  haveI : FiniteDimensional E M := Module.Finite.of_restrictScalars_finite F E M
  haveI : IsGalois F₁ M := IsGalois.tower_top_of_isGalois F F₁ M
  haveI : IsGalois F₂ M := IsGalois.tower_top_of_isGalois F F₂ M
  haveI : IsGalois E M := IsGalois.tower_top_of_isGalois F E M

  have hθinj : Function.Injective (IsScalarTower.toAlgHom F F₂ F₁) := (algebraMap F₂ F₁).injective
  let θe : F₂ ≃ₐ[F] F₁ := AlgEquiv.ofBijective (IsScalarTower.toAlgHom F F₂ F₁) ⟨hθinj, hθ⟩
  let s : M ≃ₐ[F] M := θe.liftNormal M
  have hcomm : ∀ y : F₂, s (algebraMap F₂ M y) = algebraMap F₁ M (algebraMap F₂ F₁ y) :=
    fun y => AlgEquiv.liftNormal_commutes θe M y
  have hs_inv : ∀ z : M, (s⁻¹ : M ≃ₐ[F] M) (s z) = z := fun z => s.symm_apply_apply z
  have hs_inv' : ∀ z : M, s ((s⁻¹ : M ≃ₐ[F] M) z) = z := fun z => s.apply_symm_apply z

  have hconjₛ : ∀ h : M ≃ₐ[F] M,
      h ∈ (resHom F M F₁).range ↔ s⁻¹ * h * s ∈ (resHom F M F₂).range := by
    intro h
    rw [mem_range_resHom_iff, mem_range_resHom_iff]
    constructor
    · intro hfix y
      show (s⁻¹ : M ≃ₐ[F] M) (h (s (algebraMap F₂ M y))) = algebraMap F₂ M y
      rw [hcomm y, hfix (algebraMap F₂ F₁ y), ← hcomm y, hs_inv]
    · intro hfix x
      obtain ⟨y, rfl⟩ := hθ x
      rw [show algebraMap F₁ M (algebraMap F₂ F₁ y) = s (algebraMap F₂ M y) from (hcomm y).symm]
      have h2 : h (s (algebraMap F₂ M y)) = s ((s⁻¹ * h * s) (algebraMap F₂ M y)) := by
        show h (s _) = s ((s⁻¹ : M ≃ₐ[F] M) (h (s _)))
        rw [hs_inv']
      rw [h2, hfix y]

  have hle : (resHom F M F₁).range ⊓ (resHom F M F₂).range ≤ (resHom F M E).range :=
    fun g hg => mem_range_resHom_iff.mpr (forall_apply_algebraMap_eq_of_adjoin_eq_top hgen g
      (mem_range_resHom_iff.mp hg.1) (mem_range_resHom_iff.mp hg.2))
  have hge : (resHom F M E).range ≤ (resHom F M F₁).range ⊓ (resHom F M F₂).range := by
    intro g hg
    rw [Subgroup.mem_inf, mem_range_resHom_iff, mem_range_resHom_iff]
    refine ⟨fun x => ?_, fun x => ?_⟩
    · rw [IsScalarTower.algebraMap_apply F₁ E M x]
      exact mem_range_resHom_iff.mp hg _
    · rw [IsScalarTower.algebraMap_apply F₂ E M x]
      exact mem_range_resHom_iff.mp hg _
  have hHE : (resHom F M F₁).range ⊓ (resHom F M F₂).range = (resHom F M E).range :=
    le_antisymm hle hge
  have hidxₛ : ((resHom F M F₁).range ⊓ (resHom F M F₂).range).index + (resHom F M F₁).range.index
      = (resHom F M F₁).range.index * (resHom F M F₂).range.index := by
    rw [hHE, index_range_resHom, index_range_resHom, index_range_resHom]
    exact hLD2
  have hnₛ : (resHom F M F₂).range.index ≠ 2 := by
    rw [index_range_resHom]; exact hn
  obtain ⟨hcover, hdisj⟩ :=
    cover_disjoint_of_index (resHom F M F₁).range (resHom F M F₂).range s hconjₛ hidxₛ hnₛ

  obtain ⟨P₁, hP₁⟩ := Place.exists_restrict_eq (M := M) w₁
  obtain ⟨P₂, hP₂⟩ := Place.exists_restrict_eq (M := M) w₂
  have hP₁F : P₁.restrict F = v := by rw [← restrict_restrict (E := F₁) P₁, hP₁, hw₁]
  have hP₂F : P₂.restrict F = v := by rw [← restrict_restrict (E := F₂) P₂, hP₂, hw₂]
  have hP₂P₁ : P₂.restrict F = P₁.restrict F := by rw [hP₁F, hP₂F]
  have hA : (v.fiberOver M).card * (P₁.ramificationIndex F * P₁.inertiaDeg F) =
      Module.finrank F M :=
    Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg v P₁ hP₁F
  have hA₁ : (w₁.ramificationIndex F * w₁.inertiaDeg F) * Module.finrank F₁ M =
      (w₁.fiberOver M).card * (P₁.ramificationIndex F * P₁.inertiaDeg F) := by
    have hTC := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg w₁ P₁ hP₁
    have he := ramificationIndex_eq_mul_restrict (F := F) (E := F₁) P₁
    have hf := inertiaDeg_eq_mul_restrict (F := F) (E := F₁) P₁
    rw [hP₁] at he hf
    rw [← hTC, he, hf]; ring
  have hA₂ : (w₂.ramificationIndex F * w₂.inertiaDeg F) * Module.finrank F₂ M =
      (w₂.fiberOver M).card * (P₁.ramificationIndex F * P₁.inertiaDeg F) := by
    have hTC := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg w₂ P₂ hP₂
    have he := ramificationIndex_eq_mul_restrict (F := F) (E := F₂) P₂
    have hf := inertiaDeg_eq_mul_restrict (F := F) (E := F₂) P₂
    rw [hP₂] at he hf
    rw [← Place.ramificationIndex_eq_of_restrict_eq P₁ P₂ hP₂P₁,
      ← Place.inertiaDeg_eq_of_restrict_eq P₁ P₂ hP₂P₁, ← hTC, he, hf]; ring
  have hEpt : ∀ W ∈ T, (W.ramificationIndex F * W.inertiaDeg F) * Module.finrank E M =
      (W.fiberOver M).card * (P₁.ramificationIndex F * P₁.inertiaDeg F) := by
    intro W hW
    obtain ⟨hW₁, -⟩ := (hT W).mp hW
    obtain ⟨P, hP⟩ := Place.exists_restrict_eq (M := M) W
    have hTC := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg W P hP
    have he := ramificationIndex_eq_mul_restrict (F := F) (E := E) P
    have hf := inertiaDeg_eq_mul_restrict (F := F) (E := E) P
    rw [hP] at he hf
    have hPF : P.restrict F = P₁.restrict F := by
      rw [← restrict_restrict (E := F₁) P, ← restrict_restrict (F := F₁) (E := E) P, hP, hW₁,
        hw₁, hP₁F]
    rw [← Place.ramificationIndex_eq_of_restrict_eq P₁ P hPF,
      ← Place.inertiaDeg_eq_of_restrict_eq P₁ P hPF, ← hTC, he, hf]; ring
  have hbi : w₁.fiberOver M ∩ w₂.fiberOver M = T.biUnion fun W => W.fiberOver M := by
    ext P
    simp only [Finset.mem_inter, Place.mem_fiberOver, Finset.mem_biUnion, hT]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨P.restrict E, ⟨(restrict_restrict P).trans h₁, (restrict_restrict P).trans h₂⟩, rfl⟩
    · rintro ⟨W, ⟨h₁, h₂⟩, rfl⟩
      exact ⟨(restrict_restrict P).symm.trans h₁, (restrict_restrict P).symm.trans h₂⟩
  have hdisjf : (↑T : Set (Place K E)).PairwiseDisjoint fun W => W.fiberOver M := by
    intro W _ W' _ hne
    change Disjoint (W.fiberOver M) (W'.fiberOver M)
    exact Finset.disjoint_left.mpr fun P h h' =>
      hne (((Place.mem_fiberOver W).mp h).symm.trans ((Place.mem_fiberOver W').mp h'))
  have hEsum : (∑ W ∈ T, W.ramificationIndex F * W.inertiaDeg F) * Module.finrank E M =
      (w₁.fiberOver M ∩ w₂.fiberOver M).card * (P₁.ramificationIndex F * P₁.inertiaDeg F) := by
    rw [hbi, Finset.card_biUnion hdisjf, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl hEpt

  have hx₂ : P₂ ∈ MulAction.orbit (M ≃ₐ[F] M) P₁ := by
    rw [orbit_gal_eq, Finset.mem_coe, Place.mem_fiberOver]
    exact hP₂P₁
  obtain ⟨x₁, hx₁⟩ : ∃ x : MulAction.orbit (M ≃ₐ[F] M) P₁, (x : Place K M) = P₁ :=
    ⟨⟨P₁, MulAction.mem_orbit_self P₁⟩, rfl⟩
  obtain ⟨x₂, hx₂'⟩ : ∃ x : MulAction.orbit (M ≃ₐ[F] M) P₁, (x : Place K M) = P₂ :=
    ⟨⟨P₂, hx₂⟩, rfl⟩
  have hO := ncard_orbit_inter_orbit_defect (X := MulAction.orbit (M ≃ₐ[F] M) P₁)
    (resHom F M F₁).range (resHom F M F₂).range s hconjₛ hcover hdisj x₁ x₂
  have cX : Nat.card (MulAction.orbit (M ≃ₐ[F] M) P₁) = (v.fiberOver M).card := by
    rw [Nat.card_coe_set_eq, orbit_gal_eq, hP₁F, Set.ncard_coe_finset]
  have c₁ : (MulAction.orbit (resHom F M F₁).range x₁).ncard = (w₁.fiberOver M).card := by
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, image_val_orbit, hx₁,
      orbit_range_resHom_eq, hP₁, Set.ncard_coe_finset]
  have c₂ : (MulAction.orbit (resHom F M F₂).range x₂).ncard = (w₂.fiberOver M).card := by
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, image_val_orbit, hx₂',
      orbit_range_resHom_eq, hP₂, Set.ncard_coe_finset]
  have c₁₂ : (MulAction.orbit (resHom F M F₁).range x₁ ∩
      MulAction.orbit (resHom F M F₂).range x₂).ncard
      = (w₁.fiberOver M ∩ w₂.fiberOver M).card := by
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective,
      Set.image_inter Subtype.val_injective, image_val_orbit, image_val_orbit, hx₁, hx₂',
      orbit_range_resHom_eq, orbit_range_resHom_eq, hP₁, hP₂, ← Finset.coe_inter,
      Set.ncard_coe_finset]

  have hdict : ((s⁻¹ • P₁ : Place K M)).restrict F₂ = (P₁.restrict F₁).restrict F₂ := by
    apply Place.ext
    rw [Place.restrict_toValuationSubring, Place.restrict_toValuationSubring,
      Place.restrict_toValuationSubring]
    have hsmul : (s⁻¹ • P₁ : Place K M).toValuationSubring
        = SemilinearAut.ofAlgAut ((s⁻¹ : M ≃ₐ[F] M).restrictScalars K) • P₁.toValuationSubring :=
      rfl
    rw [hsmul]
    ext y
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap, ValuationSubring.mem_comap,
      mem_smul_valuationSubring_iff]
    have hg : (SemilinearAut.ofAlgAut ((s⁻¹ : M ≃ₐ[F] M).restrictScalars K))⁻¹
        • (algebraMap F₂ M y) = s (algebraMap F₂ M y) := by
      rw [← map_inv]
      rfl
    rw [hg, hcomm y]
  have hmatch : (x₂ ∈ MulAction.orbit (resHom F M F₂).range (s⁻¹ • x₁)) ↔
      w₁.restrict F₂ = w₂ := by
    have hval : ((s⁻¹ • x₁ : MulAction.orbit (M ≃ₐ[F] M) P₁) : Place K M) = s⁻¹ • P₁ := by
      have h1 : ((s⁻¹ • x₁ : MulAction.orbit (M ≃ₐ[F] M) P₁) : Place K M)
          = s⁻¹ • (x₁ : Place K M) := rfl
      rw [h1, hx₁]
    constructor
    · rintro ⟨g, hg⟩
      have hg' : (g : M ≃ₐ[F] M) • (s⁻¹ • P₁ : Place K M) = P₂ := by
        have := congrArg Subtype.val hg
        rwa [show ((g • (s⁻¹ • x₁) : MulAction.orbit (M ≃ₐ[F] M) P₁) : Place K M)
          = (g : M ≃ₐ[F] M) • ((s⁻¹ • x₁ : MulAction.orbit (M ≃ₐ[F] M) P₁) : Place K M) from rfl,
          hval, hx₂'] at this
      have hmem : P₂ ∈ MulAction.orbit (resHom F M F₂).range (s⁻¹ • P₁ : Place K M) := ⟨g, hg'⟩
      rw [orbit_range_resHom_eq, Finset.mem_coe, Place.mem_fiberOver, hP₂, hdict, hP₁] at hmem
      exact hmem.symm
    · intro hm
      have hmem : P₂ ∈ MulAction.orbit (resHom F M F₂).range (s⁻¹ • P₁ : Place K M) := by
        rw [orbit_range_resHom_eq, Finset.mem_coe, Place.mem_fiberOver, hP₂, hdict, hP₁]
        exact hm.symm
      obtain ⟨g, hg⟩ := hmem
      refine ⟨g, ?_⟩
      apply Subtype.ext
      rw [show ((g • (s⁻¹ • x₁) : MulAction.orbit (M ≃ₐ[F] M) P₁) : Place K M)
        = (g : M ≃ₐ[F] M) • ((s⁻¹ • x₁ : MulAction.orbit (M ≃ₐ[F] M) P₁) : Place K M) from rfl,
        hval, hx₂']
      exact hg

  rw [hHE, index_range_resHom, index_range_resHom, index_range_resHom, cX, c₁, c₂, c₁₂] at hO

  have hn₁ := Module.finrank_mul_finrank F F₁ M
  have hn₂ := Module.finrank_mul_finrank F F₂ M
  have hnE := Module.finrank_mul_finrank F E M
  have hposA : 0 < (v.fiberOver M).card :=
    Finset.card_pos.mpr ⟨P₁, by rw [Place.mem_fiberOver]; exact hP₁F⟩
  have hpos1 : 0 < Module.finrank F F₁ := Module.finrank_pos
  have hpos2 : 0 < Module.finrank F F₂ := Module.finrank_pos
  have hposE : 0 < Module.finrank F E := Module.finrank_pos
  have hposM₁ : 0 < Module.finrank F₁ M := Module.finrank_pos
  have hposM₂ : 0 < Module.finrank F₂ M := Module.finrank_pos
  have hposME : 0 < Module.finrank E M := Module.finrank_pos
  by_cases hm : w₁.restrict F₂ = w₂
  · rw [if_pos (hmatch.mpr hm)] at hO
    rw [if_pos hm]

    have hsq : Module.finrank F M * Module.finrank F M
        = ((v.fiberOver M).card * (P₁.ramificationIndex F * P₁.inertiaDeg F))
          * (Module.finrank F E * Module.finrank E M) := by
      rw [hA, hnE]
    have key : (w₁.fiberOver M ∩ w₂.fiberOver M).card * (Module.finrank F₁ M * Module.finrank F₂ M)
        + (w₁.fiberOver M).card * (Module.finrank E M * Module.finrank F₂ M)
        = (w₁.fiberOver M).card * (w₂.fiberOver M).card
          * ((P₁.ramificationIndex F * P₁.inertiaDeg F) * Module.finrank E M) := by
      have hposmul : 0 < Module.finrank F F₁ * Module.finrank F F₂ * Module.finrank F E
          * (v.fiberOver M).card :=
        Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hpos1 hpos2) hposE) hposA
      refine Nat.eq_of_mul_eq_mul_right hposmul ?_
      calc ((w₁.fiberOver M ∩ w₂.fiberOver M).card
              * (Module.finrank F₁ M * Module.finrank F₂ M)
            + (w₁.fiberOver M).card * (Module.finrank E M * Module.finrank F₂ M))
            * (Module.finrank F F₁ * Module.finrank F F₂ * Module.finrank F E
              * (v.fiberOver M).card)
          = (Module.finrank F F₁ * Module.finrank F₁ M)
              * (Module.finrank F F₂ * Module.finrank F₂ M) * Module.finrank F E
              * ((w₁.fiberOver M ∩ w₂.fiberOver M).card * (v.fiberOver M).card)
            + (Module.finrank F F₂ * Module.finrank F₂ M)
              * (Module.finrank F E * Module.finrank E M) * Module.finrank F F₁
              * ((w₁.fiberOver M).card * (v.fiberOver M).card) := by ring
        _ = Module.finrank F M * Module.finrank F M * Module.finrank F E
              * ((w₁.fiberOver M ∩ w₂.fiberOver M).card * (v.fiberOver M).card)
            + Module.finrank F M * Module.finrank F M * Module.finrank F F₁
              * ((w₁.fiberOver M).card * (v.fiberOver M).card) := by
              rw [hn₁, hn₂, hnE]
        _ = Module.finrank F M * Module.finrank F M
              * (Module.finrank F E
                  * ((w₁.fiberOver M ∩ w₂.fiberOver M).card * (v.fiberOver M).card)
                + Module.finrank F F₁
                  * ((w₁.fiberOver M).card * (v.fiberOver M).card)) := by ring
        _ = Module.finrank F M * Module.finrank F M
              * (Module.finrank F F₁ * Module.finrank F F₂
                  * ((w₁.fiberOver M).card * (w₂.fiberOver M).card)) := by rw [hO]
        _ = ((w₁.fiberOver M).card * (w₂.fiberOver M).card
              * ((P₁.ramificationIndex F * P₁.inertiaDeg F) * Module.finrank E M))
            * (Module.finrank F F₁ * Module.finrank F F₂ * Module.finrank F E
              * (v.fiberOver M).card) := by rw [hsq]; ring

    have hposμ : 0 < Module.finrank E M * (Module.finrank F₁ M * (Module.finrank F₂ M
        * (v.fiberOver M).card)) :=
      Nat.mul_pos hposME (Nat.mul_pos hposM₁ (Nat.mul_pos hposM₂ hposA))
    refine Nat.eq_of_mul_eq_mul_right hposμ ?_
    calc (∑ W ∈ T, W.ramificationIndex F * W.inertiaDeg F
            + w₁.ramificationIndex F * w₁.inertiaDeg F)
          * (Module.finrank E M * (Module.finrank F₁ M * (Module.finrank F₂ M
            * (v.fiberOver M).card)))
        = ((∑ W ∈ T, W.ramificationIndex F * W.inertiaDeg F) * Module.finrank E M)
            * (Module.finrank F₁ M * Module.finrank F₂ M) * (v.fiberOver M).card
          + ((w₁.ramificationIndex F * w₁.inertiaDeg F) * Module.finrank F₁ M)
            * (Module.finrank E M * Module.finrank F₂ M) * (v.fiberOver M).card := by ring
      _ = ((w₁.fiberOver M ∩ w₂.fiberOver M).card
            * (P₁.ramificationIndex F * P₁.inertiaDeg F))
            * (Module.finrank F₁ M * Module.finrank F₂ M) * (v.fiberOver M).card
          + ((w₁.fiberOver M).card * (P₁.ramificationIndex F * P₁.inertiaDeg F))
            * (Module.finrank E M * Module.finrank F₂ M) * (v.fiberOver M).card := by
            rw [hEsum, hA₁]
      _ = ((w₁.fiberOver M ∩ w₂.fiberOver M).card
              * (Module.finrank F₁ M * Module.finrank F₂ M)
            + (w₁.fiberOver M).card * (Module.finrank E M * Module.finrank F₂ M))
            * ((P₁.ramificationIndex F * P₁.inertiaDeg F) * (v.fiberOver M).card) := by ring
      _ = ((w₁.fiberOver M).card * (w₂.fiberOver M).card
            * ((P₁.ramificationIndex F * P₁.inertiaDeg F) * Module.finrank E M))
            * ((P₁.ramificationIndex F * P₁.inertiaDeg F) * (v.fiberOver M).card) := by
            rw [key]
      _ = ((w₁.fiberOver M).card * (P₁.ramificationIndex F * P₁.inertiaDeg F))
            * ((w₂.fiberOver M).card * (P₁.ramificationIndex F * P₁.inertiaDeg F))
            * (Module.finrank E M * (v.fiberOver M).card) := by ring
      _ = ((w₁.ramificationIndex F * w₁.inertiaDeg F) * Module.finrank F₁ M)
            * ((w₂.ramificationIndex F * w₂.inertiaDeg F) * Module.finrank F₂ M)
            * (Module.finrank E M * (v.fiberOver M).card) := by rw [hA₁, hA₂]
      _ = ((w₁.ramificationIndex F * w₁.inertiaDeg F)
            * (w₂.ramificationIndex F * w₂.inertiaDeg F))
          * (Module.finrank E M * (Module.finrank F₁ M * (Module.finrank F₂ M
            * (v.fiberOver M).card))) := by ring
  · rw [if_neg (fun hc => hm (hmatch.mp hc)), add_zero] at hO
    rw [if_neg hm, add_zero]
    have hposμ : 0 < Module.finrank E M * (Module.finrank F₁ M * (Module.finrank F₂ M
        * (v.fiberOver M).card)) :=
      Nat.mul_pos hposME (Nat.mul_pos hposM₁ (Nat.mul_pos hposM₂ hposA))
    refine Nat.eq_of_mul_eq_mul_right hposμ ?_
    have hsq : Module.finrank F M * Module.finrank F M
        = ((v.fiberOver M).card * (P₁.ramificationIndex F * P₁.inertiaDeg F))
          * (Module.finrank F E * Module.finrank E M) := by
      rw [hA, hnE]
    have key : (w₁.fiberOver M ∩ w₂.fiberOver M).card
        * (Module.finrank F₁ M * Module.finrank F₂ M)
        = (w₁.fiberOver M).card * (w₂.fiberOver M).card
          * ((P₁.ramificationIndex F * P₁.inertiaDeg F) * Module.finrank E M) := by
      have hposmul : 0 < Module.finrank F F₁ * Module.finrank F F₂ * Module.finrank F E
          * (v.fiberOver M).card :=
        Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hpos1 hpos2) hposE) hposA
      refine Nat.eq_of_mul_eq_mul_right hposmul ?_
      calc (w₁.fiberOver M ∩ w₂.fiberOver M).card
              * (Module.finrank F₁ M * Module.finrank F₂ M)
            * (Module.finrank F F₁ * Module.finrank F F₂ * Module.finrank F E
              * (v.fiberOver M).card)
          = (Module.finrank F F₁ * Module.finrank F₁ M)
              * (Module.finrank F F₂ * Module.finrank F₂ M) * Module.finrank F E
              * ((w₁.fiberOver M ∩ w₂.fiberOver M).card * (v.fiberOver M).card) := by ring
        _ = Module.finrank F M * Module.finrank F M
              * (Module.finrank F E
                  * ((w₁.fiberOver M ∩ w₂.fiberOver M).card * (v.fiberOver M).card)) := by
              rw [hn₁, hn₂]; ring
        _ = Module.finrank F M * Module.finrank F M
              * (Module.finrank F F₁ * Module.finrank F F₂
                  * ((w₁.fiberOver M).card * (w₂.fiberOver M).card)) := by rw [hO]
        _ = ((w₁.fiberOver M).card * (w₂.fiberOver M).card
              * ((P₁.ramificationIndex F * P₁.inertiaDeg F) * Module.finrank E M))
            * (Module.finrank F F₁ * Module.finrank F F₂ * Module.finrank F E
              * (v.fiberOver M).card) := by rw [hsq]; ring
    calc (∑ W ∈ T, W.ramificationIndex F * W.inertiaDeg F)
          * (Module.finrank E M * (Module.finrank F₁ M * (Module.finrank F₂ M
            * (v.fiberOver M).card)))
        = ((∑ W ∈ T, W.ramificationIndex F * W.inertiaDeg F) * Module.finrank E M)
            * (Module.finrank F₁ M * Module.finrank F₂ M) * (v.fiberOver M).card := by ring
      _ = ((w₁.fiberOver M ∩ w₂.fiberOver M).card
            * (P₁.ramificationIndex F * P₁.inertiaDeg F))
            * (Module.finrank F₁ M * Module.finrank F₂ M) * (v.fiberOver M).card := by
            rw [hEsum]
      _ = ((w₁.fiberOver M ∩ w₂.fiberOver M).card
              * (Module.finrank F₁ M * Module.finrank F₂ M))
            * ((P₁.ramificationIndex F * P₁.inertiaDeg F) * (v.fiberOver M).card) := by ring
      _ = ((w₁.fiberOver M).card * (w₂.fiberOver M).card
            * ((P₁.ramificationIndex F * P₁.inertiaDeg F) * Module.finrank E M))
            * ((P₁.ramificationIndex F * P₁.inertiaDeg F) * (v.fiberOver M).card) := by
            rw [key]
      _ = ((w₁.fiberOver M).card * (P₁.ramificationIndex F * P₁.inertiaDeg F))
            * ((w₂.fiberOver M).card * (P₁.ramificationIndex F * P₁.inertiaDeg F))
            * (Module.finrank E M * (v.fiberOver M).card) := by ring
      _ = ((w₁.ramificationIndex F * w₁.inertiaDeg F) * Module.finrank F₁ M)
            * ((w₂.ramificationIndex F * w₂.inertiaDeg F) * Module.finrank F₂ M)
            * (Module.finrank E M * (v.fiberOver M).card) := by rw [hA₁, hA₂]
      _ = ((w₁.ramificationIndex F * w₁.inertiaDeg F)
            * (w₂.ramificationIndex F * w₂.inertiaDeg F))
          * (Module.finrank E M * (Module.finrank F₁ M * (Module.finrank F₂ M
            * (v.fiberOver M).card))) := by ring

end Bifibre

end WK2ADev2

open AlgebraicCurve in
open scoped Classical in

theorem solution {K F F₁ F₂ E : Type*} (M : Type*) [Field K] [Field F] [Field F₁] [Field F₂] [Field E] [Field M] [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K E] [Algebra K M] [Algebra F F₁] [Algebra F F₂] [Algebra F E] [Algebra F M] [Algebra F₁ E] [Algebra F₂ E] [Algebra F₁ M] [Algebra F₂ M] [Algebra E M] [IsScalarTower K F F₁] [IsScalarTower K F F₂] [IsScalarTower K F E] [IsScalarTower K F M] [IsScalarTower K F₁ E] [IsScalarTower K F₂ E] [IsScalarTower K F₁ M] [IsScalarTower K F₂ M] [IsScalarTower K E M] [IsScalarTower F F₁ M] [IsScalarTower F F₂ M] [IsScalarTower F E M] [IsScalarTower F₁ E M] [IsScalarTower F₂ E M] [FiniteDimensional F F₁] [FiniteDimensional F F₂] [FiniteDimensional F E] [FiniteDimensional F₁ E] [FiniteDimensional F₂ E] [FiniteDimensional F M] [IsGalois F M] [Algebra F₂ F₁] [IsScalarTower F F₂ F₁] [IsScalarTower K F₂ F₁] [Algebra.IsIntegral F₂ F₁] (hθ : Function.Surjective (algebraMap F₂ F₁)) (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ E) ∪ Set.range (algebraMap F₂ E)) = ⊤) (hLD2 : Module.finrank F E + Module.finrank F F₁ = Module.finrank F F₁ * Module.finrank F F₂) (hn : Module.finrank F F₂ ≠ 2) (v : Place K F) (w₁ : Place K F₁) (w₂ : Place K F₂) (hw₁ : w₁.restrict F = v) (hw₂ : w₂.restrict F = v) (T : Finset (Place K E)) (hT : ∀ W, W ∈ T ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂) : ∑ W ∈ T, W.ramificationIndex F * W.inertiaDeg F + (if w₁.restrict F₂ = w₂ then w₁.ramificationIndex F * w₁.inertiaDeg F else 0) = (w₁.ramificationIndex F * w₁.inertiaDeg F) * (w₂.ramificationIndex F * w₂.inertiaDeg F) :=
  WK2ADev2.bifiber_defect M hθ hgen hLD2 hn v w₁ w₂ hw₁ hw₂ T hT

end S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber_defect
end P2MW
export P2MW.S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber_defect (solution)
