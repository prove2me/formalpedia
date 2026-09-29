-- Prove2me | solution 1 for AlgebraicCurve.genusFF_eq_and_nonempty_pic0_addEquiv_of_algebraMap_eq_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/600d59f5-25bf-547a-8e20-2119987a47d7

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_genusFF_eq_and_nonempty_pic0_addEquiv_of_algebraMap_eq_comp

set_option autoImplicit false

open AlgebraicCurve

section ConstantRenaming

variable {k K F : Type*} [Field k] [Field K] [Field F] [Algebra K F] [Algebra k F]

private theorem trAlgebraMap (e : k ≃+* K) (he : algebraMap k F = (algebraMap K F).comp e.toRingHom) (a : k) :
    algebraMap k F a = algebraMap K F (e a) :=
  DFunLike.congr_fun he a

private theorem trFinrankEq (e : k ≃+* K) {M M' : Type*} [AddCommGroup M] [Module k M] [AddCommGroup M']
    [Module K M'] (j : M ≃+ M') (hj : ∀ (c : k) (m : M), j (c • m) = e c • j m) :
    Module.finrank k M = Module.finrank K M' := by
  have h__af := congrArg Cardinal.toNat (lift_rank_eq_of_equiv_equiv (⇑e) j e.bijective hj)
  simp at h__af
  exact h__af

private def trPlaceEquiv (e : k ≃+* K) (he : algebraMap k F = (algebraMap K F).comp e.toRingHom) :
    Place k F ≃ Place K F where
  toFun v :=
    { toValuationSubring := v.toValuationSubring
      algebraMap_mem' := fun b => by
        have h : algebraMap K F b = algebraMap k F (e.symm b) := by
          rw [trAlgebraMap e he, RingEquiv.apply_symm_apply]
        rw [h]
        exact v.algebraMap_mem' _
      ne_top' := v.ne_top'
      isPrincipalIdealRing' := v.isPrincipalIdealRing' }
  invFun w :=
    { toValuationSubring := w.toValuationSubring
      algebraMap_mem' := fun a => by
        rw [trAlgebraMap e he]
        exact w.algebraMap_mem' _
      ne_top' := w.ne_top'
      isPrincipalIdealRing' := w.isPrincipalIdealRing' }
  left_inv _ := Place.ext rfl
  right_inv _ := Place.ext rfl

private theorem trPlaceEquiv_ord (e : k ≃+* K) (he : algebraMap k F = (algebraMap K F).comp e.toRingHom)
    (v : Place k F) (f : F) : (trPlaceEquiv e he v).ord f = v.ord f := rfl

private theorem trPlaceEquiv_symm_ord (e : k ≃+* K) (he : algebraMap k F = (algebraMap K F).comp e.toRingHom)
    (w : Place K F) (f : F) : ((trPlaceEquiv e he).symm w).ord f = w.ord f := rfl

private theorem trPlaceEquiv_symm_adicValuation (e : k ≃+* K)
    (he : algebraMap k F = (algebraMap K F).comp e.toRingHom) (w : Place K F) (f : F) :
    ((trPlaceEquiv e he).symm w).adicValuation f = w.adicValuation f := rfl

private theorem trPlaceEquiv_adicValuation (e : k ≃+* K)
    (he : algebraMap k F = (algebraMap K F).comp e.toRingHom) (v : Place k F) (f : F) :
    (trPlaceEquiv e he v).adicValuation f = v.adicValuation f := rfl

private theorem trResidueFinrank (e : k ≃+* K) (he : algebraMap k F = (algebraMap K F).comp e.toRingHom)
    (V : ValuationSubring F) [ak : Algebra k V] [aK : Algebra K V]
    (hk : ∀ a : k, (algebraMap k V a : F) = algebraMap k F a)
    (hK : ∀ b : K, (algebraMap K V b : F) = algebraMap K F b) :
    Module.finrank k (IsLocalRing.ResidueField V) = Module.finrank K (IsLocalRing.ResidueField V) := by
  refine trFinrankEq e (AddEquiv.refl _) fun c m => ?_
  rw [AddEquiv.refl_apply, AddEquiv.refl_apply, Algebra.smul_def, Algebra.smul_def]
  congr 1
  show IsLocalRing.residue V (algebraMap k V c) = IsLocalRing.residue V (algebraMap K V (e c))
  congr 1
  exact Subtype.ext ((hk c).trans ((trAlgebraMap e he c).trans (hK (e c)).symm))

private theorem trPlaceEquiv_deg (e : k ≃+* K) (he : algebraMap k F = (algebraMap K F).comp e.toRingHom)
    (v : Place k F) : (trPlaceEquiv e he v).deg = v.deg := by
  unfold Place.deg
  exact (trResidueFinrank e he v.toValuationSubring
    (aK := inferInstanceAs (Algebra K (trPlaceEquiv e he v).toValuationSubring))
    (fun _ => rfl) (fun _ => rfl)).symm

private def trDivisorEquiv (e : k ≃+* K) (he : algebraMap k F = (algebraMap K F).comp e.toRingHom) :
    Divisor k F ≃+ Divisor K F :=
  Finsupp.domCongr (trPlaceEquiv e he)

private theorem trDivisorEquiv_degree (e : k ≃+* K) (he : algebraMap k F = (algebraMap K F).comp e.toRingHom)
    (D : Divisor k F) : Divisor.degree (trDivisorEquiv e he D) = Divisor.degree D := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D E hD hE => simp only [map_add, hD, hE]
  | single v n => simp [trDivisorEquiv, trPlaceEquiv_deg e he]

private theorem trDivisorEquiv_isPrincipal (e : k ≃+* K) (he : algebraMap k F = (algebraMap K F).comp e.toRingHom)
    (D : Divisor k F) : (trDivisorEquiv e he D).IsPrincipal ↔ D.IsPrincipal := by
  constructor
  · rintro ⟨f, hf, h⟩
    refine ⟨f, hf, fun v => ?_⟩
    have hv := h (trPlaceEquiv e he v)
    simpa [trDivisorEquiv, trPlaceEquiv_ord e he] using hv
  · rintro ⟨f, hf, h⟩
    refine ⟨f, hf, fun w => ?_⟩
    have hw := h ((trPlaceEquiv e he).symm w)
    simpa [trDivisorEquiv, trPlaceEquiv_symm_ord e he] using hw

private theorem trDivisorEquiv_map_degZero (e : k ≃+* K)
    (he : algebraMap k F = (algebraMap K F).comp e.toRingHom) :
    (Divisor.degZero (K := k) (F := F)).map (trDivisorEquiv e he : Divisor k F →+ Divisor K F)
      = Divisor.degZero (K := K) (F := F) := by
  ext E
  constructor
  · rintro ⟨D, hD, rfl⟩
    show Divisor.degree (trDivisorEquiv e he D) = 0
    rw [trDivisorEquiv_degree]
    exact hD
  · intro hE
    refine ⟨(trDivisorEquiv e he).symm E, ?_, (trDivisorEquiv e he).apply_symm_apply E⟩
    show Divisor.degree ((trDivisorEquiv e he).symm E) = 0
    rw [← trDivisorEquiv_degree e he, (trDivisorEquiv e he).apply_symm_apply]
    exact hE

private noncomputable def trDegZeroEquiv (e : k ≃+* K) (he : algebraMap k F = (algebraMap K F).comp e.toRingHom) :
    Divisor.degZero (K := k) (F := F) ≃+ Divisor.degZero (K := K) (F := F) :=
  ((trDivisorEquiv e he).addSubgroupMap (Divisor.degZero (K := k) (F := F))).trans
    (AddEquiv.addSubgroupCongr (trDivisorEquiv_map_degZero e he))

private theorem trDegZeroEquiv_coe (e : k ≃+* K) (he : algebraMap k F = (algebraMap K F).comp e.toRingHom)
    (D : Divisor.degZero (K := k) (F := F)) :
    ((trDegZeroEquiv e he D : Divisor.degZero (K := K) (F := F)) : Divisor K F) = trDivisorEquiv e he D := rfl

private theorem trDegZeroEquiv_map_principal (e : k ≃+* K)
    (he : algebraMap k F = (algebraMap K F).comp e.toRingHom) :
    ((Divisor.principal (K := k) (F := F)).addSubgroupOf (Divisor.degZero (K := k) (F := F))).map
        (trDegZeroEquiv e he : Divisor.degZero (K := k) (F := F) →+ Divisor.degZero (K := K) (F := F))
      = (Divisor.principal (K := K) (F := F)).addSubgroupOf (Divisor.degZero (K := K) (F := F)) := by
  ext x
  rw [AddSubgroup.mem_map, AddSubgroup.mem_addSubgroupOf]
  constructor
  · rintro ⟨D, hD, rfl⟩
    rw [AddSubgroup.mem_addSubgroupOf] at hD
    show (trDivisorEquiv e he D).IsPrincipal
    exact (trDivisorEquiv_isPrincipal e he D).mpr hD
  · intro hx
    obtain ⟨D, rfl⟩ := (trDegZeroEquiv e he).surjective x
    refine ⟨D, ?_, rfl⟩
    rw [AddSubgroup.mem_addSubgroupOf]
    exact (trDivisorEquiv_isPrincipal e he D).mp hx

private noncomputable def trPic0Equiv (e : k ≃+* K) (he : algebraMap k F = (algebraMap K F).comp e.toRingHom) :
    Pic0 k F ≃+ Pic0 K F :=
  QuotientAddGroup.congr _ _ (trDegZeroEquiv e he) (trDegZeroEquiv_map_principal e he)

private def trPiEquiv (e : k ≃+* K) (he : algebraMap k F = (algebraMap K F).comp e.toRingHom) :
    (Place k F → F) ≃ₐ[F] (Place K F → F) where
  toFun α := fun w => α ((trPlaceEquiv e he).symm w)
  invFun β := fun v => β (trPlaceEquiv e he v)
  left_inv α := funext fun v => by simp
  right_inv β := funext fun w => by simp
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

private theorem trPiEquiv_apply (e : k ≃+* K) (he : algebraMap k F = (algebraMap K F).comp e.toRingHom)
    (α : Place k F → F) (w : Place K F) : trPiEquiv e he α w = α ((trPlaceEquiv e he).symm w) := rfl

private theorem trPiEquiv_map_repartitions (e : k ≃+* K)
    (he : algebraMap k F = (algebraMap K F).comp e.toRingHom) :
    (repartitions k F).map (trPiEquiv e he).toAlgHom = repartitions K F := by
  unfold repartitions
  rw [AlgHom.map_adjoin]
  congr 1
  ext β
  constructor
  · rintro ⟨α, hα, rfl⟩
    have hα' : {v : Place k F | ¬v.adicValuation (α v) ≤ 1}.Finite := hα
    have hfin := hα'.preimage (trPlaceEquiv e he).symm.injective.injOn
    show {w : Place K F | ¬w.adicValuation (trPiEquiv e he α w) ≤ 1}.Finite
    simp only [trPiEquiv_apply, ← trPlaceEquiv_symm_adicValuation e he]
    exact hfin
  · intro hβ
    refine ⟨fun v => β (trPlaceEquiv e he v), ?_, ?_⟩
    · have hβ' : {w : Place K F | ¬w.adicValuation (β w) ≤ 1}.Finite := hβ
      have hfin := hβ'.preimage (trPlaceEquiv e he).injective.injOn
      show {v : Place k F | ¬v.adicValuation (β (trPlaceEquiv e he v)) ≤ 1}.Finite
      simp only [← trPlaceEquiv_adicValuation e he]
      exact hfin
    · funext w
      show β (trPlaceEquiv e he ((trPlaceEquiv e he).symm w)) = β w
      rw [Equiv.apply_symm_apply]

private noncomputable def trRepEquiv (e : k ≃+* K) (he : algebraMap k F = (algebraMap K F).comp e.toRingHom) :
    ↥(repartitions k F) ≃ₐ[F] ↥(repartitions K F) :=
  ((repartitions k F).equivMapOfInjective (trPiEquiv e he).toAlgHom (trPiEquiv e he).injective).trans
    (Subalgebra.equivOfEq _ _ (trPiEquiv_map_repartitions e he))

private theorem trRepEquiv_coe (e : k ≃+* K) (he : algebraMap k F = (algebraMap K F).comp e.toRingHom)
    (α : ↥(repartitions k F)) (w : Place K F) :
    ((trRepEquiv e he α : ↥(repartitions K F)) : Place K F → F) w
      = (α : Place k F → F) ((trPlaceEquiv e he).symm w) := rfl

private theorem trRepEquiv_mem_repartitionsOf (e : k ≃+* K)
    (he : algebraMap k F = (algebraMap K F).comp e.toRingHom) (α : ↥(repartitions k F)) :
    trRepEquiv e he α ∈ repartitionsOf (0 : Divisor K F) ↔ α ∈ repartitionsOf (0 : Divisor k F) := by
  show (∀ w : Place K F, w.adicValuation (((trRepEquiv e he α : ↥(repartitions K F)) : Place K F → F) w)
      ≤ WithZero.exp ((0 : Divisor K F) w)) ↔
    ∀ v : Place k F, v.adicValuation ((α : Place k F → F) v) ≤ WithZero.exp ((0 : Divisor k F) v)
  simp only [trRepEquiv_coe, Finsupp.coe_zero, Pi.zero_apply]
  constructor
  · intro h v
    have hv := h (trPlaceEquiv e he v)
    rw [trPlaceEquiv_adicValuation e he, Equiv.symm_apply_apply] at hv
    exact hv
  · intro h w
    have hw := h ((trPlaceEquiv e he).symm w)
    rw [trPlaceEquiv_symm_adicValuation e he] at hw
    exact hw

private theorem trRepEquiv_mem_principalRepartitions (e : k ≃+* K)
    (he : algebraMap k F = (algebraMap K F).comp e.toRingHom) (α : ↥(repartitions k F)) :
    trRepEquiv e he α ∈ principalRepartitions K F ↔ α ∈ principalRepartitions k F := by
  rw [mem_principalRepartitions_iff, mem_principalRepartitions_iff]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, funext fun v => ?_⟩
    have hv := congrFun hf (trPlaceEquiv e he v)
    rw [trRepEquiv_coe, Equiv.symm_apply_apply] at hv
    exact hv
  · rintro ⟨f, hf⟩
    refine ⟨f, funext fun w => ?_⟩
    rw [trRepEquiv_coe, hf]

private theorem trRepEquiv_mem_sup (e : k ≃+* K) (he : algebraMap k F = (algebraMap K F).comp e.toRingHom)
    (α : ↥(repartitions k F)) :
    trRepEquiv e he α ∈ repartitionsOf (0 : Divisor K F) ⊔ principalRepartitions K F ↔
      α ∈ repartitionsOf (0 : Divisor k F) ⊔ principalRepartitions k F := by
  rw [Submodule.mem_sup, Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, hyz⟩
    refine ⟨(trRepEquiv e he).symm y, ?_, (trRepEquiv e he).symm z, ?_, ?_⟩
    · rw [← trRepEquiv_mem_repartitionsOf e he, AlgEquiv.apply_symm_apply]
      exact hy
    · rw [← trRepEquiv_mem_principalRepartitions e he, AlgEquiv.apply_symm_apply]
      exact hz
    · apply (trRepEquiv e he).injective
      rw [map_add, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
      exact hyz
  · rintro ⟨y, hy, z, hz, rfl⟩
    refine ⟨trRepEquiv e he y, (trRepEquiv_mem_repartitionsOf e he y).mpr hy, trRepEquiv e he z,
      (trRepEquiv_mem_principalRepartitions e he z).mpr hz, ?_⟩
    rw [map_add]

private theorem trRepEquiv_map_sup (e : k ≃+* K) (he : algebraMap k F = (algebraMap K F).comp e.toRingHom) :
    ((repartitionsOf (0 : Divisor k F) ⊔ principalRepartitions k F).restrictScalars ℤ).map
        ((trRepEquiv e he).toAddEquiv.toIntLinearEquiv : ↥(repartitions k F) →ₗ[ℤ] ↥(repartitions K F))
      = (repartitionsOf (0 : Divisor K F) ⊔ principalRepartitions K F).restrictScalars ℤ := by
  ext β
  rw [Submodule.mem_map, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨α, hα, rfl⟩
    rw [Submodule.restrictScalars_mem] at hα
    exact (trRepEquiv_mem_sup e he α).mpr hα
  · intro hβ
    obtain ⟨α, rfl⟩ := (trRepEquiv e he).surjective β
    refine ⟨α, ?_, rfl⟩
    rw [Submodule.restrictScalars_mem]
    exact (trRepEquiv_mem_sup e he α).mp hβ

private noncomputable def trH1Equiv (e : k ≃+* K) (he : algebraMap k F = (algebraMap K F).comp e.toRingHom) :
    H1 (0 : Divisor k F) ≃+ H1 (0 : Divisor K F) :=
  ((Submodule.Quotient.restrictScalarsEquiv ℤ
      (repartitionsOf (0 : Divisor k F) ⊔ principalRepartitions k F)).symm.toAddEquiv.trans
    (Submodule.Quotient.equiv _ _ (trRepEquiv e he).toAddEquiv.toIntLinearEquiv
      (trRepEquiv_map_sup e he)).toAddEquiv).trans
    (Submodule.Quotient.restrictScalarsEquiv ℤ
      (repartitionsOf (0 : Divisor K F) ⊔ principalRepartitions K F)).toAddEquiv

private theorem trH1Equiv_mk (e : k ≃+* K) (he : algebraMap k F = (algebraMap K F).comp e.toRingHom)
    (α : ↥(repartitions k F)) :
    trH1Equiv e he (Submodule.Quotient.mk α) = Submodule.Quotient.mk (trRepEquiv e he α) := rfl

private theorem trRepEquiv_smul (e : k ≃+* K) (he : algebraMap k F = (algebraMap K F).comp e.toRingHom)
    (c : k) (α : ↥(repartitions k F)) : trRepEquiv e he (c • α) = e c • trRepEquiv e he α := by
  apply Subtype.ext
  funext w
  change c • (α : Place k F → F) ((trPlaceEquiv e he).symm w) = e c • (α : Place k F → F) ((trPlaceEquiv e he).symm w)
  rw [Algebra.smul_def, Algebra.smul_def, trAlgebraMap e he]

private theorem trGenusFF (e : k ≃+* K) (he : algebraMap k F = (algebraMap K F).comp e.toRingHom) :
    genusFF k F = genusFF K F := by
  unfold genusFF
  refine trFinrankEq e (trH1Equiv e he) fun c x => ?_
  obtain ⟨α, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, trH1Equiv_mk, trH1Equiv_mk, trRepEquiv_smul, Submodule.Quotient.mk_smul]

end ConstantRenaming

theorem solution
    (k K F : Type*) [Field k] [Field K] [Field F] [Algebra K F] [Algebra k F]
    (e : k ≃+* K) (he : algebraMap k F = (algebraMap K F).comp e.toRingHom) :
    genusFF k F = genusFF K F ∧ Nonempty (Pic0 k F ≃+ Pic0 K F) :=
  ⟨trGenusFF e he, ⟨trPic0Equiv e he⟩⟩

#print axioms solution

end S_AlgebraicCurve_genusFF_eq_and_nonempty_pic0_addEquiv_of_algebraMap_eq_comp
end P2MW
export P2MW.S_AlgebraicCurve_genusFF_eq_and_nonempty_pic0_addEquiv_of_algebraMap_eq_comp (solution)
