-- Prove2me | solution 1 for AdicCompletion.exists_ringEquiv_quotient_map_adicCompletion_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/0f1230f7-150c-5ed4-ac74-9803ddfc479d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AdicCompletion_exists_ringEquiv_quotient_map_adicCompletion_quotient

set_option autoImplicit false

open IsLocalRing

namespace R1AF8AdicQuot

open AdicCompletion Submodule

variable {N : Type*} [CommRing N] (I 𝔭 : Ideal N)

abbrev Ibar : Ideal (N ⧸ 𝔭) := I.map (Ideal.Quotient.mk 𝔭)

lemma pow_le_comap (n : ℕ) :
    I ^ n ≤ ((Ibar I 𝔭) ^ n).comap (Ideal.Quotient.mk 𝔭) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]

noncomputable def lev (n : ℕ) : AdicCompletion I N →+* (N ⧸ 𝔭) ⧸ (Ibar I 𝔭) ^ n :=
  (Ideal.quotientMap ((Ibar I 𝔭) ^ n) (Ideal.Quotient.mk 𝔭) (pow_le_comap I 𝔭 n)).comp
    (AdicCompletion.evalₐ I n : AdicCompletion I N →ₐ[N] N ⧸ I ^ n).toRingHom

lemma lev_mk (n : ℕ) (s : AdicCauchySequence I N) :
    lev I 𝔭 n (AdicCompletion.mk I N s) =
      Ideal.Quotient.mk ((Ibar I 𝔭) ^ n) (Ideal.Quotient.mk 𝔭 (s n)) := by
  simp [lev, Ideal.quotientMap_mk]

lemma lev_of (n : ℕ) (x : N) :
    lev I 𝔭 n (AdicCompletion.of I N x) =
      Ideal.Quotient.mk ((Ibar I 𝔭) ^ n) (Ideal.Quotient.mk 𝔭 x) := by
  simp [lev, Ideal.quotientMap_mk]

lemma lev_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (Ibar I 𝔭) hle).comp (lev I 𝔭 n) = lev I 𝔭 m := by
  ext x
  induction x using AdicCompletion.induction_on with
  | h s =>
    simp only [RingHom.comp_apply, lev_mk, Ideal.Quotient.factor_mk]
    have h := AdicCompletion.Ideal.mk_eq_mk I hle s

    have h' := congrArg (Ideal.quotientMap ((Ibar I 𝔭) ^ m) (Ideal.Quotient.mk 𝔭)
      (pow_le_comap I 𝔭 m)) h
    simpa [Ideal.quotientMap_mk] using h'

noncomputable def phi : AdicCompletion I N →+* AdicCompletion (Ibar I 𝔭) (N ⧸ 𝔭) :=
  AdicCompletion.liftRingHom (Ibar I 𝔭) (lev I 𝔭) (fun hle => lev_compat I 𝔭 hle)

@[scoped simp] lemma evalₐ_phi (n : ℕ) (x : AdicCompletion I N) :
    AdicCompletion.evalₐ (Ibar I 𝔭) n (phi I 𝔭 x) = lev I 𝔭 n x := by
  simp [phi]

lemma phi_of (x : N) :
    phi I 𝔭 (AdicCompletion.of I N x) =
      AdicCompletion.of (Ibar I 𝔭) (N ⧸ 𝔭) (Ideal.Quotient.mk 𝔭 x) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_phi, lev_of, AdicCompletion.evalₐ_of]

lemma phi_algebraMap (x : N) :
    phi I 𝔭 (algebraMap N (AdicCompletion I N) x) =
      AdicCompletion.of (Ibar I 𝔭) (N ⧸ 𝔭) (Ideal.Quotient.mk 𝔭 x) := by
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, phi_of]

lemma map_le_ker :
    𝔭.map (algebraMap N (AdicCompletion I N)) ≤ RingHom.ker (phi I 𝔭) := by
  rw [Ideal.map_le_iff_le_comap]
  intro p hp
  rw [Ideal.mem_comap, RingHom.mem_ker, phi_algebraMap,
    (Ideal.Quotient.eq_zero_iff_mem).mpr hp, _root_.map_zero]

noncomputable def phiBar :
    (AdicCompletion I N ⧸ 𝔭.map (algebraMap N (AdicCompletion I N))) →+*
      AdicCompletion (Ibar I 𝔭) (N ⧸ 𝔭) :=
  Ideal.Quotient.lift _ (phi I 𝔭) (fun _ ha => map_le_ker I 𝔭 ha)

@[scoped simp] lemma phiBar_mk (a : AdicCompletion I N) :
    phiBar I 𝔭 (Ideal.Quotient.mk _ a) = phi I 𝔭 a := by
  simp [phiBar]

lemma smul_top_eq (n : ℕ) :
    (I ^ n • ⊤ : Submodule N (N ⧸ 𝔭)) =
      ((Ibar I 𝔭) ^ n • ⊤ : Ideal (N ⧸ 𝔭)).restrictScalars N := by
  rw [Ideal.smul_top_eq_map, Ideal.Quotient.algebraMap_eq, Ideal.map_pow, Ideal.smul_eq_mul,
    Ideal.mul_top]

noncomputable def eps (n : ℕ) :
    ((N ⧸ 𝔭) ⧸ ((Ibar I 𝔭) ^ n • ⊤ : Ideal (N ⧸ 𝔭))) ≃ₗ[N]
      ((N ⧸ 𝔭) ⧸ (I ^ n • ⊤ : Submodule N (N ⧸ 𝔭))) :=
  (Submodule.Quotient.restrictScalarsEquiv N ((Ibar I 𝔭) ^ n • ⊤ : Ideal (N ⧸ 𝔭))).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (smul_top_eq I 𝔭 n).symm

@[scoped simp] lemma eps_mk (n : ℕ) (b : N ⧸ 𝔭) :
    eps I 𝔭 n (Submodule.Quotient.mk b) = Submodule.Quotient.mk b := by
  simp only [eps, LinearEquiv.trans_apply]
  rw [Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.quotEquivOfEq_mk]

@[scoped simp] lemma eps_symm_mk (n : ℕ) (b : N ⧸ 𝔭) :
    (eps I 𝔭 n).symm (Submodule.Quotient.mk b) = Submodule.Quotient.mk b := by
  rw [LinearEquiv.symm_apply_eq, eps_mk]

noncomputable def chiInv (y : AdicCompletion (Ibar I 𝔭) (N ⧸ 𝔭)) : AdicCompletion I (N ⧸ 𝔭) :=
  ⟨fun n => eps I 𝔭 n (y.val n), by
    intro m n hmn
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (y.val n)
    have hm : y.val m = Submodule.Quotient.mk b := by
      rw [← y.property hmn, ← hb]; rfl
    change AdicCompletion.transitionMap I (N ⧸ 𝔭) hmn (eps I 𝔭 n (y.val n)) = eps I 𝔭 m (y.val m)
    rw [← hb, hm, eps_mk, eps_mk]
    rfl⟩

noncomputable def chi (x : AdicCompletion I (N ⧸ 𝔭)) : AdicCompletion (Ibar I 𝔭) (N ⧸ 𝔭) :=
  ⟨fun n => (eps I 𝔭 n).symm (x.val n), by
    intro m n hmn
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
    have hm : x.val m = Submodule.Quotient.mk b := by
      rw [← x.property hmn, ← hb]; rfl
    change AdicCompletion.transitionMap (Ibar I 𝔭) (N ⧸ 𝔭) hmn ((eps I 𝔭 n).symm (x.val n)) =
      (eps I 𝔭 m).symm (x.val m)
    rw [← hb, hm, eps_symm_mk, eps_symm_mk]
    rfl⟩

@[scoped simp] lemma chi_val (x : AdicCompletion I (N ⧸ 𝔭)) (n : ℕ) :
    (chi I 𝔭 x).val n = (eps I 𝔭 n).symm (x.val n) := rfl

@[scoped simp] lemma chiInv_val (y : AdicCompletion (Ibar I 𝔭) (N ⧸ 𝔭)) (n : ℕ) :
    (chiInv I 𝔭 y).val n = eps I 𝔭 n (y.val n) := rfl

lemma chi_chiInv (y : AdicCompletion (Ibar I 𝔭) (N ⧸ 𝔭)) : chi I 𝔭 (chiInv I 𝔭 y) = y := by
  refine AdicCompletion.ext fun n => ?_
  simp

lemma chiInv_chi (x : AdicCompletion I (N ⧸ 𝔭)) : chiInv I 𝔭 (chi I 𝔭 x) = x := by
  refine AdicCompletion.ext fun n => ?_
  simp

lemma chi_bijective : Function.Bijective (chi I 𝔭) :=
  ⟨Function.LeftInverse.injective (g := chiInv I 𝔭) (chiInv_chi I 𝔭),
   Function.RightInverse.surjective (g := chiInv I 𝔭) (chi_chiInv I 𝔭)⟩

lemma chi_smul_of_one (a : AdicCompletion I N) :
    chi I 𝔭 (a • AdicCompletion.of I (N ⧸ 𝔭) 1) = phi I 𝔭 a := by
  induction a using AdicCompletion.induction_on with
  | h s =>
    refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [evalₐ_phi, lev_mk]
    rw [← AdicCompletion.factor_eval_eq_evalₐ _ _ (le_of_eq (Ideal.mul_top _)),
      AdicCompletion.eval_apply, chi_val, AdicCompletion.smul_eval]
    have h1 : (AdicCompletion.mk I N s).val n =
        Ideal.Quotient.mk (I ^ n • ⊤ : Ideal N) (s n) := rfl
    have h2 : (AdicCompletion.of I (N ⧸ 𝔭) 1).val n =
        Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule N (N ⧸ 𝔭))) 1 := rfl
    have h3 : ((s n : N) • (1 : N ⧸ 𝔭)) = Ideal.Quotient.mk 𝔭 (s n) := by
      rw [Algebra.smul_def (s n : N) (1 : N ⧸ 𝔭), mul_one, Ideal.Quotient.algebraMap_eq]
    rw [h1, h2, AdicCompletion.mk_smul_mk, ← Submodule.Quotient.mk_smul, h3, eps_symm_mk]
    exact Ideal.Quotient.factor_mk (le_of_eq (Ideal.mul_top _)) _

variable [IsNoetherianRing N]

noncomputable def Psi :
    (AdicCompletion I N ⧸ 𝔭.map (algebraMap N (AdicCompletion I N))) ≃ₗ[AdicCompletion I N]
      AdicCompletion I (N ⧸ 𝔭) :=
  (Ideal.qoutMapEquivTensorQout (AdicCompletion I N) (I := 𝔭)) ≪≫ₗ
    AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I (N ⧸ 𝔭)

lemma Psi_symm_of_one :
    (Psi I 𝔭).symm (AdicCompletion.of I (N ⧸ 𝔭) 1) = 1 := by
  simp only [Psi, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_symm_of]

  change (TensorProduct.tensorQuotEquivQuotSMul (AdicCompletion I N) 𝔭 ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (by simp) ≪≫ₗ Submodule.Quotient.restrictScalarsEquiv N _)
      ((1 : AdicCompletion I N) ⊗ₜ[N] (1 : N ⧸ 𝔭)) = _
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, ← map_one (Ideal.Quotient.mk 𝔭),
    TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, one_smul, Submodule.quotEquivOfEq_mk,
    Submodule.Quotient.restrictScalarsEquiv_mk]
  exact map_one (Ideal.Quotient.mk (𝔭.map (algebraMap N (AdicCompletion I N))))

lemma Psi_mk (a : AdicCompletion I N) :
    Psi I 𝔭 (Ideal.Quotient.mk _ a) = a • AdicCompletion.of I (N ⧸ 𝔭) 1 := by
  have h : Ideal.Quotient.mk (𝔭.map (algebraMap N (AdicCompletion I N))) a =
      a • (1 : AdicCompletion I N ⧸ 𝔭.map (algebraMap N (AdicCompletion I N))) := by
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one]
  rw [h, map_smul, ← Psi_symm_of_one I 𝔭, LinearEquiv.apply_symm_apply]

lemma phiBar_eq_comp : ⇑(phiBar I 𝔭) = chi I 𝔭 ∘ Psi I 𝔭 := by
  funext q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp only [Function.comp_apply, phiBar_mk, Psi_mk, chi_smul_of_one]

lemma phiBar_bijective : Function.Bijective (phiBar I 𝔭) := by
  rw [phiBar_eq_comp]
  exact (chi_bijective I 𝔭).comp (Psi I 𝔭).bijective

theorem main :
    ∃ e : (AdicCompletion I N ⧸ 𝔭.map (algebraMap N (AdicCompletion I N))) ≃+*
        AdicCompletion (I.map (Ideal.Quotient.mk 𝔭)) (N ⧸ 𝔭),
      ∀ x : N, e (Ideal.Quotient.mk _ (algebraMap N (AdicCompletion I N) x)) =
        algebraMap (N ⧸ 𝔭) (AdicCompletion (I.map (Ideal.Quotient.mk 𝔭)) (N ⧸ 𝔭))
          (Ideal.Quotient.mk 𝔭 x) := by
  refine ⟨RingEquiv.ofBijective (phiBar I 𝔭) (phiBar_bijective I 𝔭), fun x => ?_⟩
  rw [RingEquiv.ofBijective_apply, phiBar_mk, phi_algebraMap, AdicCompletion.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply]

end R1AF8AdicQuot
p2m_reactivate "P2MW.S_AdicCompletion_exists_ringEquiv_quotient_map_adicCompletion_quotient.R1AF8AdicQuot"

theorem solution
    (N : Type*) [CommRing N] [IsNoetherianRing N] (I 𝔭 : Ideal N) :
    ∃ e : (AdicCompletion I N ⧸ 𝔭.map (algebraMap N (AdicCompletion I N))) ≃+*
        AdicCompletion (I.map (Ideal.Quotient.mk 𝔭)) (N ⧸ 𝔭),
      ∀ x : N, e (Ideal.Quotient.mk _ (algebraMap N (AdicCompletion I N) x)) =
        algebraMap (N ⧸ 𝔭) (AdicCompletion (I.map (Ideal.Quotient.mk 𝔭)) (N ⧸ 𝔭)) (Ideal.Quotient.mk 𝔭 x) :=
  R1AF8AdicQuot.main I 𝔭

end S_AdicCompletion_exists_ringEquiv_quotient_map_adicCompletion_quotient
end P2MW
export P2MW.S_AdicCompletion_exists_ringEquiv_quotient_map_adicCompletion_quotient (solution)
