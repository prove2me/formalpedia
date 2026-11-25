-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_FWCharP
-- name    : GroundTheory_PAdicHodge_FWCharP
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T11:42:24.796277+00:00
-- url     : https://prove2.me/theorems/5cfc1181-ecb1-4319-8143-76669e3bbb82
-- title:
--   FWChar P
-- statement:
--   Definitions and structural lemmas for FWChar P, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWCharP.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FWGlue
import Definitions.Def_GroundTheory_PAdicHodge_TiltEquiv
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_exists_mk_untilt_eq
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_untilt_eq_zero_iff
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_untilt_zero
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
section Congr
theorem algEquiv_apply_eq_of_mem_adjoin {F M : Type*} [Field F] [Field M] [Algebra F M]
    (τ : M ≃ₐ[F] M) {S : Set M} (hS : ∀ s ∈ S, τ s = s) {x : M}
    (hx : x ∈ IntermediateField.adjoin F S) : τ x = x := by
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx => exact hS x hx
  | algebraMap c => exact τ.commutes c
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]
theorem exists_finite_le_adjoin {F M : Type*} [Field F] [Field M] [Algebra F M]
    (W : IntermediateField F M) [FiniteDimensional F W] :
    ∃ S : Set M, S.Finite ∧ W ≤ IntermediateField.adjoin F S := by
  classical
  set B := Module.finBasis F W
  refine ⟨Set.range fun i => (B i : M), Set.finite_range _, fun x hx => ?_⟩
  have := congrArg (fun u : W => (u : M)) (B.sum_repr (⟨x, hx⟩ : W))
  simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at this
  rw [← this]
  exact sum_mem fun i _ => IntermediateField.smul_mem _
    (IntermediateField.subset_adjoin _ _ (Set.mem_range_self i))
variable {F F' : Type*} [Field F] [Field F']
def conjAlgEquiv {L M : Type*} [Field L] [Field M] [Algebra F L] [Algebra F' M] (e : F ≃+* F')
    (E : L ≃+* M) (hE : ∀ c, E (algebraMap F L c) = algebraMap F' M (e c)) (σ : L ≃ₐ[F] L) :
    M ≃ₐ[F'] M :=
  AlgEquiv.ofRingEquiv (f := E.symm.trans (σ.toRingEquiv.trans E)) fun c => by
    have h1 : E.symm (algebraMap F' M c) = algebraMap F L (e.symm c) := by
      rw [RingEquiv.symm_apply_eq, hE, RingEquiv.apply_symm_apply]
    simp only [RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv]
    rw [h1, AlgEquiv.commutes, hE, RingEquiv.apply_symm_apply]
theorem conjAlgEquiv_apply {L M : Type*} [Field L] [Field M] [Algebra F L] [Algebra F' M]
    (e : F ≃+* F') (E : L ≃+* M) (hE : ∀ c, E (algebraMap F L c) = algebraMap F' M (e c))
    (σ : L ≃ₐ[F] L) (x : M) : conjAlgEquiv e E hE σ x = E (σ (E.symm x)) :=
  rfl
theorem continuous_conjAlgEquiv {L M : Type*} [Field L] [Field M] [Algebra F L] [Algebra F' M]
    [Algebra.IsIntegral F L] (e : F ≃+* F') (E : L ≃+* M)
    (hE : ∀ c, E (algebraMap F L c) = algebraMap F' M (e c)) :
    Continuous (conjAlgEquiv e E hE) := by
  have hmul : ∀ σ τ : L ≃ₐ[F] L,
      conjAlgEquiv e E hE (σ * τ) = conjAlgEquiv e E hE σ * conjAlgEquiv e E hE τ := fun σ τ =>
    AlgEquiv.ext fun x => by simp [conjAlgEquiv_apply]
  let φ : (L ≃ₐ[F] L) →* (M ≃ₐ[F'] M) :=
    { toFun := conjAlgEquiv e E hE
      map_one' := AlgEquiv.ext fun x => by simp [conjAlgEquiv_apply]
      map_mul' := hmul }
  change Continuous φ
  apply continuous_of_continuousAt_one φ (continuousAt_def.mpr _)
  intro U hU
  rw [map_one, krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨W, hW, hsub⟩ := hU
  obtain ⟨S, hSfin, hWS⟩ := exists_finite_le_adjoin W
  rw [krullTopology_mem_nhds_one_iff]
  have : Finite (E.symm '' S) := (hSfin.image _).to_subtype
  have : FiniteDimensional F (IntermediateField.adjoin F (E.symm '' S)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨IntermediateField.adjoin F (E.symm '' S), this, fun σ hσ => hsub ?_⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  intro x hx
  refine algEquiv_apply_eq_of_mem_adjoin (φ σ) (fun s hs => ?_) (hWS hx)
  change E (σ (E.symm s)) = s
  rw [hσ _ (IntermediateField.subset_adjoin _ _ ⟨s, hs, rfl⟩), RingEquiv.apply_symm_apply]
def conjHomeomorph {L M : Type*} [Field L] [Field M] [Algebra F L] [Algebra F' M]
    [Algebra.IsIntegral F L] [Algebra.IsIntegral F' M] (e : F ≃+* F') (E : L ≃+* M)
    (hE : ∀ c, E (algebraMap F L c) = algebraMap F' M (e c)) : (L ≃ₐ[F] L) ≃ₜ* (M ≃ₐ[F'] M) :=
  have hE' : ∀ c, E.symm (algebraMap F' M c) = algebraMap F L (e.symm c) := fun c => by
    rw [RingEquiv.symm_apply_eq, hE, RingEquiv.apply_symm_apply]
  { toFun := conjAlgEquiv e E hE
    invFun := conjAlgEquiv e.symm E.symm hE'
    left_inv := fun σ => AlgEquiv.ext fun x => by
      rw [conjAlgEquiv_apply, conjAlgEquiv_apply, RingEquiv.symm_symm, RingEquiv.symm_apply_apply,
        RingEquiv.symm_apply_apply]
    right_inv := fun τ => AlgEquiv.ext fun x => by
      rw [conjAlgEquiv_apply, conjAlgEquiv_apply, RingEquiv.symm_symm, RingEquiv.apply_symm_apply,
        RingEquiv.apply_symm_apply]
    map_mul' := fun σ τ => AlgEquiv.ext fun x => by
      simp only [conjAlgEquiv_apply, AlgEquiv.mul_apply, RingEquiv.symm_apply_apply]
    continuous_toFun := continuous_conjAlgEquiv e E hE
    continuous_invFun := continuous_conjAlgEquiv e.symm E.symm hE' }
variable (F F') in

def absoluteGaloisGroupCongr (e : F ≃+* F') :
    Field.absoluteGaloisGroup F ≃ₜ* Field.absoluteGaloisGroup F' :=
  conjHomeomorph e (IsAlgClosure.equivOfEquiv (AlgebraicClosure F) (AlgebraicClosure F') e)
    (IsAlgClosure.equivOfEquiv_algebraMap _ _ e)
end Congr
section CharP
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [CharP K p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "𝒪♭" => PreTilt (normInteger K) p
variable (K p) in

def untiltRingHomOfCharP : 𝒪♭ →+* normInteger K where
  toFun x := PreTilt.untilt x
  map_one' := map_one _
  map_mul' := untilt_mul
  map_zero' := untilt_zero
  map_add' := untilt_add_of_natCast_eq_zero (CharP.cast_eq_zero K p)
theorem untiltRingHomOfCharP_bijective : Function.Bijective (untiltRingHomOfCharP K p) := by
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    exact untilt_eq_zero_iff.1 (congrArg Subtype.val hx)
  · intro a
    obtain ⟨x, hx⟩ := exists_mk_untilt_eq (p := p) a
    refine ⟨x, ?_⟩
    have hp : (p : normInteger K) = 0 := Subtype.ext (by simp)
    rw [Ideal.Quotient.eq, hp, Ideal.span_singleton_eq_bot.2 rfl, Ideal.mem_bot, sub_eq_zero] at hx
    exact hx
variable (K p) in

def tiltRingEquivOfCharP : K♭ ≃+* K :=
  IsFractionRing.ringEquivOfRingEquiv (A := 𝒪♭) (K := K♭) (B := normInteger K) (L := K)
    (RingEquiv.ofBijective _ untiltRingHomOfCharP_bijective)
end CharP
end GroundTheory.PAdicHodge


