-- Prove2me | solution 1 for AlgebraicCurve.SemilinearAut.existsUnique_baseAut_eq_smul_algebraMap_eq_of_constantFieldExtension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/4b31ef46-fd65-53eb-8c3b-acafef45524b

import Mathlib
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemilinearAut_existsUnique_baseAut_eq_smul_algebraMap_eq_of_constantFieldExtension

open AlgebraicCurve

set_option autoImplicit false

open scoped TensorProduct

namespace G5

section Twist

variable {K F K' : Type*} [Field K] [Field F] [Field K'] [Algebra K F] [Algebra K K']
  (g : SemilinearAut K F) (τ : K' ≃+* K')
  (hτ : ∀ a : K, τ (algebraMap K K' a) = algebraMap K K' (SemilinearAut.baseAut g a))

noncomputable def twistHom (σ : K' ≃+* K') (φ : F ≃+* F)
    (h : ∀ a : K, ∀ c : K', ∀ y : F, σ (a • c) ⊗ₜ[K] φ y = σ c ⊗ₜ[K] φ (a • y)) :
    K' ⊗[K] F →+ K' ⊗[K] F :=
  TensorProduct.liftAddHom
    { toFun := fun c => ((TensorProduct.mk K K' F (σ c)).toAddMonoidHom).comp φ.toAddMonoidHom
      map_zero' := by ext y; simp
      map_add' := fun c c' => by ext y; simp }
    (fun a c y => by simpa using h a c y)

theorem twistHom_tmul (σ : K' ≃+* K') (φ : F ≃+* F)
    (h : ∀ a : K, ∀ c : K', ∀ y : F, σ (a • c) ⊗ₜ[K] φ y = σ c ⊗ₜ[K] φ (a • y)) (c : K') (y : F) :
    twistHom σ φ h (c ⊗ₜ y) = σ c ⊗ₜ φ y := by
  simp [twistHom, TensorProduct.liftAddHom_tmul]

include hτ in
theorem twist_compat : ∀ a : K, ∀ c : K', ∀ y : F,
    τ (a • c) ⊗ₜ[K] (SemilinearAut.toRingAut g) y = τ c ⊗ₜ[K] (SemilinearAut.toRingAut g) (a • y) := by
  intro a c y
  rw [Algebra.smul_def, map_mul, hτ, Algebra.smul_def, map_mul, SemilinearAut.commutes,
    ← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.smul_tmul]

include hτ in
theorem twist_compat_symm : ∀ a : K, ∀ c : K', ∀ y : F,
    τ.symm (a • c) ⊗ₜ[K] (SemilinearAut.toRingAut g).symm y =
      τ.symm c ⊗ₜ[K] (SemilinearAut.toRingAut g).symm (a • y) := by
  intro a c y

  have hτ' : ∀ b : K, τ.symm (algebraMap K K' b) = algebraMap K K' ((SemilinearAut.baseAut g).symm b) := by
    intro b
    apply τ.injective
    rw [RingEquiv.apply_symm_apply, hτ, RingEquiv.apply_symm_apply]
  have hg' : ∀ b : K, (SemilinearAut.toRingAut g).symm (algebraMap K F b) =
      algebraMap K F ((SemilinearAut.baseAut g).symm b) := by
    intro b
    apply (SemilinearAut.toRingAut g).injective
    rw [RingEquiv.apply_symm_apply, SemilinearAut.commutes, RingEquiv.apply_symm_apply]
  rw [Algebra.smul_def, map_mul, hτ', Algebra.smul_def, map_mul, hg', ← Algebra.smul_def, ← Algebra.smul_def,
    TensorProduct.smul_tmul]

noncomputable def twist : K' ⊗[K] F ≃+* K' ⊗[K] F where
  toFun := twistHom τ (SemilinearAut.toRingAut g) (twist_compat g τ hτ)
  invFun := twistHom τ.symm (SemilinearAut.toRingAut g).symm (twist_compat_symm g τ hτ)
  left_inv x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c y => simp [twistHom_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  right_inv x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c y => simp [twistHom_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  map_add' x y := map_add _ x y
  map_mul' x y := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c z =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul c' z' => simp [twistHom_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      | add y y' hy hy' => simp only [mul_add, map_add, hy, hy']
    | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']

theorem twist_tmul (c : K') (y : F) : twist g τ hτ (c ⊗ₜ y) = τ c ⊗ₜ (g • y) := by
  show twistHom τ (SemilinearAut.toRingAut g) (twist_compat g τ hτ) (c ⊗ₜ y) = _
  rw [twistHom_tmul, SemilinearAut.smul_def]

end Twist

end G5

open AlgebraicCurve G5 in
theorem solution
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (g : SemilinearAut K F) (τ : K' ≃+* K')
    (hτ : ∀ a : K, τ (algebraMap K K' a) = algebraMap K K' (SemilinearAut.baseAut g a)) :
    ∃! g' : SemilinearAut K' F',
      (∀ c : K', SemilinearAut.baseAut g' c = τ c) ∧
      ∀ y : F, g' • algebraMap F F' y = algebraMap F F' (g • y) := by
  classical

  let μ : K' ⊗[K] F →ₐ[K'] F' :=
    Algebra.TensorProduct.lift (Algebra.ofId K' F') (IsScalarTower.toAlgHom K F F')
      (fun _ _ => Commute.all _ _)
  have hμ_tmul : ∀ (a : K') (y : F), μ (a ⊗ₜ y) = algebraMap K' F' a * algebraMap F F' y :=
    fun a y => by simp [μ]
  have hμ : Function.Injective μ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    let bF := Module.Free.chooseBasis K F
    let B := Algebra.TensorProduct.basis K' bF
    have hli : LinearIndependent K' (fun i => algebraMap F F' (bF i)) :=
      AlgebraicCurve.linearIndependent_of_constantFieldExtension K F K' F' hfg hfg' hgen
        bF.linearIndependent
    have hcomp : (μ.toLinearMap : K' ⊗[K] F → F') ∘ (B : _ → K' ⊗[K] F) =
        fun i => algebraMap F F' (bF i) := by
      funext i
      simp [B, Algebra.TensorProduct.basis_apply, hμ_tmul]
    have hz' : Finsupp.linearCombination K' (fun i => algebraMap F F' (bF i)) (B.repr z) = 0 := by
      rw [← hcomp, ← Finsupp.apply_linearCombination, B.linearCombination_repr]
      exact hz
    have hrepr : B.repr z = 0 := linearIndependent_iff.mp hli _ hz'
    simpa using hrepr
  set S : Subalgebra K' F' := μ.range with hS
  let e : (K' ⊗[K] F) ≃ₐ[K'] S := AlgEquiv.ofInjective μ hμ
  have he : ∀ z, ((e z : S) : F') = μ z := fun z => AlgEquiv.ofInjective_apply μ hμ z
  haveI : FaithfulSMul S F' := (faithfulSMul_iff_algebraMap_injective S F').mpr Subtype.val_injective
  have hFS : ∀ y : F, algebraMap F F' y ∈ S := fun y =>
    ⟨1 ⊗ₜ y, show μ (1 ⊗ₜ y) = _ by rw [hμ_tmul, map_one, one_mul]⟩
  have hadj : Algebra.adjoin K' (Set.range (algebraMap F F')) ≤ S :=
    Algebra.adjoin_le (by rintro _ ⟨y, rfl⟩; exact hFS y)
  haveI : IsFractionRing S F' := by
    refine IsFractionRing.of_field S F' fun z => ?_
    have hz : z ∈ IntermediateField.adjoin K' (Set.range (algebraMap F F')) := by
      rw [hgen]; exact IntermediateField.mem_top
    obtain ⟨r, hr, s, hs, hrs⟩ := (IntermediateField.mem_adjoin_iff_div (F := K')).mp hz
    exact ⟨⟨r, hadj hr⟩, ⟨s, hadj hs⟩, hrs⟩

  let θ : K' ⊗[K] F ≃+* K' ⊗[K] F := twist g τ hτ
  let ΦS : S ≃+* S := (e.symm.toRingEquiv.trans θ).trans e.toRingEquiv
  have hΦS : ∀ z, ΦS (e z) = e (θ z) := fun z => by simp [ΦS]
  let Φ : F' ≃+* F' := IsFractionRing.ringEquivOfRingEquiv ΦS
  have hΦ : ∀ s : S, Φ (s : F') = ((ΦS s : S) : F') := fun s =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap ΦS s
  have hΦμ : ∀ z, Φ (μ z) = μ (θ z) := fun z => by
    rw [← he, hΦ, hΦS, he]
  have hΦK : ∀ a : K', Φ (algebraMap K' F' a) = algebraMap K' F' (τ a) := fun a => by
    have h1 : algebraMap K' F' a = μ (a ⊗ₜ 1) := by rw [hμ_tmul, map_one, mul_one]
    rw [h1, hΦμ]
    show μ (twist g τ hτ (a ⊗ₜ 1)) = _
    rw [twist_tmul, show g • (1 : F) = 1 from smul_one g, hμ_tmul, map_one, mul_one]
  have hΦF : ∀ y : F, Φ (algebraMap F F' y) = algebraMap F F' (g • y) := fun y => by
    have h1 : algebraMap F F' y = μ (1 ⊗ₜ y) := by rw [hμ_tmul, map_one, one_mul]
    rw [h1, hΦμ]
    show μ (twist g τ hτ (1 ⊗ₜ y)) = _
    rw [twist_tmul, map_one, hμ_tmul, map_one, one_mul]

  refine ⟨⟨(Φ, τ), SemilinearAut.mem_iff.mpr fun a => hΦK a⟩, ⟨fun c => rfl, fun y => ?_⟩, ?_⟩
  · rw [SemilinearAut.smul_def]; exact hΦF y

  · rintro g₂ ⟨hb₂, hF₂⟩
    have hb₂' : SemilinearAut.baseAut g₂ = τ := RingEquiv.ext hb₂

    apply Subtype.ext
    apply Prod.ext _ hb₂'
    apply RingEquiv.ext
    intro z
    let E : IntermediateField K' F' :=
      { carrier := {z | SemilinearAut.toRingAut g₂ z = Φ z}
        mul_mem' := fun {x y} hx hy => by
          simp only [Set.mem_setOf_eq] at hx hy ⊢
          rw [map_mul, map_mul, hx, hy]
        one_mem' := by simp only [Set.mem_setOf_eq, map_one]
        add_mem' := fun {x y} hx hy => by
          simp only [Set.mem_setOf_eq] at hx hy ⊢
          rw [map_add, map_add, hx, hy]
        zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]
        algebraMap_mem' := fun c => by
          simp only [Set.mem_setOf_eq]
          rw [← SemilinearAut.smul_def, SemilinearAut.smul_algebraMap, hb₂, hΦK]
        inv_mem' := fun x hx => by
          simp only [Set.mem_setOf_eq] at hx ⊢
          rw [map_inv₀, map_inv₀, hx] }
    have hE : IntermediateField.adjoin K' (Set.range (algebraMap F F')) ≤ E := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨y, rfl⟩
      show SemilinearAut.toRingAut g₂ (algebraMap F F' y) = Φ (algebraMap F F' y)
      rw [← SemilinearAut.smul_def, hF₂, hΦF]
    have hz : z ∈ E := hE (by rw [hgen]; exact IntermediateField.mem_top)
    exact hz

end S_AlgebraicCurve_SemilinearAut_existsUnique_baseAut_eq_smul_algebraMap_eq_of_constantFieldExtension
end P2MW
export P2MW.S_AlgebraicCurve_SemilinearAut_existsUnique_baseAut_eq_smul_algebraMap_eq_of_constantFieldExtension (solution)
