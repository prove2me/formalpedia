-- Prove2me | solution 1 for AlgebraicCurve.cechH1ToH1_mk_eq_of_cechH1ToH1_pullbackAlong_mk_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/7266c2ef-0a42-5664-8366-f2694d07c5a8

import Mathlib
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_CechH1PushPull
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_restrictAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_cechH1ToH1_mk_eq_of_cechH1ToH1_pullbackAlong_mk_eq

set_option autoImplicit false

open AlgebraicCurve

namespace L1Aux

variable {K F F₁ : Type*} [Field K] [Field F] [Field F₁] [Algebra K F] [Algebra K F₁]

theorem adicValuation_le_one_iff_mem (v : Place K F) (f : F) :
    v.adicValuation f ≤ 1 ↔ f ∈ v.toValuationSubring := by
  constructor
  · intro h
    rcases (v.adicValuation_le_one_iff).mp h with rfl | h
    · exact zero_mem _
    · exact v.mem_toValuationSubring_of_ord_nonneg h
  · exact v.adicValuation_le_one_of_mem

theorem mem_restrictAlong_iff (φ : F →ₐ[K] F₁) (hφ : φ.toRingHom.IsIntegral) (w : Place K F₁) (f : F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring := Iff.rfl

theorem restrictAlong_id (hid : (AlgHom.id K F).toRingHom.IsIntegral) (v : Place K F) :
    v.restrictAlong (AlgHom.id K F) hid = v := by
  apply Place.ext
  ext f
  exact mem_restrictAlong_iff _ _ _ _

theorem restrictAlong_injective_of_surjective (φ : F →ₐ[K] F₁) (hφ : φ.toRingHom.IsIntegral)
    (hsurj : Function.Surjective φ) : Function.Injective (fun w : Place K F₁ => w.restrictAlong φ hφ) := by
  intro w w' h
  apply Place.ext
  ext y
  obtain ⟨x, rfl⟩ := hsurj y
  rw [← mem_restrictAlong_iff φ hφ w x, ← mem_restrictAlong_iff φ hφ w' x]
  exact congrArg (fun v : Place K F => x ∈ v.toValuationSubring) h |>.to_iff

end L1Aux

theorem solution
    {K : Type*} {F F₁ : Type*} [Field K] [Field F] [Algebra K F] [Field F₁] [Algebra K F₁]
    (θ : F →ₐ[K] F₁) (hθ : θ.toRingHom.IsIntegral) (hbij : Function.Bijective θ)
    {S₀ S₁ : Set (Place K F)} (hS : S₀ ∪ S₁ = Set.univ)
    (a b : ↥(lSpaceOn (S₀ ∩ S₁) (0 : Divisor K F)))
    (h : cechH1ToH1 (preimage_restrictAlong_union_eq_univ θ hθ hS) 0
        (cechH1.pullbackAlong θ hθ S₀ S₁ (Submodule.Quotient.mk a)) =
      cechH1ToH1 (preimage_restrictAlong_union_eq_univ θ hθ hS) 0
        (cechH1.pullbackAlong θ hθ S₀ S₁ (Submodule.Quotient.mk b))) :
    cechH1ToH1 hS 0 (Submodule.Quotient.mk a) = cechH1ToH1 hS 0 (Submodule.Quotient.mk b) := by
  classical

  let e : F ≃ₐ[K] F₁ := AlgEquiv.ofBijective θ hbij
  let θi : F₁ →ₐ[K] F := e.symm.toAlgHom
  have hθi_apply : ∀ y, θ (θi y) = y := fun y => e.apply_symm_apply y
  have hθi_apply' : ∀ x, θi (θ x) = x := fun x => e.symm_apply_apply x
  have hθi : θi.toRingHom.IsIntegral := RingHom.isIntegral_of_surjective _ e.symm.surjective
  let σ : Place K F → Place K F₁ := fun v => v.restrictAlong θi hθi
  have hid : θi.comp θ = AlgHom.id K F := by ext x; exact hθi_apply' x
  have hidint : (AlgHom.id K F).toRingHom.IsIntegral := RingHom.isIntegral_of_surjective _ Function.surjective_id
  have hcompint : (θi.comp θ).toRingHom.IsIntegral := by rw [hid]; exact hidint
  have hσ : ∀ v, (σ v).restrictAlong θ hθ = v := by
    intro v
    rw [AlgebraicCurve.Place.restrictAlong_restrictAlong θ θi hθ hθi hcompint v,
      Place.restrictAlong_congr hid hcompint hidint]
    exact L1Aux.restrictAlong_id _ v
  have hσinj : Function.Injective σ := L1Aux.restrictAlong_injective_of_surjective θi hθi e.symm.surjective

  have hmem : ∀ (v : Place K F) (y : F₁), θi y ∈ v.toValuationSubring ↔ y ∈ (σ v).toValuationSubring :=
    fun v y => (L1Aux.mem_restrictAlong_iff θi hθi v y).symm

  let Ψ : (Place K F₁ → F₁) →+* (Place K F → F) :=
    RingHom.pi fun v => θi.toRingHom.comp (Pi.evalRingHom (fun _ : Place K F₁ => F₁) (σ v))
  have hΨ_apply : ∀ α v, Ψ α v = θi (α (σ v)) := fun α v => rfl
  have hΨmem : ∀ α : Place K F₁ → F₁, α ∈ repartitions K F₁ → Ψ α ∈ repartitions K F := by
    intro α hα
    refine Algebra.adjoin_induction (hx := hα) ?_ ?_ ?_ ?_
    · intro β hβ
      refine mem_repartitions_of_finite ?_
      have hsub : {v : Place K F | ¬v.adicValuation (Ψ β v) ≤ 1} ⊆ σ ⁻¹' {w : Place K F₁ | ¬w.adicValuation (β w) ≤ 1} := by
        intro v hv
        simp only [Set.mem_preimage, Set.mem_setOf_eq] at hv ⊢
        rw [L1Aux.adicValuation_le_one_iff_mem] at hv ⊢
        rwa [hΨ_apply, hmem] at hv
      exact (hβ.preimage hσinj.injOn).subset hsub
    · intro f
      have : Ψ (algebraMap F₁ (Place K F₁ → F₁) f) = algebraMap F (Place K F → F) (θi f) := by
        funext v; rfl
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
    · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
    · intro x y _ _ hx hy; rw [map_mul]; exact mul_mem hx hy

  let T : ↥(repartitions K F₁) →ₗ[K] ↥(repartitions K F) :=
    { toFun := fun α => ⟨Ψ α, hΨmem α α.2⟩
      map_add' := fun α β => Subtype.ext (map_add Ψ _ _)
      map_smul' := fun c α => by
        apply Subtype.ext
        funext v
        change θi ((c • (α : Place K F₁ → F₁)) (σ v)) = c • θi ((α : Place K F₁ → F₁) (σ v))
        rw [Pi.smul_apply, map_smul] }
  have hT_apply : ∀ (α : ↥(repartitions K F₁)) v, (T α : Place K F → F) v = θi ((α : Place K F₁ → F₁) (σ v)) :=
    fun α v => rfl

  have hT_eoc : ∀ x : F, T (extendOffChart K ((Place.restrictAlong θ hθ) ⁻¹' S₀) (θ x)) = extendOffChart K S₀ x := by
    intro x
    apply Subtype.ext
    funext v
    rw [hT_apply, coe_extendOffChart_apply, coe_extendOffChart_apply, Set.mem_preimage, hσ]
    split_ifs
    · exact map_zero _
    · exact hθi_apply' x

  have hT_bdd : ∀ α ∈ repartitionsOf (0 : Divisor K F₁), T α ∈ repartitionsOf (0 : Divisor K F) := by
    intro α hα v
    have h1 := hα (σ v)
    rw [Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero] at h1 ⊢
    rw [L1Aux.adicValuation_le_one_iff_mem] at h1 ⊢
    rw [hT_apply, hmem]
    exact h1
  have hT_pr : ∀ α ∈ principalRepartitions K F₁, T α ∈ principalRepartitions K F := by
    intro α hα
    obtain ⟨f, hf⟩ := mem_principalRepartitions_iff.mp hα
    refine mem_principalRepartitions_iff.mpr ⟨θi f, ?_⟩
    funext v
    rw [hT_apply, hf]

  rw [cechH1.pullbackAlong_mk, cechH1.pullbackAlong_mk, cechH1ToH1_mk, cechH1ToH1_mk,
    lSpaceOnZero.coe_pullbackAlong_apply, lSpaceOnZero.coe_pullbackAlong_apply] at h
  rw [cechH1ToH1_mk, cechH1ToH1_mk]
  have H := (Submodule.Quotient.eq _).mp h
  obtain ⟨r, hr, p, hp, hrp⟩ := Submodule.mem_sup.mp H
  apply (Submodule.Quotient.eq _).mpr
  refine Submodule.mem_sup.mpr ⟨T r, hT_bdd r hr, T p, hT_pr p hp, ?_⟩
  rw [← map_add, hrp, map_sub, hT_eoc, hT_eoc]

end S_AlgebraicCurve_cechH1ToH1_mk_eq_of_cechH1ToH1_pullbackAlong_mk_eq
end P2MW
export P2MW.S_AlgebraicCurve_cechH1ToH1_mk_eq_of_cechH1ToH1_pullbackAlong_mk_eq (solution)
