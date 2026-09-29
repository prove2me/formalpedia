-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.kunneth_toModule_diag_injective_of_cls_unitPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/423b40e8-eaa6-56ce-8c84-c6cb7e020ce6

import Theorems.Thm_CochainCx_Bounded_exists_kunneth_toModule_HTot_tensor_injective
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_biCech_preimageFamily_equiv_tensor_cochain_pinned
import Theorems.Thm_DoubleComplex_exists_HTot_equiv_of_levelwise_equiv_pinned
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_HTot_biCech_equiv_prodCover_cup_pinned
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_HSucc_equiv_unitPullback_id_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_unitPullback_prodCover_cup_sub_cup_unitPullback_mem
import Theorems.Thm_AlgebraicGeometry_Scheme_isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BiCech
import Definitions.Def_AlgebraicGeometry_BoundedCochainTensor
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_kunneth_toModule_diag_injective_of_cls_unitPullback
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableOSub"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct DirectSum

universe u

namespace G3bReduce

open AlgebraicGeometry.OModulePresheaf DoubleComplex

section ClassHandle

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
  (F : OModulePresheaf π) (K : V.OrderedAffineCover) (hdd : ∀ i, F.d K (i + 1) ∘ₗ F.d K i = 0)
  {H : Type u} [AddCommGroup H] [Module R H] (𝒜 : ℕ → Submodule R H)
  (cls : ∀ n : ℕ, ↥(LinearMap.ker (F.d K n)) →ₗ[R] H)
  (cls_range : ∀ n : ℕ, LinearMap.range (cls n) = 𝒜 n)
  (cls_zero : ∀ z : ↥(LinearMap.ker (F.d K 0)), cls 0 z = 0 ↔ z = 0)
  (cls_succ : ∀ (n : ℕ) (z : ↥(LinearMap.ker (F.d K (n + 1)))),
    cls (n + 1) z = 0 ↔ (z : F.cochain K (n + 1)) ∈ LinearMap.range (F.d K n))

noncomputable def psi (n : ℕ) : ↥(LinearMap.ker (F.d K n)) →ₗ[R] ↥(𝒜 n) :=
  LinearMap.codRestrict (𝒜 n) (cls n) (fun z => by rw [← cls_range]; exact LinearMap.mem_range_self _ _)

theorem psi_apply_coe (n : ℕ) (z : ↥(LinearMap.ker (F.d K n))) :
    (psi F K 𝒜 cls cls_range n z : H) = cls n z := rfl

include cls_zero cls_succ in
theorem ker_psi (n : ℕ) :
    LinearMap.ker (psi F K 𝒜 cls cls_range n) = (CochainCx.Bounded.ofCech F K hdd).B n := by
  ext z
  rw [LinearMap.mem_ker, ← Subtype.coe_inj, psi_apply_coe, Submodule.coe_zero]
  cases n with
  | zero =>
    rw [cls_zero]
    exact (Submodule.mem_bot R).symm
  | succ m =>
    rw [cls_succ]
    exact Iff.rfl

theorem psi_surjective (n : ℕ) : Function.Surjective (psi F K 𝒜 cls cls_range n) := by
  intro y
  have hy : (y : H) ∈ LinearMap.range (cls n) := by rw [cls_range]; exact y.2
  obtain ⟨z, hz⟩ := hy
  exact ⟨z, Subtype.ext hz⟩

noncomputable def phi (n : ℕ) : (CochainCx.Bounded.ofCech F K hdd).H n ≃ₗ[R] ↥(𝒜 n) :=
  (Submodule.quotEquivOfEq _ _ (ker_psi F K hdd 𝒜 cls cls_range cls_zero cls_succ n).symm) ≪≫ₗ
    LinearMap.quotKerEquivOfSurjective (psi F K 𝒜 cls cls_range n) (psi_surjective F K 𝒜 cls cls_range n)

theorem phi_mk (n : ℕ) (z : ↥(LinearMap.ker (F.d K n))) :
    (phi F K hdd 𝒜 cls cls_range cls_zero cls_succ n (Submodule.Quotient.mk z) : H) = cls n z := by
  rw [phi, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  rfl

end ClassHandle

theorem cls_mul_of_eq {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}
    (K : V.OrderedAffineCover) {H : Type u} [Ring H] [Algebra R H]
    (cls : ∀ n : ℕ, ↥(LinearMap.ker ((OModulePresheaf.unit π).d K n)) →ₗ[R] H)
    (cls_mul : ∀ (a b : ℕ) (α : ↥(LinearMap.ker ((OModulePresheaf.unit π).d K a)))
        (β : ↥(LinearMap.ker ((OModulePresheaf.unit π).d K b))),
      ∃ hγ : (OModulePresheaf.unit π).cup K a b (a + b) rfl α.1 β.1 ∈ LinearMap.ker ((OModulePresheaf.unit π).d K (a + b)),
        cls (a + b) ⟨_, hγ⟩ = cls a α * cls b β)
    {a b n : ℕ} (hn : a + b = n)
    (α : ↥(LinearMap.ker ((OModulePresheaf.unit π).d K a))) (β : ↥(LinearMap.ker ((OModulePresheaf.unit π).d K b))) :
    ∃ hγ : (OModulePresheaf.unit π).cup K a b n hn α.1 β.1 ∈ LinearMap.ker ((OModulePresheaf.unit π).d K n),
      cls n ⟨_, hγ⟩ = cls a α * cls b β := by
  subst hn
  exact cls_mul a b α β

theorem cls_refine_cup_eq
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of k)) (πY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated πX] [IsSeparated πY]
    (𝔘 : X.OrderedAffineCover) (𝔙 : Y.OrderedAffineCover)
    (haff : ∀ i j, IsAffineOpen ((𝔘.preimageFamily (pullback.fst πX πY)).U i ⊓ (𝔙.preimageFamily (pullback.snd πX πY)).U j))
    (hcov : ⨆ ij : 𝔘.ι × 𝔙.ι,
      (𝔘.preimageFamily (pullback.fst πX πY)).U ij.1 ⊓ (𝔙.preimageFamily (pullback.snd πX πY)).U ij.2 = ⊤)

    (𝒲 : (pullback πX πY).OrderedAffineCover) (lam₁ : 𝒲.ι → 𝔘.ι) (lam₂ : 𝒲.ι → 𝔙.ι)
    (h₁ : ∀ w, 𝒲.U w ≤ pullback.fst πX πY ⁻¹ᵁ 𝔘.U (lam₁ w))
    (h₂ : ∀ w, 𝒲.U w ≤ pullback.snd πX πY ⁻¹ᵁ 𝔙.U (lam₂ w))
    (hμ : ∀ w, 𝒲.U w ≤ (𝟙 (pullback πX πY)) ⁻¹ᵁ
      ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).U
        (toLex (lam₁ w, lam₂ w)))
    (p q n : ℕ) (hn : p + q = n)
    (α : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝔘 p))) (β : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝔙 q)))
    {H' : Type u} [AddCommGroup H'] [Module k H']
    (cls' : ∀ n : ℕ, ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).d 𝒲 n)) →ₗ[k] H')
    (cls'_succ : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).d 𝒲 (n + 1)))),
      cls' (n + 1) z = 0 ↔ (z : (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).cochain 𝒲 (n + 1)) ∈
        LinearMap.range ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).d 𝒲 n))
    (hzA : OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (𝟙 (pullback πX πY)) 𝒲
        ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov)
        (fun w => toLex (lam₁ w, lam₂ w)) hμ n
        ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).cup
          ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) p q n hn
          (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.fst πX πY)
            ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) 𝔘
            (fun ij => (ofLex ij).1) (fun ij => inf_le_left) p α.1)
          (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.snd πX πY)
            ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) 𝔙
            (fun ij => (ofLex ij).2) (fun ij => inf_le_right) q β.1)) ∈
      LinearMap.ker ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).d 𝒲 n))
    (hzB : (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).cup 𝒲 p q n hn
        (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.fst πX πY) 𝒲 𝔘 lam₁ h₁ p α.1)
        (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.snd πX πY) 𝒲 𝔙 lam₂ h₂ q β.1) ∈
      LinearMap.ker ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).d 𝒲 n)) :
    cls' n ⟨_, hzA⟩ = cls' n ⟨_, hzB⟩ := by
  have hKe := AlgebraicGeometry.OModulePresheaf.unitPullback_prodCover_cup_sub_cup_unitPullback_mem πX πY 𝔘 𝔙 haff hcov
    𝒲 lam₁ lam₂ h₁ h₂ hμ p q n hn α β
  cases n with
  | zero =>
    change _ ∈ (⊥ : Submodule k ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).cochain 𝒲 0)) at hKe
    rw [Submodule.mem_bot, sub_eq_zero] at hKe
    congr 1
    exact Subtype.ext hKe
  | succ m =>
    change _ ∈ LinearMap.range ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).d 𝒲 m) at hKe
    have h0 : cls' (m + 1) (⟨_, hzA⟩ - ⟨_, hzB⟩) = 0 := (cls'_succ m _).mpr hKe
    rwa [map_sub, sub_eq_zero] at h0

set_option maxHeartbeats 3200000 in
theorem main
    {k : Type u} [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k)) [IsSeparated f]
    (𝒦 : A.OrderedAffineCover)
    (𝒲 : (pullback f f).OrderedAffineCover) (lam₁ lam₂ : 𝒲.ι → 𝒦.ι)
    (h₁ : ∀ w, 𝒲.U w ≤ pullback.fst f f ⁻¹ᵁ 𝒦.U (lam₁ w))
    (h₂ : ∀ w, 𝒲.U w ≤ pullback.snd f f ⁻¹ᵁ 𝒦.U (lam₂ w))
    (H : Type u) [Ring H] [Algebra k H] (𝒜 : ℕ → Submodule k H) [SetLike.GradedMonoid 𝒜]
    (cls : ∀ n : ℕ, ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 n)) →ₗ[k] H)
    (cls_range : ∀ n : ℕ, LinearMap.range (cls n) = 𝒜 n)
    (cls_zero : ∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 0)), cls 0 z = 0 ↔ z = 0)
    (cls_succ : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 (n + 1)))),
      cls (n + 1) z = 0 ↔ (z : (OModulePresheaf.unit f).cochain 𝒦 (n + 1)) ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒦 n))
    (H' : Type u) [Ring H'] [Algebra k H'] (𝒜' : ℕ → Submodule k H') [SetLike.GradedMonoid 𝒜']
    (cls' : ∀ n : ℕ, ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n)) →ₗ[k] H')
    (cls'_range : ∀ n : ℕ, LinearMap.range (cls' n) = 𝒜' n)
    (cls'_zero : ∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 0)), cls' 0 z = 0 ↔ z = 0)
    (cls'_succ : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 (n + 1)))),
      cls' (n + 1) z = 0 ↔ (z : (OModulePresheaf.unit (pullback.fst f f ≫ f)).cochain 𝒲 (n + 1)) ∈ LinearMap.range ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n))
    (cls'_mul : ∀ (a b : ℕ) (α : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 a))) (β : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 b))),
      ∃ hγ : (OModulePresheaf.unit (pullback.fst f f ≫ f)).cup 𝒲 a b (a + b) rfl α.1 β.1 ∈ LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 (a + b)),
        cls' (a + b) ⟨_, hγ⟩ = cls' a α * cls' b β)
    (cls'_internal : DirectSum.IsInternal 𝒜')
    (p₁ p₂ : H →ₐ[k] H')
    (hp₁ : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 n))),
      ∃ hz : OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.fst f f) 𝒲 𝒦 lam₁ h₁ n z.1 ∈
          LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n),
        p₁ (cls n z) = cls' n ⟨_, hz⟩)
    (hp₂ : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 n))),
      ∃ hz : OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.snd f f) 𝒲 𝒦 lam₂ h₂ n z.1 ∈
          LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n),
        p₂ (cls n z) = cls' n ⟨_, hz⟩)
    (n : ℕ) :
    Function.Injective (DirectSum.toModule k (DoubleComplex.Diag n) H' fun i : DoubleComplex.Diag n =>
      LinearMap.mul' k H' ∘ₗ
        TensorProduct.map (p₁.toLinearMap ∘ₗ (𝒜 i.1.1).subtype) (p₂.toLinearMap ∘ₗ (𝒜 i.1.2).subtype)) := by
  classical

  let P := pullback f f
  let p1 := pullback.fst f f
  let p2 := pullback.snd f f

  have haff : ∀ i j, IsAffineOpen ((𝒦.preimageFamily (pullback.fst f f)).U i ⊓ (𝒦.preimageFamily (pullback.snd f f)).U j) :=
    fun i j => (AlgebraicGeometry.Scheme.isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback f f
      (pullback.fst f f) (pullback.snd f f) (IsPullback.of_hasPullback f f) (𝒦.U i) (𝒦.isAffineOpen i)
      (𝒦.U j) (𝒦.isAffineOpen j)).1
  have hcov : ⨆ ij : (𝒦.preimageFamily (pullback.fst f f)).ι × (𝒦.preimageFamily (pullback.snd f f)).ι,
      (𝒦.preimageFamily (pullback.fst f f)).U ij.1 ⊓ (𝒦.preimageFamily (pullback.snd f f)).U ij.2 = ⊤ := by
    apply le_antisymm le_top
    intro z _
    have e1 : (pullback.fst f f).base z ∈ (⊤ : A.Opens) := trivial
    have e2 : (pullback.snd f f).base z ∈ (⊤ : A.Opens) := trivial
    rw [← 𝒦.iSup_eq_top] at e1 e2
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp e1
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp e2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(i, j), ⟨hi, hj⟩⟩
  let 𝔓 := (𝒦.preimageFamily (pullback.fst f f)).prodCover (𝒦.preimageFamily (pullback.snd f f)) haff hcov
  have hμ : ∀ w, 𝒲.U w ≤ (𝟙 (pullback f f)) ⁻¹ᵁ 𝔓.U (toLex (lam₁ w, lam₂ w)) := fun w => le_inf (h₁ w) (h₂ w)

  let C : CochainCx.Bounded k :=
    CochainCx.Bounded.ofCech (OModulePresheaf.unit f) 𝒦 (AlgebraicGeometry.OModulePresheaf.d_comp_d _ _)
  let D' : DoubleComplex.Bounded k :=
    (OModulePresheaf.unit (pullback.fst f f ≫ f)).biCech (𝒦.preimageFamily (pullback.fst f f)) (𝒦.preimageFamily (pullback.snd f f))
  let CP : CochainCx.Bounded k :=
    CochainCx.Bounded.ofCech (OModulePresheaf.unit (pullback.fst f f ≫ f)) 𝔓 (AlgebraicGeometry.OModulePresheaf.d_comp_d _ _)
  let CW : CochainCx.Bounded k :=
    CochainCx.Bounded.ofCech (OModulePresheaf.unit (pullback.fst f f ≫ f)) 𝒲 (AlgebraicGeometry.OModulePresheaf.d_comp_d _ _)

  obtain ⟨κ, hκ, hκinj⟩ := CochainCx.Bounded.exists_kunneth_toModule_HTot_tensor_injective C C n

  obtain ⟨e, heH, heV, hepin⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_biCech_preimageFamily_equiv_tensor_cochain_pinned f f 𝒦 𝒦
  obtain ⟨E, hE⟩ := DoubleComplex.exists_HTot_equiv_of_levelwise_equiv_pinned (C.tensor C) D'
    (fun p q => (e p q).symm)
    (fun p q x => by
      show (e (p + 1) q).symm (((OModulePresheaf.unit f).d 𝒦 p).rTensor ((OModulePresheaf.unit f).cochain 𝒦 q) x) =
        OModulePresheaf.BiCech.dH (OModulePresheaf.unit (pullback.fst f f ≫ f))
          (𝒦.preimageFamily (pullback.fst f f)) (𝒦.preimageFamily (pullback.snd f f)) p q ((e p q).symm x)
      rw [LinearEquiv.symm_apply_eq, heH, LinearEquiv.apply_symm_apply])
    (fun p q x => by
      show (e p (q + 1)).symm (((OModulePresheaf.unit f).d 𝒦 q).lTensor ((OModulePresheaf.unit f).cochain 𝒦 p) x) =
        OModulePresheaf.BiCech.dV (OModulePresheaf.unit (pullback.fst f f ≫ f))
          (𝒦.preimageFamily (pullback.fst f f)) (𝒦.preimageFamily (pullback.snd f f)) p q ((e p q).symm x)
      rw [LinearEquiv.symm_apply_eq, heV, LinearEquiv.apply_symm_apply])
    n

  obtain ⟨θ, hθ⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_HTot_biCech_equiv_prodCover_cup_pinned f f 𝒦 𝒦 haff hcov

  obtain ⟨ρ₀, ρs, hρ₀, hρs⟩ := AlgebraicGeometry.OModulePresheaf.exists_HSucc_equiv_unitPullback_id_of_isSeparated
    (pullback.fst f f ≫ f) 𝔓 𝒲 (fun w => toLex (lam₁ w, lam₂ w)) hμ
  have hρ : ∃ ρ : ∀ m : ℕ,
      (CochainCx.Bounded.ofCech (OModulePresheaf.unit (pullback.fst f f ≫ f))
          ((𝒦.preimageFamily (pullback.fst f f)).prodCover (𝒦.preimageFamily (pullback.snd f f)) haff hcov)
          (AlgebraicGeometry.OModulePresheaf.d_comp_d _ _)).H m ≃ₗ[k]
        (CochainCx.Bounded.ofCech (OModulePresheaf.unit (pullback.fst f f ≫ f)) 𝒲
          (AlgebraicGeometry.OModulePresheaf.d_comp_d _ _)).H m,
      ∀ (m : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d
        ((𝒦.preimageFamily (pullback.fst f f)).prodCover (𝒦.preimageFamily (pullback.snd f f)) haff hcov) m))),
        ∃ hz : OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (𝟙 (pullback f f)) 𝒲
            ((𝒦.preimageFamily (pullback.fst f f)).prodCover (𝒦.preimageFamily (pullback.snd f f)) haff hcov)
            (fun w => toLex (lam₁ w, lam₂ w)) hμ m z.1 ∈
            LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 m),
          ρ m (Submodule.Quotient.mk z) = Submodule.Quotient.mk ⟨_, hz⟩ := by
    refine ⟨fun m => match m with
      | 0 => (Submodule.quotEquivOfEqBot (CP.B 0) rfl) ≪≫ₗ ρ₀ ≪≫ₗ (Submodule.quotEquivOfEqBot (CW.B 0) rfl).symm
      | m + 1 => ρs m, ?_⟩
    intro m z
    cases m with
    | zero =>
      refine ⟨(hρ₀ z) ▸ (ρ₀ z).2, ?_⟩
      show (Submodule.quotEquivOfEqBot (CW.B 0) rfl).symm (ρ₀ (Submodule.quotEquivOfEqBot (CP.B 0) rfl
        (Submodule.Quotient.mk z))) = _
      rw [Submodule.quotEquivOfEqBot_apply_mk, Submodule.quotEquivOfEqBot_symm_apply]
      congr 1
      exact Subtype.ext (hρ₀ z)
    | succ m => exact hρs m z
  obtain ⟨ρ, hρ⟩ := hρ

  let φ := phi (OModulePresheaf.unit f) 𝒦 (AlgebraicGeometry.OModulePresheaf.d_comp_d _ _) 𝒜 cls cls_range cls_zero cls_succ
  let φ' := phi (OModulePresheaf.unit (pullback.fst f f ≫ f)) 𝒲 (AlgebraicGeometry.OModulePresheaf.d_comp_d _ _)
    𝒜' cls' cls'_range cls'_zero cls'_succ
  have hφ : ∀ (a : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 a))), (φ a (Submodule.Quotient.mk z) : H) = cls a z :=
    fun a z => phi_mk _ _ _ _ _ _ _ _ a z
  have hφ' : ∀ (a : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 a))),
      (φ' a (Submodule.Quotient.mk z) : H') = cls' a z :=
    fun a z => phi_mk _ _ _ _ _ _ _ _ a z

  let ι : CW.H n →ₗ[k] H' := (𝒜' n).subtype ∘ₗ (φ' n).toLinearMap
  have hι : Function.Injective ι := fun x y hxy => (φ' n).injective (Subtype.ext hxy)

  let g : (⨁ i : Diag n, C.H i.1.1 ⊗[k] C.H i.1.2) →ₗ[k] H' :=
    ι ∘ₗ (ρ n).toLinearMap ∘ₗ (θ n).toLinearMap ∘ₗ E.toLinearMap ∘ₗ
      DirectSum.toModule k (Diag n) (HTot (C.tensor C) n) κ
  have hg : Function.Injective g :=
    hι.comp ((ρ n).injective.comp ((θ n).injective.comp (E.injective.comp hκinj)))

  let s : (⨁ i : Diag n, C.H i.1.1 ⊗[k] C.H i.1.2) →ₗ[k] (⨁ i : Diag n, ↥(𝒜 i.1.1) ⊗[k] ↥(𝒜 i.1.2)) :=
    DirectSum.toModule k (Diag n) _ fun i =>
      DirectSum.lof k (Diag n) (fun i : Diag n => ↥(𝒜 i.1.1) ⊗[k] ↥(𝒜 i.1.2)) i ∘ₗ
        (TensorProduct.congr (φ i.1.1) (φ i.1.2)).toLinearMap
  let s' : (⨁ i : Diag n, ↥(𝒜 i.1.1) ⊗[k] ↥(𝒜 i.1.2)) →ₗ[k] (⨁ i : Diag n, C.H i.1.1 ⊗[k] C.H i.1.2) :=
    DirectSum.toModule k (Diag n) _ fun i =>
      DirectSum.lof k (Diag n) (fun i : Diag n => C.H i.1.1 ⊗[k] C.H i.1.2) i ∘ₗ
        (TensorProduct.congr (φ i.1.1) (φ i.1.2)).symm.toLinearMap
  have hss' : s ∘ₗ s' = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.id_apply, s', s, DirectSum.toModule_lof, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
  have hs : Function.Surjective s := fun y => ⟨s' y, by rw [← LinearMap.comp_apply, hss', LinearMap.id_apply]⟩

  have key : (DirectSum.toModule k (DoubleComplex.Diag n) H' fun i : DoubleComplex.Diag n =>
      LinearMap.mul' k H' ∘ₗ
        TensorProduct.map (p₁.toLinearMap ∘ₗ (𝒜 i.1.1).subtype) (p₂.toLinearMap ∘ₗ (𝒜 i.1.2).subtype)) ∘ₗ s = g := by
    apply DirectSum.linearMap_ext
    intro i
    apply TensorProduct.ext'
    intro a' b'
    obtain ⟨α, rfl⟩ := Submodule.Quotient.mk_surjective _ a'
    obtain ⟨β, rfl⟩ := Submodule.Quotient.mk_surjective _ b'

    have lhs : (DirectSum.toModule k (DoubleComplex.Diag n) H' fun i : DoubleComplex.Diag n =>
        LinearMap.mul' k H' ∘ₗ
          TensorProduct.map (p₁.toLinearMap ∘ₗ (𝒜 i.1.1).subtype) (p₂.toLinearMap ∘ₗ (𝒜 i.1.2).subtype))
        (s (DirectSum.lof k (Diag n) (fun i : Diag n => C.H i.1.1 ⊗[k] C.H i.1.2) i
          (Submodule.Quotient.mk α ⊗ₜ[k] Submodule.Quotient.mk β))) = p₁ (cls i.1.1 α) * p₂ (cls i.1.2 β) := by
      simp only [s, DirectSum.toModule_lof, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.congr_tmul,
        TensorProduct.map_tmul, LinearMap.mul'_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply, hφ]

    obtain ⟨hz₁, hpα⟩ := hp₁ i.1.1 α
    obtain ⟨hz₂, hpβ⟩ := hp₂ i.1.2 β
    obtain ⟨hγ, hmul⟩ := cls_mul_of_eq 𝒲 cls' cls'_mul (show i.1.1 + i.1.2 = n from i.2) ⟨_, hz₁⟩ ⟨_, hz₂⟩

    obtain ⟨hzA, hA⟩ := hκ i α β
    obtain ⟨hzB, hB⟩ := hE ⟨_, hzA⟩
    obtain ⟨hzC, hwC, hC⟩ := hθ n i α β
    obtain ⟨hzD, hD⟩ := hρ n ⟨_, hwC⟩

    have hbox : (⟨_, hzB⟩ : ↥(LinearMap.ker (dTot D' n))) = ⟨_, hzC⟩ := by
      apply Subtype.ext
      dsimp only
      funext j
      by_cases hji : j = i
      · subst hji
        rw [Pi.single_eq_same, Pi.single_eq_same]
        funext st
        exact hepin j.1.1 j.1.2 α.1 β.1 st.1 st.2
      · rw [Pi.single_eq_of_ne hji, Pi.single_eq_of_ne hji]
        exact LinearEquiv.map_zero _
    simp only [LinearMap.comp_apply]
    rw [lhs, hpα, hpβ, ← hmul]
    show _ = ι (ρ n (θ n (E (DirectSum.toModule k (Diag n) (HTot (C.tensor C) n) κ
      (DirectSum.lof k (Diag n) (fun i : Diag n => C.H i.1.1 ⊗[k] C.H i.1.2) i
        (Submodule.Quotient.mk α ⊗ₜ[k] Submodule.Quotient.mk β))))))
    rw [DirectSum.toModule_lof, hA, hB, hbox, hC]
    refine Eq.trans ?_ (congrArg ι hD).symm
    show _ = ((φ' n (Submodule.Quotient.mk ⟨_, hzD⟩)) : H')
    rw [hφ']
    exact (cls_refine_cup_eq f f 𝒦 𝒦 haff hcov 𝒲 lam₁ lam₂ h₁ h₂ hμ i.1.1 i.1.2 n i.2 α β cls' cls'_succ hzD hγ).symm

  intro x y hxy
  obtain ⟨x', rfl⟩ := hs x
  obtain ⟨y', rfl⟩ := hs y
  have hg' : g x' = g y' := by
    rw [← key]
    exact hxy
  rw [hg hg']

end G3bReduce

theorem solution
    {k : Type u} [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k)) [IsSeparated f]
    (𝒦 : A.OrderedAffineCover)
    (𝒲 : (pullback f f).OrderedAffineCover) (lam₁ lam₂ : 𝒲.ι → 𝒦.ι)
    (h₁ : ∀ w, 𝒲.U w ≤ pullback.fst f f ⁻¹ᵁ 𝒦.U (lam₁ w))
    (h₂ : ∀ w, 𝒲.U w ≤ pullback.snd f f ⁻¹ᵁ 𝒦.U (lam₂ w))
    (H : Type u) [Ring H] [Algebra k H] (𝒜 : ℕ → Submodule k H) [SetLike.GradedMonoid 𝒜]
    (cls : ∀ n : ℕ, ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 n)) →ₗ[k] H)
    (cls_range : ∀ n : ℕ, LinearMap.range (cls n) = 𝒜 n)
    (cls_zero : ∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 0)), cls 0 z = 0 ↔ z = 0)
    (cls_succ : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 (n + 1)))),
      cls (n + 1) z = 0 ↔ (z : (OModulePresheaf.unit f).cochain 𝒦 (n + 1)) ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒦 n))
    (H' : Type u) [Ring H'] [Algebra k H'] (𝒜' : ℕ → Submodule k H') [SetLike.GradedMonoid 𝒜']
    (cls' : ∀ n : ℕ, ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n)) →ₗ[k] H')
    (cls'_range : ∀ n : ℕ, LinearMap.range (cls' n) = 𝒜' n)
    (cls'_zero : ∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 0)), cls' 0 z = 0 ↔ z = 0)
    (cls'_succ : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 (n + 1)))),
      cls' (n + 1) z = 0 ↔ (z : (OModulePresheaf.unit (pullback.fst f f ≫ f)).cochain 𝒲 (n + 1)) ∈ LinearMap.range ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n))
    (cls'_mul : ∀ (a b : ℕ) (α : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 a))) (β : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 b))),
      ∃ hγ : (OModulePresheaf.unit (pullback.fst f f ≫ f)).cup 𝒲 a b (a + b) rfl α.1 β.1 ∈ LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 (a + b)),
        cls' (a + b) ⟨_, hγ⟩ = cls' a α * cls' b β)
    (cls'_internal : DirectSum.IsInternal 𝒜')
    (p₁ p₂ : H →ₐ[k] H')
    (hp₁ : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 n))),
      ∃ hz : OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.fst f f) 𝒲 𝒦 lam₁ h₁ n z.1 ∈
          LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n),
        p₁ (cls n z) = cls' n ⟨_, hz⟩)
    (hp₂ : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 n))),
      ∃ hz : OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.snd f f) 𝒲 𝒦 lam₂ h₂ n z.1 ∈
          LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n),
        p₂ (cls n z) = cls' n ⟨_, hz⟩)
    (n : ℕ) :
    Function.Injective (DirectSum.toModule k (DoubleComplex.Diag n) H' fun i : DoubleComplex.Diag n =>
      LinearMap.mul' k H' ∘ₗ
        TensorProduct.map (p₁.toLinearMap ∘ₗ (𝒜 i.1.1).subtype) (p₂.toLinearMap ∘ₗ (𝒜 i.1.2).subtype)) :=
  G3bReduce.main f 𝒦 𝒲 lam₁ lam₂ h₁ h₂ H 𝒜 cls cls_range cls_zero cls_succ H' 𝒜' cls' cls'_range cls'_zero cls'_succ cls'_mul cls'_internal p₁ p₂ hp₁ hp₂ n

end S_AlgebraicGeometry_OModulePresheaf_kunneth_toModule_diag_injective_of_cls_unitPullback
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_kunneth_toModule_diag_injective_of_cls_unitPullback (solution)
