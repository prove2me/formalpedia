-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_tensorProduct_linearEquiv_sections_pullback_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/57353401-5c31-593c-8755-f5cf5245d2fa

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_eq_of_forall_map_homOfLE_eq_and_exists_of_compatible
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensorProduct_linearEquiv_sections_pullback_preimage_of_isAffineOpen
import Theorems.Thm_AlgebraicGeometry_IsSeparated_isAffineOpen_inf_and_exists_eq_sum_mul_of_isAffineOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensorProduct_linearEquiv_sections_pullback_of_flat
p2m_attr_erase "instance" "PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free PresheafOfModules.ExteriorPower.instModulePresheafAb"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace W81d14f68

noncomputable abbrev algOf {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (V : X.Opens) :
    Algebra S Γ(X, V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra

noncomputable abbrev modOf {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (M : X.Modules)
    (V : X.Opens) : Module S Γ(M, V) :=
  letI := algOf f V; Module.compHom _ (algebraMap S Γ(X, V))

theorem algOf_res {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S))
    {W W' : X.Opens} (h : W' ≤ W) (r : S) :
    X.presheaf.map (homOfLE h).op ((letI := algOf f W; algebraMap S Γ(X, W)) r) =
      (letI := algOf f W'; algebraMap S Γ(X, W')) r := by
  show X.presheaf.map (homOfLE h).op (((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appLE ⊤ W le_top).hom r) =
    ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appLE ⊤ W' le_top).hom r
  rw [← Scheme.Hom.appLE_map f (le_top : W ≤ f ⁻¹ᵁ ⊤) (homOfLE h).op]
  rfl

theorem algTop_res {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S))
    (W : X.Opens) (r : S) :
    X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
        ((letI := ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom.toAlgebra; algebraMap S Γ(X, ⊤)) r) =
      (letI := algOf f W; algebraMap S Γ(X, W)) r :=
  rfl

noncomputable def resL {X : Scheme.{u}} (M : X.Modules) {R : Type*} [CommRing R] {W W' : X.Opens} (i : W' ⟶ W)
    (φ : R →+* Γ(X, W)) (φ' : R →+* Γ(X, W')) (hφ : ∀ r, X.presheaf.map i.op (φ r) = φ' r) :
    letI := Module.compHom Γ(M, W) φ; letI := Module.compHom Γ(M, W') φ'
    Γ(M, W) →ₗ[R] Γ(M, W') :=
  letI := Module.compHom Γ(M, W) φ; letI := Module.compHom Γ(M, W') φ'
  { toFun := fun s => M.presheaf.map i.op s
    map_add' := fun s t => map_add _ s t
    map_smul' := fun r s => by
      show M.presheaf.map i.op (φ r • s) = φ' r • M.presheaf.map i.op s
      rw [Scheme.Modules.map_smul, hφ] }

theorem resL_apply {X : Scheme.{u}} (M : X.Modules) {R : Type*} [CommRing R] {W W' : X.Opens} (i : W' ⟶ W)
    (φ : R →+* Γ(X, W)) (φ' : R →+* Γ(X, W')) (hφ : ∀ r, X.presheaf.map i.op (φ r) = φ' r) (s : Γ(M, W)) :
    resL M i φ φ' hφ s = M.presheaf.map i.op s :=
  rfl

theorem one_smul_tmul {R : Type*} [CommSemiring R] {R' : Type*} [CommSemiring R'] [Algebra R R']
    {P : Type*} [AddCommMonoid P] [Module R P] (s : R') (p : P) :
    s ⊗ₜ[R] p = s • ((1 : R') ⊗ₜ[R] p) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem bijective_liftBaseChange_of_cover
    {R : Type*} [CommRing R] (R' : Type*) [CommRing R'] [Algebra R R'] [Module.Flat R R']
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Type*} [AddCommGroup A] [Module R A]
    {B : ι → Type*} [∀ i, AddCommGroup (B i)] [∀ i, Module R (B i)]
    {C : ι → ι → Type*} [∀ i j, AddCommGroup (C i j)] [∀ i j, Module R (C i j)]
    {A' : Type*} [AddCommGroup A'] [Module R' A'] [Module R A'] [IsScalarTower R R' A']
    {B' : ι → Type*} [∀ i, AddCommGroup (B' i)] [∀ i, Module R' (B' i)]
    {C' : ι → ι → Type*} [∀ i j, AddCommGroup (C' i j)] [∀ i j, Module R' (C' i j)]
    (res : ∀ i, A →ₗ[R] B i) (ρ₁ : ∀ i j, B i →ₗ[R] C i j) (ρ₂ : ∀ i j, B j →ₗ[R] C i j)
    (sq : ∀ i j (a : A), ρ₁ i j (res i a) = ρ₂ i j (res j a))
    (sep : ∀ a a' : A, (∀ i, res i a = res i a') → a = a')
    (glue : ∀ b : ∀ i, B i, (∀ i j, ρ₁ i j (b i) = ρ₂ i j (b j)) → ∃ a, ∀ i, res i a = b i)
    (res' : ∀ i, A' →ₗ[R'] B' i) (ρ₁' : ∀ i j, B' i →ₗ[R'] C' i j) (ρ₂' : ∀ i j, B' j →ₗ[R'] C' i j)
    (sq' : ∀ i j (a : A'), ρ₁' i j (res' i a) = ρ₂' i j (res' j a))
    (sep' : ∀ a a' : A', (∀ i, res' i a = res' i a') → a = a')
    (u : A →ₗ[R] A') (β : ∀ i, R' ⊗[R] B i ≃ₗ[R'] B' i) (γ : ∀ i j, R' ⊗[R] C i j ≃ₗ[R'] C' i j)
    (hβ : ∀ i (a : A), res' i (u a) = β i (1 ⊗ₜ res i a))
    (hγ₁ : ∀ i j (b : B i), ρ₁' i j (β i (1 ⊗ₜ b)) = γ i j (1 ⊗ₜ ρ₁ i j b))
    (hγ₂ : ∀ i j (b : B j), ρ₂' i j (β j (1 ⊗ₜ b)) = γ i j (1 ⊗ₜ ρ₂ i j b)) :
    Function.Bijective (LinearMap.liftBaseChange R' u) := by
  classical
  set φ := LinearMap.liftBaseChange R' u with hφ

  have Hβ : ∀ i (x : R' ⊗[R] A), res' i (φ x) = β i ((res i).lTensor R' x) := by
    intro i x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s a =>
        rw [hφ, LinearMap.liftBaseChange_tmul, map_smul, hβ, LinearMap.lTensor_tmul, ← map_smul,
          ← one_smul_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have Hγ₁ : ∀ i j (z : R' ⊗[R] B i), ρ₁' i j (β i z) = γ i j ((ρ₁ i j).lTensor R' z) := by
    intro i j z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s b =>
        rw [LinearMap.lTensor_tmul, one_smul_tmul s b, map_smul, map_smul, hγ₁, ← map_smul,
          ← one_smul_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have Hγ₂ : ∀ i j (z : R' ⊗[R] B j), ρ₂' i j (β j z) = γ i j ((ρ₂ i j).lTensor R' z) := by
    intro i j z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s b =>
        rw [LinearMap.lTensor_tmul, one_smul_tmul s b, map_smul, map_smul, hγ₂, ← map_smul,
          ← one_smul_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

  let resPi : A →ₗ[R] (∀ i, B i) := LinearMap.pi res
  let δ : (∀ i, B i) →ₗ[R] (∀ p : ι × ι, C p.1 p.2) :=
    LinearMap.pi fun p => (ρ₁ p.1 p.2).comp (LinearMap.proj p.1) - (ρ₂ p.1 p.2).comp (LinearMap.proj p.2)
  have resPi_apply : ∀ a i, resPi a i = res i a := fun a i => rfl
  have δ_apply : ∀ b p, δ b p = ρ₁ p.1 p.2 (b p.1) - ρ₂ p.1 p.2 (b p.2) := fun b p => rfl
  have hresPi : Function.Injective resPi := fun a a' h =>
    sep a a' fun i => by rw [← resPi_apply, ← resPi_apply, h]
  have hexact : Function.Exact resPi δ := by
    intro b
    constructor
    · intro h0
      obtain ⟨a, ha⟩ := glue b fun i j => by
        have := congr_fun h0 (i, j)
        rwa [δ_apply, Pi.zero_apply, sub_eq_zero] at this
      exact ⟨a, funext ha⟩
    · rintro ⟨a, rfl⟩
      funext p
      rw [δ_apply, resPi_apply, resPi_apply, sq, sub_self, Pi.zero_apply]

  let πB := TensorProduct.piRight R R' R' B
  let πC := TensorProduct.piRight R R' R' (fun p : ι × ι => C p.1 p.2)
  have hπB : ∀ (x : R' ⊗[R] A) i, πB (resPi.lTensor R' x) i = (res i).lTensor R' x := by
    intro x i
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s a => simp [πB, resPi_apply]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  have hπC : ∀ (z : R' ⊗[R] (∀ i, B i)) (p : ι × ι), πC (δ.lTensor R' z) p =
      (ρ₁ p.1 p.2).lTensor R' (πB z p.1) - (ρ₂ p.1 p.2).lTensor R' (πB z p.2) := by
    intro z p
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s b => simp [πB, πC, δ_apply, TensorProduct.tmul_sub]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]; abel
  constructor
  ·
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : ∀ i, (res i).lTensor R' x = 0 := fun i => by
      apply (β i).injective
      rw [← Hβ, hx, map_zero, map_zero]
    have h2 : resPi.lTensor R' x = 0 := by
      apply πB.injective
      rw [map_zero]
      funext i
      rw [hπB, h1, Pi.zero_apply]
    exact (injective_iff_map_eq_zero _).mp
      (Module.Flat.lTensor_preserves_injective_linearMap (M := R') resPi hresPi) x h2
  ·
    intro y
    let b : ∀ i, R' ⊗[R] B i := fun i => (β i).symm (res' i y)
    have hb : ∀ i, β i (b i) = res' i y := fun i => (β i).apply_symm_apply _
    have hδ : δ.lTensor R' (πB.symm b) = 0 := by
      apply πC.injective
      rw [map_zero]
      funext p
      rw [hπC, LinearEquiv.apply_symm_apply, Pi.zero_apply, sub_eq_zero]
      apply (γ p.1 p.2).injective
      rw [← Hγ₁, ← Hγ₂, hb, hb, sq']
    obtain ⟨x, hx⟩ := ((Module.Flat.lTensor_exact R' hexact) (πB.symm b)).mp hδ
    refine ⟨x, sep' _ _ fun i => ?_⟩
    rw [Hβ, ← hπB, hx, LinearEquiv.apply_symm_apply, hb]

end W81d14f68

theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.Flat S S']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) [QuasiCompact f] [IsSeparated f]
    (f' : X' ⟶ Spec (CommRingCat.of S')) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    letI : Algebra S Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom.toAlgebra
    letI : Module S Γ(M, ⊤) := Module.compHom _ (algebraMap S Γ(X, ⊤))
    letI : Algebra S' Γ(X', ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appTop).hom.toAlgebra
    letI : Module S' Γ((Scheme.Modules.pullback c).obj M, ⊤) := Module.compHom _ (algebraMap S' Γ(X', ⊤))
    ∃ β : S' ⊗[S] Γ(M, ⊤) ≃ₗ[S'] Γ((Scheme.Modules.pullback c).obj M, ⊤),
      ∀ s : Γ(M, ⊤), β (1 ⊗ₜ s) = (((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app M).app ⊤) s := by
  classical

  letI algTop : Algebra S Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom.toAlgebra
  letI modTop : Module S Γ(M, ⊤) := Module.compHom _ (algebraMap S Γ(X, ⊤))
  letI algTop' : Algebra S' Γ(X', ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appTop).hom.toAlgebra
  set N := (Scheme.Modules.pullback c).obj M with hN
  letI modTop' : Module S' Γ(N, ⊤) := Module.compHom _ (algebraMap S' Γ(X', ⊤))
  let η := (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app M
  have hcomp : ∀ a : S, c.appTop (algebraMap S Γ(X, ⊤) a) = algebraMap S' Γ(X', ⊤) (algebraMap S S' a) := by
    intro a
    show ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop ≫ c.appTop).hom a =
      (CommRingCat.ofHom (algebraMap S S') ≫ (Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appTop).hom a
    congr 2
    rw [← Scheme.Hom.comp_appTop, hc.w, Scheme.Hom.comp_appTop, ← Category.assoc, ← Category.assoc,
      Scheme.ΓSpecIso_inv_naturality]
  letI modTopS : Module S Γ(N, ⊤) := Module.compHom _ (algebraMap S S')
  haveI towTop : IsScalarTower S S' Γ(N, ⊤) := ⟨fun a b y => by
    show (a • b) • y = (algebraMap S S' a) • (b • y)
    rw [Algebra.smul_def, mul_smul]⟩
  let ηtop : Γ(M, ⊤) → Γ(N, ⊤) := fun s => η.app ⊤ s
  have ηtop_smul : ∀ (r : Γ(X, ⊤)) (s : Γ(M, ⊤)), ηtop (r • s) = c.appTop r • ηtop s :=
    fun r s => Scheme.Modules.Hom.app_smul η r s
  let u : Γ(M, ⊤) →ₗ[S] Γ(N, ⊤) :=
    { toFun := ηtop
      map_add' := fun s t => map_add _ s t
      map_smul' := fun a s => by
        show ηtop (algebraMap S Γ(X, ⊤) a • s) = algebraMap S' Γ(X', ⊤) (algebraMap S S' a) • ηtop s
        rw [ηtop_smul, ← hcomp] }
  have u_apply : ∀ s, u s = Scheme.Modules.pullbackLocalSection c s := fun s => rfl

  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨ι, instι, U, hUaff, hUcov⟩ : ∃ (ι : Type u) (_ : Fintype ι) (U : ι → X.Opens),
      (∀ i, IsAffineOpen (U i)) ∧ (⨆ i, U i) = ⊤ :=
    ⟨X.affineCover.finiteSubcover.I₀, inferInstance, fun i => (X.affineCover.finiteSubcover.f i).opensRange,
      fun i => isAffineOpen_opensRange (X.affineCover.finiteSubcover.f i),
      X.affineCover.finiteSubcover.iSup_opensRange⟩
  have hUUaff : ∀ i j, IsAffineOpen (U i ⊓ U j) := fun i j =>
    (AlgebraicGeometry.IsSeparated.isAffineOpen_inf_and_exists_eq_sum_mul_of_isAffineOpen f (U i) (U j)
      (hUaff i) (hUaff j)).1
  have hUcov' : (⊤ : X'.Opens) ≤ ⨆ i, c ⁻¹ᵁ U i := (c.iSup_preimage_eq_top hUcov).ge

  have hW2 : ∀ (V : X.Opens), IsAffineOpen V →
      letI := W81d14f68.modOf f M V; letI := W81d14f68.modOf f' N (c ⁻¹ᵁ V)
      ∃ β : S' ⊗[S] Γ(M, V) ≃ₗ[S'] Γ(N, c ⁻¹ᵁ V),
        ∀ s : Γ(M, V), β (1 ⊗ₜ s) = Scheme.Modules.pullbackLocalSection c s := fun V hV =>
    Scheme.Modules.IsInvertible.exists_tensorProduct_linearEquiv_sections_pullback_preimage_of_isAffineOpen
      S' f f' c hc M hM V hV
  choose βV hβV using hW2

  letI instB : ∀ i, Module S Γ(M, U i) := fun i => W81d14f68.modOf f M (U i)
  letI instC : ∀ i j, Module S Γ(M, U i ⊓ U j) := fun i j => W81d14f68.modOf f M (U i ⊓ U j)
  letI instB' : ∀ i, Module S' Γ(N, c ⁻¹ᵁ U i) := fun i => W81d14f68.modOf f' N (c ⁻¹ᵁ U i)
  letI instC' : ∀ i j, Module S' Γ(N, c ⁻¹ᵁ (U i ⊓ U j)) := fun i j => W81d14f68.modOf f' N (c ⁻¹ᵁ (U i ⊓ U j))

  let res : ∀ i, Γ(M, ⊤) →ₗ[S] Γ(M, U i) := fun i =>
    W81d14f68.resL M (homOfLE (le_top : U i ≤ ⊤)) (algebraMap S Γ(X, ⊤))
      (letI := W81d14f68.algOf f (U i); algebraMap S Γ(X, U i)) (W81d14f68.algTop_res f (U i))
  let ρ₁ : ∀ i j, Γ(M, U i) →ₗ[S] Γ(M, U i ⊓ U j) := fun i j =>
    W81d14f68.resL M (homOfLE (inf_le_left : U i ⊓ U j ≤ U i))
      (letI := W81d14f68.algOf f (U i); algebraMap S Γ(X, U i))
      (letI := W81d14f68.algOf f (U i ⊓ U j); algebraMap S Γ(X, U i ⊓ U j)) (W81d14f68.algOf_res f inf_le_left)
  let ρ₂ : ∀ i j, Γ(M, U j) →ₗ[S] Γ(M, U i ⊓ U j) := fun i j =>
    W81d14f68.resL M (homOfLE (inf_le_right : U i ⊓ U j ≤ U j))
      (letI := W81d14f68.algOf f (U j); algebraMap S Γ(X, U j))
      (letI := W81d14f68.algOf f (U i ⊓ U j); algebraMap S Γ(X, U i ⊓ U j)) (W81d14f68.algOf_res f inf_le_right)

  let res' : ∀ i, Γ(N, ⊤) →ₗ[S'] Γ(N, c ⁻¹ᵁ U i) := fun i =>
    W81d14f68.resL N (homOfLE (le_top : c ⁻¹ᵁ U i ≤ ⊤)) (algebraMap S' Γ(X', ⊤))
      (letI := W81d14f68.algOf f' (c ⁻¹ᵁ U i); algebraMap S' Γ(X', c ⁻¹ᵁ U i))
      (W81d14f68.algTop_res f' (c ⁻¹ᵁ U i))
  let ρ₁' : ∀ i j, Γ(N, c ⁻¹ᵁ U i) →ₗ[S'] Γ(N, c ⁻¹ᵁ (U i ⊓ U j)) := fun i j =>
    W81d14f68.resL N (homOfLE (c.preimage_mono (inf_le_left : U i ⊓ U j ≤ U i)))
      (letI := W81d14f68.algOf f' (c ⁻¹ᵁ U i); algebraMap S' Γ(X', c ⁻¹ᵁ U i))
      (letI := W81d14f68.algOf f' (c ⁻¹ᵁ (U i ⊓ U j)); algebraMap S' Γ(X', c ⁻¹ᵁ (U i ⊓ U j)))
      (W81d14f68.algOf_res f' (c.preimage_mono inf_le_left))
  let ρ₂' : ∀ i j, Γ(N, c ⁻¹ᵁ U j) →ₗ[S'] Γ(N, c ⁻¹ᵁ (U i ⊓ U j)) := fun i j =>
    W81d14f68.resL N (homOfLE (c.preimage_mono (inf_le_right : U i ⊓ U j ≤ U j)))
      (letI := W81d14f68.algOf f' (c ⁻¹ᵁ U j); algebraMap S' Γ(X', c ⁻¹ᵁ U j))
      (letI := W81d14f68.algOf f' (c ⁻¹ᵁ (U i ⊓ U j)); algebraMap S' Γ(X', c ⁻¹ᵁ (U i ⊓ U j)))
      (W81d14f68.algOf_res f' (c.preimage_mono inf_le_right))

  let β : ∀ i, S' ⊗[S] Γ(M, U i) ≃ₗ[S'] Γ(N, c ⁻¹ᵁ U i) := fun i => βV (U i) (hUaff i)
  let γ : ∀ i j, S' ⊗[S] Γ(M, U i ⊓ U j) ≃ₗ[S'] Γ(N, c ⁻¹ᵁ (U i ⊓ U j)) := fun i j =>
    βV (U i ⊓ U j) (hUUaff i j)

  have res_apply : ∀ i (a : Γ(M, ⊤)), res i a = M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op a :=
    fun i a => rfl
  have ρ₁_apply : ∀ i j (b : Γ(M, U i)),
      ρ₁ i j b = M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op b := fun i j b => rfl
  have ρ₂_apply : ∀ i j (b : Γ(M, U j)),
      ρ₂ i j b = M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op b := fun i j b => rfl
  have res'_apply : ∀ i (a : Γ(N, ⊤)),
      res' i a = N.presheaf.map (homOfLE (le_top : c ⁻¹ᵁ U i ≤ ⊤)).op a := fun i a => rfl
  have ρ₁'_apply : ∀ i j (b : Γ(N, c ⁻¹ᵁ U i)), ρ₁' i j b =
      N.presheaf.map (homOfLE (c.preimage_mono (inf_le_left : U i ⊓ U j ≤ U i))).op b := fun i j b => rfl
  have ρ₂'_apply : ∀ i j (b : Γ(N, c ⁻¹ᵁ U j)), ρ₂' i j b =
      N.presheaf.map (homOfLE (c.preimage_mono (inf_le_right : U i ⊓ U j ≤ U j))).op b := fun i j b => rfl
  have resresM : ∀ {O₁ O₂ O₃ : X.Opens} (h₁₂ : O₂ ≤ O₁) (h₂₃ : O₃ ≤ O₂) (x : Γ(M, O₁)),
      M.presheaf.map (homOfLE h₂₃).op (M.presheaf.map (homOfLE h₁₂).op x) =
        M.presheaf.map (homOfLE (h₂₃.trans h₁₂)).op x := by
    intro O₁ O₂ O₃ h₁₂ h₂₃ x
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
  have resresN : ∀ {O₁ O₂ O₃ : X'.Opens} (h₁₂ : O₂ ≤ O₁) (h₂₃ : O₃ ≤ O₂) (x : Γ(N, O₁)),
      N.presheaf.map (homOfLE h₂₃).op (N.presheaf.map (homOfLE h₁₂).op x) =
        N.presheaf.map (homOfLE (h₂₃.trans h₁₂)).op x := by
    intro O₁ O₂ O₃ h₁₂ h₂₃ x
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl

  have sq : ∀ i j (a : Γ(M, ⊤)), ρ₁ i j (res i a) = ρ₂ i j (res j a) := by
    intro i j a
    rw [ρ₁_apply, ρ₂_apply, res_apply, res_apply, resresM, resresM]
  have sq' : ∀ i j (a : Γ(N, ⊤)), ρ₁' i j (res' i a) = ρ₂' i j (res' j a) := by
    intro i j a
    rw [ρ₁'_apply, ρ₂'_apply, res'_apply, res'_apply, resresN, resresN]

  have W1X := AlgebraicGeometry.Scheme.Modules.eq_of_forall_map_homOfLE_eq_and_exists_of_compatible
    M U ⊤ (fun _ => le_top) hUcov.ge
  have W1X' := AlgebraicGeometry.Scheme.Modules.eq_of_forall_map_homOfLE_eq_and_exists_of_compatible
    N (fun i => c ⁻¹ᵁ U i) ⊤ (fun _ => le_top) hUcov'
  have sep : ∀ a a' : Γ(M, ⊤), (∀ i, res i a = res i a') → a = a' := fun a a' h =>
    W1X.1 a a' fun i => by rw [← res_apply, ← res_apply, h i]
  have glue : ∀ b : ∀ i, Γ(M, U i), (∀ i j, ρ₁ i j (b i) = ρ₂ i j (b j)) →
      ∃ a : Γ(M, ⊤), ∀ i, res i a = b i := fun b hb => by
    obtain ⟨a, ha⟩ := W1X.2 b fun i j => by rw [← ρ₁_apply, ← ρ₂_apply, hb i j]
    exact ⟨a, fun i => by rw [res_apply, ha i]⟩
  have sep' : ∀ a a' : Γ(N, ⊤), (∀ i, res' i a = res' i a') → a = a' := fun a a' h =>
    W1X'.1 a a' fun i => by rw [← res'_apply, ← res'_apply, h i]

  have hβ : ∀ i (a : Γ(M, ⊤)), res' i (u a) = β i (1 ⊗ₜ res i a) := by
    intro i a
    rw [hβV, res'_apply, res_apply, u_apply]
    exact Scheme.Modules.map_homOfLE_pullbackLocalSection c (le_top : U i ≤ ⊤) a
  have hγ₁ : ∀ i j (b : Γ(M, U i)), ρ₁' i j (β i (1 ⊗ₜ b)) = γ i j (1 ⊗ₜ ρ₁ i j b) := by
    intro i j b
    rw [hβV, hβV, ρ₁'_apply, ρ₁_apply]
    exact Scheme.Modules.map_homOfLE_pullbackLocalSection c (inf_le_left : U i ⊓ U j ≤ U i) b
  have hγ₂ : ∀ i j (b : Γ(M, U j)), ρ₂' i j (β j (1 ⊗ₜ b)) = γ i j (1 ⊗ₜ ρ₂ i j b) := by
    intro i j b
    rw [hβV, hβV, ρ₂'_apply, ρ₂_apply]
    exact Scheme.Modules.map_homOfLE_pullbackLocalSection c (inf_le_right : U i ⊓ U j ≤ U j) b

  have hbij : Function.Bijective (LinearMap.liftBaseChange S' u) :=
    W81d14f68.bijective_liftBaseChange_of_cover S' res ρ₁ ρ₂ sq sep glue res' ρ₁' ρ₂' sq' sep' u β γ
      hβ hγ₁ hγ₂
  refine ⟨LinearEquiv.ofBijective (LinearMap.liftBaseChange S' u) hbij, fun s => ?_⟩
  rw [LinearEquiv.ofBijective_apply, LinearMap.liftBaseChange_tmul, one_smul]
  rfl

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensorProduct_linearEquiv_sections_pullback_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensorProduct_linearEquiv_sections_pullback_of_flat (solution)
