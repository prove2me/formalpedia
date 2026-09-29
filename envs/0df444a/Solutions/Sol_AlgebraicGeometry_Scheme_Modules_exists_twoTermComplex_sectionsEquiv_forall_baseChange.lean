-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_twoTermComplex_sectionsEquiv_forall_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/bbbf6e11-a16a-56db-8355-09a4379c5cac

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_CoherentBaseChange
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_twoTermComplex_kerMapBaseChange_bijective_ofModules
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cochain_baseChange_equiv_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_zero_ofModules_eq_zero_iff_existsUnique
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_twoTermComplex_sectionsEquiv_forall_baseChange
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace TensorProduct

namespace P2mSectionsBaseChangeH0

section Cover

def coverOfCompact (X : Scheme.{u}) [CompactSpace X] : X.OrderedAffineCover :=
  let 𝒰 := X.affineCover.finiteSubcover
  { ι := 𝒰.I₀
    instFintype := inferInstance
    instLinearOrder := LinearOrder.lift' (Fintype.equivFin 𝒰.I₀) (Fintype.equivFin 𝒰.I₀).injective
    U := fun i => (𝒰.f i).opensRange
    isAffineOpen := fun i => isAffineOpen_opensRange (𝒰.f i)
    iSup_eq_top := 𝒰.iSup_opensRange }

end Cover

section H0

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (M : V.Modules)
  (K : V.OrderedAffineCover)

def toCochain :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
    Γ(M, ⊤) →ₗ[R] (OModulePresheaf.ofModules π M).cochain K 0 :=
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
  LinearMap.pi fun s => (OModulePresheaf.ofModules π M).res (le_top : K.inter s ≤ ⊤)

theorem toCochain_apply (x : Γ(M, ⊤)) (s : K.Idx 0) :
    toCochain π M K x s = M.presheaf.map (homOfLE (le_top : K.inter s ≤ ⊤)).op x := rfl

theorem toCochain_apply' (x : Γ(M, ⊤)) (s : K.Idx 0) :
    toCochain π M K x s = (OModulePresheaf.ofModules π M).res (le_top : K.inter s ≤ ⊤)
      (show (OModulePresheaf.ofModules π M).obj ⊤ from x) := rfl

theorem d_toCochain (x : Γ(M, ⊤)) :
    (OModulePresheaf.ofModules π M).d K 0 (toCochain π M K x) = 0 := by
  funext s
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, toCochain_apply',
    OModulePresheaf.res_res]
  exact add_neg_cancel _

theorem toCochain_mem (x : Γ(M, ⊤)) : toCochain π M K x ∈ (OModulePresheaf.ofModules π M).H0 K :=
  d_toCochain π M K x

theorem toCochain_injective : Function.Injective (toCochain π M K) := by
  intro x y hxy
  obtain ⟨z, -, huniq⟩ := (OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique π M K _).mp
    (d_toCochain π M K x)
  exact (huniq x fun s => rfl).trans (huniq y fun s => by rw [hxy]; rfl).symm

theorem exists_toCochain_eq (c : (OModulePresheaf.ofModules π M).cochain K 0)
    (hc : c ∈ (OModulePresheaf.ofModules π M).H0 K) : ∃ x : Γ(M, ⊤), toCochain π M K x = c := by
  obtain ⟨x, hx, -⟩ := (OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique π M K c).mp hc
  exact ⟨x, funext fun s => (hx s).symm⟩

def sectionsEquivH0 :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
    Γ(M, ⊤) ≃ₗ[R] (OModulePresheaf.ofModules π M).H0 K :=
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
  LinearEquiv.ofBijective (LinearMap.codRestrict ((OModulePresheaf.ofModules π M).H0 K)
      (toCochain π M K) (toCochain_mem π M K))
    ⟨fun x y h => toCochain_injective π M K (congrArg Subtype.val h),
     fun ⟨c, hc⟩ => by
      obtain ⟨x, rfl⟩ := exists_toCochain_eq π M K c hc
      exact ⟨x, rfl⟩⟩

theorem coe_sectionsEquivH0 (x : Γ(M, ⊤)) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
    ((sectionsEquivH0 π M K x : (OModulePresheaf.ofModules π M).H0 K) :
      (OModulePresheaf.ofModules π M).cochain K 0) = toCochain π M K x := rfl

end H0

section Unit

variable {X Y : Scheme.{u}} (p : Y ⟶ X)

lemma app_map {N N' : X.Modules} (φ : N ⟶ N') {W W' : X.Opens} (i : W' ⟶ W) (n : Γ(N, W)) :
    φ.app W' (N.presheaf.map i.op n) = N'.presheaf.map i.op (φ.app W n) := by
  have h := φ.mapPresheaf.naturality i.op
  exact ConcreteCategory.congr_hom h n

lemma map_map (N : X.Modules) {W W' W'' : X.Opens} (i : W' ⟶ W) (j : W'' ⟶ W') (k : W'' ⟶ W)
    (n : Γ(N, W)) :
    N.presheaf.map j.op (N.presheaf.map i.op n) = N.presheaf.map k.op n := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  obtain rfl : k = j ≫ i := Subsingleton.elim _ _
  rfl

abbrev unitApp (M : X.Modules) (U : X.Opens) (e : Γ(M, U)) :
    Γ((Scheme.Modules.pullback p).obj M, p ⁻¹ᵁ U) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app U e

lemma unitApp_map (M : X.Modules) {U W : X.Opens} (i : W ⟶ U) (k : p ⁻¹ᵁ W ⟶ p ⁻¹ᵁ U) (e : Γ(M, U)) :
    unitApp p M W (M.presheaf.map i.op e)
      = ((Scheme.Modules.pullback p).obj M).presheaf.map k.op (unitApp p M U e) := by
  have h := app_map ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) i e
  refine h.trans ?_
  obtain rfl : k = (Opens.map p.base).map i := Subsingleton.elim _ _
  rfl

end Unit

section KerTransfer

variable {R : Type u} [CommRing R]
variable {K0 K1 C0 C1 : Type u} [AddCommGroup K0] [Module R K0] [AddCommGroup K1] [Module R K1]
  [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]

theorem lid_baseChange_apply (f : C0 →ₗ[R] C1) (x : R ⊗[R] C0) :
    TensorProduct.lid R C1 (f.baseChange R x) = f (TensorProduct.lid R C0 x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r m => rw [LinearMap.baseChange_tmul, TensorProduct.lid_tmul, TensorProduct.lid_tmul, map_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

variable (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0) (ι1 : K1 →ₗ[R] C1)
  (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK)

theorem tmul_one_mem_ker {N P : Type u} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : N →ₗ[R] P) (x : LinearMap.ker f) :
    (1 : R) ⊗ₜ[R] (x : N) ∈ LinearMap.ker (f.baseChange R) := by
  rw [LinearMap.mem_ker, LinearMap.baseChange_tmul, LinearMap.mem_ker.mp x.2, tmul_zero]

theorem kerMap_bijective (h : Function.Bijective (TwoChartCech.kerMapBaseChange dK d ι0 ι1 comm R)) :
    Function.Bijective (TwoChartCech.kerMap dK d ι0 ι1 comm) := by
  constructor
  · intro x y hxy
    have hv : ι0 x = ι0 y := congrArg Subtype.val hxy
    have h1 : TwoChartCech.kerMapBaseChange dK d ι0 ι1 comm R ⟨_, tmul_one_mem_ker dK x⟩
        = TwoChartCech.kerMapBaseChange dK d ι0 ι1 comm R ⟨_, tmul_one_mem_ker dK y⟩ := by
      apply Subtype.ext
      change ι0.baseChange R ((1 : R) ⊗ₜ[R] (x : K0)) = ι0.baseChange R ((1 : R) ⊗ₜ[R] (y : K0))
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, hv]
    have h2 := congrArg (fun z => TensorProduct.lid R K0 (Subtype.val z)) (h.1 h1)
    simp only [TensorProduct.lid_tmul, one_smul] at h2
    exact Subtype.ext h2
  · intro y
    obtain ⟨x, hx⟩ := h.2 ⟨_, tmul_one_mem_ker d y⟩
    have hxv : ι0.baseChange R (x : R ⊗[R] K0) = (1 : R) ⊗ₜ[R] (y : C0) := congrArg Subtype.val hx
    refine ⟨⟨TensorProduct.lid R K0 x, ?_⟩, Subtype.ext ?_⟩
    · rw [LinearMap.mem_ker, ← lid_baseChange_apply, LinearMap.mem_ker.mp x.2, map_zero]
    · change ι0 (TensorProduct.lid R K0 x) = y
      rw [← lid_baseChange_apply, hxv, TensorProduct.lid_tmul, one_smul]

end KerTransfer

section KerOfEquiv

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
variable {C0 C1 D0 D1 : Type u} [AddCommGroup C0] [Module A C0] [AddCommGroup C1] [Module A C1]
  [AddCommGroup D0] [Module A D0] [AddCommGroup D1] [Module A D1]

def kerEquivOfEquiv (d : C0 →ₗ[A] C1) (d' : D0 →ₗ[A] D1) (E0 : C0 ≃ₗ[A] D0) (E1 : C1 ≃ₗ[A] D1)
    (h : E1.toLinearMap ∘ₗ d = d' ∘ₗ E0.toLinearMap) :
    LinearMap.ker d ≃ₗ[A] LinearMap.ker d' :=
  (LinearEquiv.ofEq _ _ (by
    rw [← LinearEquiv.ker_comp E1 d, h, LinearMap.ker_comp])).trans (E0.ofSubmodule' (LinearMap.ker d'))

theorem coe_kerEquivOfEquiv (d : C0 →ₗ[A] C1) (d' : D0 →ₗ[A] D1) (E0 : C0 ≃ₗ[A] D0) (E1 : C1 ≃ₗ[A] D1)
    (h : E1.toLinearMap ∘ₗ d = d' ∘ₗ E0.toLinearMap) (x : LinearMap.ker d) :
    (kerEquivOfEquiv d d' E0 E1 h x : D0) = E0 x := rfl

theorem coe_kerEquivOfEquiv_symm (d : C0 →ₗ[A] C1) (d' : D0 →ₗ[A] D1) (E0 : C0 ≃ₗ[A] D0)
    (E1 : C1 ≃ₗ[A] D1) (h : E1.toLinearMap ∘ₗ d = d' ∘ₗ E0.toLinearMap) (y : LinearMap.ker d') :
    ((kerEquivOfEquiv d d' E0 E1 h).symm y : C0) = E0.symm y := by
  set x := (kerEquivOfEquiv d d' E0 E1 h).symm y with hx
  have hy : (kerEquivOfEquiv d d' E0 E1 h) x = y := LinearEquiv.apply_symm_apply _ _
  have hcoe : E0 (x : C0) = (y : D0) := by
    rw [← coe_kerEquivOfEquiv d d' E0 E1 h x, hy]
  rw [← hcoe, LinearEquiv.symm_apply_apply]

end KerOfEquiv

section Main

p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover"

theorem main
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    ∃ (G : CoherentBaseChange.TwoTermComplex.{u, u} R)
      (ε₀ : letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤
        Γ(M, ⊤) ≃ₗ[R] LinearMap.ker G.d)
      (ε : ∀ (A : Type u) [CommRing A] [Algebra R A],
        letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
          (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M) ⊤
        Γ((Scheme.Modules.pullback
            (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M, ⊤) ≃ₗ[A] G.H0 A),
      ∀ (A : Type u) [CommRing A] [Algebra R A] (m : Γ(M, ⊤)),
        ε A (show Γ((Scheme.Modules.pullback
                (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M, ⊤) from
              (((Scheme.Modules.pullbackPushforwardAdjunction
                (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app ⊤) m)
          = G.kerBaseChangeHom A (1 ⊗ₜ[R] ε₀ m) := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 := coverOfCompact X
  let F := OModulePresheaf.ofModules f M
  letI instM := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤

  obtain ⟨G, ι0, ι1, comm, hbij⟩ :=
    OModulePresheaf.exists_twoTermComplex_kerMapBaseChange_bijective_ofModules f M htriv 𝒰

  let eK : LinearMap.ker G.d ≃ₗ[R] F.H0 𝒰 :=
    LinearEquiv.ofBijective (TwoChartCech.kerMap G.d (F.d 𝒰 0) ι0 ι1 comm)
      (kerMap_bijective G.d (F.d 𝒰 0) ι0 ι1 comm (hbij R))
  let ε₀ : Γ(M, ⊤) ≃ₗ[R] LinearMap.ker G.d := (sectionsEquivH0 f M 𝒰).trans eK.symm
  have hε₀ : ∀ m : Γ(M, ⊤), ι0 (ε₀ m : G.C0) = toCochain f M 𝒰 m := by
    intro m
    have h1 : eK (ε₀ m) = sectionsEquivH0 f M 𝒰 m := LinearEquiv.apply_symm_apply _ _
    exact congrArg Subtype.val h1

  have hεA : ∀ (A : Type u) [CommRing A] [Algebra R A],
      ∃ ε :
        (letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
            (Limits.pullback.snd f (specMap R A))
            ((Scheme.Modules.pullback (Limits.pullback.fst f (specMap R A))).obj M) ⊤
         Γ((Scheme.Modules.pullback (Limits.pullback.fst f (specMap R A))).obj M, ⊤) ≃ₗ[A] G.H0 A),
        ∀ m : Γ(M, ⊤),
          ε (show Γ((Scheme.Modules.pullback (Limits.pullback.fst f (specMap R A))).obj M, ⊤) from
              (((Scheme.Modules.pullbackPushforwardAdjunction
                (Limits.pullback.fst f (specMap R A))).unit.app M).app ⊤) m)
            = G.kerBaseChangeHom A (1 ⊗ₜ[R] ε₀ m) := by
    intro A _ _
    let p₁ := Limits.pullback.fst f (specMap R A)
    let p₂ := Limits.pullback.snd f (specMap R A)
    let MA : (Limits.pullback f (specMap R A)).Modules := (Scheme.Modules.pullback p₁).obj M
    let FA := OModulePresheaf.ofModules p₂ MA
    letI instMA := Scheme.TwoAffineOpenCover.moduleSectionsOfHom p₂ MA ⊤

    obtain ⟨E, hEd, hEf⟩ := OModulePresheaf.exists_cochain_baseChange_equiv_of_locallyTrivial f 𝒰 M htriv A

    let e1 : Γ(MA, ⊤) ≃ₗ[A] FA.H0 (𝒰.baseChange f A) := sectionsEquivH0 p₂ MA (𝒰.baseChange f A)
    let e2 : LinearMap.ker ((F.d 𝒰 0).baseChange A) ≃ₗ[A] FA.H0 (𝒰.baseChange f A) :=
      kerEquivOfEquiv ((F.d 𝒰 0).baseChange A) (FA.d (𝒰.baseChange f A) 0) (E 0) (E 1) (hEd 0)
    let e3 : G.H0 A ≃ₗ[A] LinearMap.ker ((F.d 𝒰 0).baseChange A) :=
      LinearEquiv.ofBijective (TwoChartCech.kerMapBaseChange G.d (F.d 𝒰 0) ι0 ι1 comm A) (hbij A)
    refine ⟨e1.trans (e2.symm.trans e3.symm), fun m => ?_⟩

    change e3.symm (e2.symm (e1 _)) = _
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [coe_kerEquivOfEquiv_symm, LinearEquiv.symm_apply_eq]
    change ((e1 _ : FA.H0 (𝒰.baseChange f A)) : FA.cochain (𝒰.baseChange f A) 0)
      = E 0 (ι0.baseChange A ((G.kerBaseChangeHom A (1 ⊗ₜ[R] ε₀ m) : G.H0 A) : A ⊗[R] G.C0))
    rw [CoherentBaseChange.TwoTermComplex.kerBaseChangeHom_apply_coe, LinearMap.baseChange_tmul,
      Submodule.subtype_apply, LinearMap.baseChange_tmul, hε₀ m, coe_sectionsEquivH0]

    funext s
    rw [hEf 0 1 (toCochain f M 𝒰 m) s, one_smul, toCochain_apply, toCochain_apply]
    have h2 := unitApp_map p₁ M (homOfLE (le_top : 𝒰.inter s ≤ ⊤))
      (homOfLE (le_top : p₁ ⁻¹ᵁ 𝒰.inter s ≤ p₁ ⁻¹ᵁ ⊤)) m
    change MA.presheaf.map (homOfLE (le_top : (𝒰.baseChange f A).inter s ≤ ⊤)).op (unitApp p₁ M ⊤ m)
      = FA.res (𝒰.baseChange_inter_le f A s)
        (unitApp p₁ M (𝒰.inter s) (M.presheaf.map (homOfLE (le_top : 𝒰.inter s ≤ ⊤)).op m))
    rw [h2, OModulePresheaf.ofModules_res_apply]
    exact (map_map MA _ _ _ _).symm
  classical
  choose ε hε using hεA
  exact ⟨G, ε₀, fun A _ _ => ε A, fun A _ _ m => hε A m⟩

end Main

end P2mSectionsBaseChangeH0

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    ∃ (G : CoherentBaseChange.TwoTermComplex.{u, u} R)
      (ε₀ : letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤
        Γ(M, ⊤) ≃ₗ[R] LinearMap.ker G.d)
      (ε : ∀ (A : Type u) [CommRing A] [Algebra R A],
        letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
          (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M) ⊤
        Γ((Scheme.Modules.pullback
            (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M, ⊤) ≃ₗ[A] G.H0 A),
      ∀ (A : Type u) [CommRing A] [Algebra R A] (m : Γ(M, ⊤)),
        ε A (show Γ((Scheme.Modules.pullback
                (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M, ⊤) from
              (((Scheme.Modules.pullbackPushforwardAdjunction
                (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app ⊤) m)
          = G.kerBaseChangeHom A (1 ⊗ₜ[R] ε₀ m) :=
  P2mSectionsBaseChangeH0.main f M htriv

end S_AlgebraicGeometry_Scheme_Modules_exists_twoTermComplex_sectionsEquiv_forall_baseChange
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_twoTermComplex_sectionsEquiv_forall_baseChange (solution)
