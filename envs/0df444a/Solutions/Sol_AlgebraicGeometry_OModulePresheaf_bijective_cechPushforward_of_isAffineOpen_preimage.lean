-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.bijective_cechPushforward_of_isAffineOpen_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/c1d4ca8c-c38f-51ef-a5e9-416420cb9561

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_zero_eq_zero_iff_existsUnique_of_isQuasicoherent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.AlgebraicGeometry"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.AlgebraicGeometry TopologicalSpace Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.map_appLE IsLocallyNoetherian Scheme.Opens.ι_image_le Scheme.Opens.topIso_inv Surjective IsProper LocallyOfFiniteType.isLocallyNoetherian Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Hom.image_preimage_eq_opensRange_inf QuasiCompact IsAffine LocallyOfFiniteType Spec Scheme QuasiCompact.compactSpace_of_compactSpace Scheme.Hom.comp_appLE IsAffineOpen.isoSpec_hom_appTop IsSeparated IsLocallyNoetherian.component_noetherian Scheme.Opens.mem_basicOpen_toScheme IsAffineOpen IsNoetherian Scheme.Hom.preimage_iSup Scheme.Opens Scheme.Hom.coe_image Scheme.Hom.appLE_map Scheme.Opens.ι_image_top Scheme.Opens.opensRange_ι morphismRestrict_appLE Scheme.ΓSpecIso OModulePresheaf.cechPushforward.chart_le_preimage OModulePresheaf.cechPushforward Scheme.OrderedAffineCover Scheme.OrderedAffineCover.inter Scheme.OrderedAffineCover.face_val Scheme.OrderedAffineCover.inter_le OModulePresheaf OModulePresheaf.d_apply Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.OrderedAffineCover.fiberAffineOpen"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "cechPushforward.chart_le_preimage cechPushforward.mem_cocycles_iff cechPushforward Hom res_refl_apply res_res cochain d d_apply H0 IsCoherent IsQuasicoherent res res_smul res_refl isScalarTower module obj res_comp addCommGroup moduleSections d_zero_eq_zero_iff_existsUnique_of_isQuasicoherent"
namespace Rebase
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

variable {A : Type u} [CommRing A] {P V' : Scheme.{u}}
  (q : P ⟶ Spec (CommRingCat.of A)) (p : V' ⟶ P) (W : P.affineOpens)

abbrev pW : V'.Opens := p ⁻¹ᵁ (W : P.Opens)

def qW : ((pW p W) : Scheme.{u}) ⟶ Spec (CommRingCat.of Γ(P, (W : P.Opens))) :=
  (p ∣_ (W : P.Opens)) ≫ W.2.isoSpec.hom

theorem qW_def : qW p W = (p ∣_ (W : P.Opens)) ≫ W.2.isoSpec.hom := rfl

abbrev Bch : Type u := Γ(P, (W : P.Opens))

abbrev ΓW (O : ((pW p W) : Scheme.{u}).Opens) : Type u := Γ(((pW p W) : Scheme.{u}), O)

scoped instance isProper_qW [IsProper p] : IsProper (qW p W) := by
  unfold qW; infer_instance

theorem isNoetherian_of_isProper [IsNoetherianRing A] [IsProper q] : IsNoetherian P := by
  haveI : LocallyOfFiniteType q := inferInstance
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of A)) := inferInstance
  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
  haveI : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace q
  exact {}

theorem isNoetherianRing_chart [IsNoetherianRing A] [IsProper q] : IsNoetherianRing Γ(P, (W : P.Opens)) := by
  haveI := isNoetherian_of_isProper q
  exact IsLocallyNoetherian.component_noetherian W

theorem ΓSpecIso_inv_qW_app_map (O : ((pW p W) : Scheme.{u}).Opens) :
    (Scheme.ΓSpecIso (CommRingCat.of Γ(P, (W : P.Opens)))).inv ≫ (qW p W).app ⊤ ≫
        ((pW p W) : Scheme.{u}).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op =
      p.appLE (W : P.Opens) ((pW p W).ι ''ᵁ O) (Scheme.Opens.ι_image_le _ _) := by
  rw [show (qW p W).app ⊤ ≫ ((pW p W) : Scheme.{u}).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op =
      W.2.isoSpec.hom.appTop ≫ (p ∣_ (W : P.Opens)).appLE ⊤ O le_top from
      Scheme.Hom.comp_appLE _ _ ⊤ O le_top,
    IsAffineOpen.isoSpec_hom_appTop,
    show (Scheme.ΓSpecIso (CommRingCat.of Γ(P, (W : P.Opens)))).inv = (Scheme.ΓSpecIso Γ(P, (W : P.Opens))).inv
      from rfl,
    Category.assoc (obj := CommRingCat), Iso.inv_hom_id_assoc, morphismRestrict_appLE, Scheme.Opens.topIso_inv]
  erw [Scheme.Hom.map_appLE]

theorem algebraMap_qW_eq (O : ((pW p W) : Scheme.{u}).Opens) (b : Γ(P, (W : P.Opens))) :
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom (qW p W) O
     algebraMap Γ(P, (W : P.Opens)) Γ(((pW p W) : Scheme.{u}), O) b) =
      (p.appLE (W : P.Opens) ((pW p W).ι ''ᵁ O) (Scheme.Opens.ι_image_le _ _)).hom b := by
  have h := ΓSpecIso_inv_qW_app_map p W O
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) b

theorem map_algebraMap_qW {O O' : ((pW p W) : Scheme.{u}).Opens} (h : O ≤ O') (b : Γ(P, (W : P.Opens))) :
    (((pW p W) : Scheme.{u}).presheaf.map (homOfLE h).op).hom
        (letI := Scheme.TwoAffineOpenCover.algebraOfHom (qW p W) O'
         algebraMap Γ(P, (W : P.Opens)) Γ(((pW p W) : Scheme.{u}), O') b) =
      (letI := Scheme.TwoAffineOpenCover.algebraOfHom (qW p W) O
       algebraMap Γ(P, (W : P.Opens)) Γ(((pW p W) : Scheme.{u}), O) b) := by
  show (((pW p W) : Scheme.{u}).presheaf.map (homOfLE h).op).hom
      (((Scheme.ΓSpecIso (CommRingCat.of Γ(P, (W : P.Opens)))).inv ≫ (qW p W).appLE ⊤ O' le_top).hom b) =
    ((Scheme.ΓSpecIso (CommRingCat.of Γ(P, (W : P.Opens)))).inv ≫ (qW p W).appLE ⊤ O le_top).hom b
  rw [← Scheme.Hom.appLE_map (qW p W) (le_top : O' ≤ (qW p W) ⁻¹ᵁ ⊤) (homOfLE h).op]
  rfl

theorem appLE_algebraMap_chart (O : ((pW p W) : Scheme.{u}).Opens) (a : A) :
    (p.appLE (W : P.Opens) ((pW p W).ι ''ᵁ O) (Scheme.Opens.ι_image_le _ _)).hom
        (letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
         algebraMap A Γ(P, (W : P.Opens)) a) =
      (letI := Scheme.TwoAffineOpenCover.algebraOfHom (p ≫ q) ((pW p W).ι ''ᵁ O)
       algebraMap A Γ(V', (pW p W).ι ''ᵁ O) a) := by
  show ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ (W : P.Opens) le_top ≫
      p.appLE (W : P.Opens) ((pW p W).ι ''ᵁ O) (Scheme.Opens.ι_image_le _ _)).hom a =
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (p ≫ q).appLE ⊤ ((pW p W).ι ''ᵁ O) le_top).hom a
  rw [Scheme.Hom.appLE_comp_appLE]

section Datum

variable (G : OModulePresheaf (p ≫ q))

abbrev modSec (O : ((pW p W) : Scheme.{u}).Opens) : Module (ΓW p W O) (G.obj ((pW p W).ι ''ᵁ O)) :=
  G.moduleSections ((pW p W).ι ''ᵁ O)

attribute [local instance] modSec

abbrev modB (O : ((pW p W) : Scheme.{u}).Opens) : Module (Bch W) (G.obj ((pW p W).ι ''ᵁ O)) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (qW p W) O
  Module.compHom (G.obj ((pW p W).ι ''ᵁ O)) (algebraMap (Bch W) (ΓW p W O))

attribute [local instance] modB

theorem modB_smul_def (O : ((pW p W) : Scheme.{u}).Opens) (b : Bch W) (x : G.obj ((pW p W).ι ''ᵁ O)) :
    b • x = (letI := Scheme.TwoAffineOpenCover.algebraOfHom (qW p W) O; algebraMap (Bch W) (ΓW p W O) b) • x :=
  rfl

theorem modB_smul_def' (O : ((pW p W) : Scheme.{u}).Opens) (b : Bch W) (x : G.obj ((pW p W).ι ''ᵁ O)) :
    b • x = (p.appLE (W : P.Opens) ((pW p W).ι ''ᵁ O) (Scheme.Opens.ι_image_le _ _)).hom b • x := by
  rw [modB_smul_def, algebraMap_qW_eq]
  rfl

theorem isScalarTower_modB (O : ((pW p W) : Scheme.{u}).Opens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (qW p W) O
    IsScalarTower (Bch W) (ΓW p W O) (G.obj ((pW p W).ι ''ᵁ O)) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (qW p W) O
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

theorem res_smul_piece {O O' : ((pW p W) : Scheme.{u}).Opens} (h : O ≤ O') (a : ΓW p W O')
    (x : G.obj ((pW p W).ι ''ᵁ O')) :
    G.res ((pW p W).ι.image_mono h) (a • x) =
      (((pW p W) : Scheme.{u}).presheaf.map (homOfLE h).op).hom a • G.res ((pW p W).ι.image_mono h) x :=
  G.res_smul _ a x

def resW {O O' : ((pW p W) : Scheme.{u}).Opens} (h : O ≤ O') :
    G.obj ((pW p W).ι ''ᵁ O') →ₗ[Bch W] G.obj ((pW p W).ι ''ᵁ O) :=
  { toFun := G.res ((pW p W).ι.image_mono h)
    map_add' := map_add _
    map_smul' := fun b x => by
      rw [RingHom.id_apply, modB_smul_def, modB_smul_def, res_smul_piece q p W G h, map_algebraMap_qW] }

theorem resW_apply {O O' : ((pW p W) : Scheme.{u}).Opens} (h : O ≤ O') (x : G.obj ((pW p W).ι ''ᵁ O')) :
    resW q p W G h x = G.res ((pW p W).ι.image_mono h) x := rfl

theorem resW_smul {O O' : ((pW p W) : Scheme.{u}).Opens} (h : O ≤ O') (a : ΓW p W O')
    (x : G.obj ((pW p W).ι ''ᵁ O')) :
    resW q p W G h (a • x) = (((pW p W) : Scheme.{u}).presheaf.map (homOfLE h).op).hom a • resW q p W G h x :=
  G.res_smul _ a x

theorem resW_refl (O : ((pW p W) : Scheme.{u}).Opens) : resW q p W G (le_refl O) = LinearMap.id :=
  LinearMap.ext fun x => G.res_refl_apply _ x

theorem resW_comp {O O' O'' : ((pW p W) : Scheme.{u}).Opens} (h : O ≤ O') (h' : O' ≤ O'') :
    resW q p W G (h.trans h') = resW q p W G h ∘ₗ resW q p W G h' :=
  LinearMap.ext fun x => (G.res_res _ _ x).symm

def GW : OModulePresheaf (qW p W) where
  obj O := G.obj ((pW p W).ι ''ᵁ O)
  addCommGroup _ := G.addCommGroup _
  module O := modB q p W G O
  moduleSections O := modSec q p W G O
  isScalarTower O := isScalarTower_modB q p W G O
  res h := resW q p W G h
  res_smul h a x := resW_smul q p W G h a x
  res_refl O := resW_refl q p W G O
  res_comp h h' := resW_comp q p W G h h'

theorem GW_obj (O : ((pW p W) : Scheme.{u}).Opens) : (GW q p W G).obj O = G.obj ((pW p W).ι ''ᵁ O) := rfl

theorem GW_res_apply {O O' : ((pW p W) : Scheme.{u}).Opens} (h : O ≤ O') (x : (GW q p W G).obj O') :
    (GW q p W G).res h x = G.res ((pW p W).ι.image_mono h) (show G.obj ((pW p W).ι ''ᵁ O') from x) := rfl

theorem GW_smul_def (O : ((pW p W) : Scheme.{u}).Opens) (b : Bch W) (x : (GW q p W G).obj O) :
    b • x = (show (GW q p W G).obj O from
        (p.appLE (W : P.Opens) ((pW p W).ι ''ᵁ O) (Scheme.Opens.ι_image_le _ _)).hom b •
          (show G.obj ((pW p W).ι ''ᵁ O) from x)) :=
  modB_smul_def' q p W G O b x

abbrev modA (O : ((pW p W) : Scheme.{u}).Opens) : Module A ((GW q p W G).obj O) := G.module ((pW p W).ι ''ᵁ O)

attribute [local instance] modA

theorem algebraMap_smul_GW (O : ((pW p W) : Scheme.{u}).Opens) (a : A) (x : (GW q p W G).obj O) :
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
     algebraMap A (Bch W) a • x) = a • x := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (p ≫ q) ((pW p W).ι ''ᵁ O)
  rw [GW_smul_def, appLE_algebraMap_chart]
  exact algebraMap_smul Γ(V', (pW p W).ι ''ᵁ O) a (show G.obj ((pW p W).ι ''ᵁ O) from x)

theorem isScalarTower_GW (O : ((pW p W) : Scheme.{u}).Opens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
    IsScalarTower A (Bch W) ((GW q p W G).obj O) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
  IsScalarTower.of_algebraMap_smul fun a x => algebraMap_smul_GW q p W G O a x

end Datum

section Cover

variable (K' : V'.OrderedAffineCover)

def KW [IsSeparated q] : Scheme.OrderedAffineCover ((pW p W) : Scheme.{u}) where
  ι := K'.ι
  U i := (pW p W).ι ⁻¹ᵁ K'.U i
  isAffineOpen i := by
    rw [← (pW p W).ι.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, inf_comm]
    exact Scheme.OrderedAffineCover.fiberAffineOpen p q (K'.isAffineOpen i) W.2
  iSup_eq_top := by
    rw [← Scheme.Hom.preimage_iSup, K'.iSup_eq_top]
    rfl

theorem KW_ι [IsSeparated q] : (KW q p W K').ι = K'.ι := rfl

theorem KW_U [IsSeparated q] (i : K'.ι) : (KW q p W K').U i = (pW p W).ι ⁻¹ᵁ K'.U i := rfl

theorem image_KW_U [IsSeparated q] (i : K'.ι) :
    (pW p W).ι ''ᵁ (KW q p W K').U i = K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens) := by
  rw [KW_U, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]

end Cover

section Transfer

variable (G : OModulePresheaf (p ≫ q))

theorem presheaf_res_res {O₁ O₂ O₃ : V'.Opens} (h12 : O₁ ≤ O₂) (h23 : O₂ ≤ O₃) (x : Γ(V', O₃)) :
    (V'.presheaf.map (homOfLE h12).op).hom ((V'.presheaf.map (homOfLE h23).op).hom x) =
      (V'.presheaf.map (homOfLE (h12.trans h23)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← V'.presheaf.map_comp]; rfl

theorem ι_image_basicOpen_piece (O : ((pW p W) : Scheme.{u}).Opens) (r : ΓW p W O) :
    (pW p W).ι ''ᵁ (((pW p W) : Scheme.{u}).basicOpen r) = V'.basicOpen (show Γ(V', (pW p W).ι ''ᵁ O) from r) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact Scheme.Opens.mem_basicOpen_toScheme.1 hy
  · intro hx
    have hxW : x ∈ (pW p W : V'.Opens) :=
      Scheme.Opens.ι_image_le _ _ (V'.basicOpen_le (show Γ(V', (pW p W).ι ''ᵁ O) from r) hx)
    exact ⟨⟨x, hxW⟩, Scheme.Opens.mem_basicOpen_toScheme.2 hx, rfl⟩

theorem isCoherent_GW (hc : G.IsCoherent) : (GW q p W G).IsCoherent := fun O =>
  hc ⟨(pW p W).ι ''ᵁ O.1, O.2.image_of_isOpenImmersion _⟩

theorem isQuasicoherent_GW (hqc : G.IsQuasicoherent) : (GW q p W G).IsQuasicoherent := by
  intro O f
  have hO' : IsAffineOpen ((pW p W).ι ''ᵁ O.1) := O.2.image_of_isOpenImmersion _
  obtain ⟨h1, h2⟩ := hqc ⟨(pW p W).ι ''ᵁ O.1, hO'⟩ (show Γ(V', (pW p W).ι ''ᵁ O.1) from f)
  have e := ι_image_basicOpen_piece p W O.1 f

  have hle₁ : (pW p W).ι ''ᵁ (((pW p W) : Scheme.{u}).basicOpen f) ≤ (pW p W).ι ''ᵁ O.1 :=
    (pW p W).ι.image_mono (((pW p W) : Scheme.{u}).basicOpen_le f)
  have hle₂ : V'.basicOpen (show Γ(V', (pW p W).ι ''ᵁ O.1) from f) ≤ (pW p W).ι ''ᵁ O.1 := V'.basicOpen_le _
  constructor
  · intro x
    obtain ⟨n, y, hy⟩ := h1 (G.res e.ge x)
    refine ⟨n, y, ?_⟩
    have hy' := congrArg (G.res e.le) hy
    rw [G.res_res, G.res_smul, G.res_res, presheaf_res_res] at hy'
    rw [GW_res_apply]
    refine (hy'.trans ?_)
    congr 1
    exact G.res_refl_apply _ x
  · intro y hy0
    apply h2 y
    show G.res hle₂ y = 0
    have : G.res hle₂ y = G.res e.ge (G.res hle₁ y) := (G.res_res _ _ y).symm
    rw [this]
    exact (congrArg (G.res e.ge) hy0).trans (map_zero _)

end Transfer

section Powers

attribute [local instance] modSec modB modA

theorem mem_smul_top_pi_iff {R : Type*} [CommSemiring R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (I : Ideal R) (x : ∀ i, M i) :
    x ∈ I • (⊤ : Submodule R (∀ i, M i)) ↔ ∀ i, x i ∈ I • (⊤ : Submodule R (M i)) := by
  constructor
  · intro hx i
    have h := Submodule.mem_map_of_mem (f := LinearMap.proj (R := R) (φ := M) i) hx
    rw [Submodule.map_smul''] at h
    exact Submodule.smul_mono le_rfl le_top h
  · intro hx
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h := Submodule.mem_map_of_mem (f := LinearMap.single R M i) (hx i)
    rw [Submodule.map_smul''] at h
    exact Submodule.smul_mono le_rfl le_top h

theorem smul_top_mem_map {R : Type*} [CommSemiring R] {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (I : Ideal R) (f : M →ₗ[R] N) {x : M} (hx : x ∈ I • (⊤ : Submodule R M)) :
    f x ∈ I • (⊤ : Submodule R N) := by
  have h := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem mem_map_smul_top_iff {R S M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [AddCommMonoid M]
    [Module R M] [Module S M] [IsScalarTower R S M] (I : Ideal R) (x : M) :
    x ∈ I.map (algebraMap R S) • (⊤ : Submodule S M) ↔ x ∈ I • (⊤ : Submodule R M) := by
  rw [← Submodule.restrictScalars_mem R, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]

variable (G : OModulePresheaf (p ≫ q)) (K' : V'.OrderedAffineCover) (I : Ideal A)

theorem cochain_mem_pow_smul_top_iff [IsSeparated q] (n m : ℕ)
    (x : (GW q p W G).cochain (KW q p W K') n) :
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
     x ∈ (I.map (algebraMap A (Bch W))) ^ m • (⊤ : Submodule (Bch W) ((GW q p W G).cochain (KW q p W K') n))) ↔
      ∀ s, (x s : G.obj ((pW p W).ι ''ᵁ (KW q p W K').inter s)) ∈
        I ^ m • (⊤ : Submodule A (G.obj ((pW p W).ι ''ᵁ (KW q p W K').inter s))) := by
  classical
  letI := Scheme.TwoAffineOpenCover.algebraOfHom q (W : P.Opens)
  rw [← Ideal.map_pow, mem_smul_top_pi_iff]
  refine forall_congr' fun s => ?_
  haveI := isScalarTower_GW q p W G ((KW q p W K').inter s)
  exact mem_map_smul_top_iff (I ^ m) (x s)

end Powers

section Bridge0

variable [IsSeparated q] (G : OModulePresheaf (p ≫ q)) (K' : V'.OrderedAffineCover)

def σ (i : K'.ι) : (KW q p W K').Idx 0 := ⟨fun _ => i, fun a b hab => absurd (Fin.lt_def.mp hab) (by omega)⟩

@[scoped simp] theorem σ_val (i : K'.ι) (k : Fin 1) : (σ q p W K' i).1 k = i := rfl

theorem inter_σ (i : K'.ι) : (KW q p W K').inter (σ q p W K' i) = (KW q p W K').U i := by
  simp only [Scheme.OrderedAffineCover.inter, σ_val]
  exact iInf_const

theorem image_inter_σ (i : K'.ι) :
    (pW p W).ι ''ᵁ (KW q p W K').inter (σ q p W K' i) = (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) := by
  rw [inter_σ, image_KW_U]

theorem image_inter_le {b : ℕ} (s : (KW q p W K').Idx b) (k : Fin (b + 1)) :
    (pW p W).ι ''ᵁ (KW q p W K').inter s ≤ (K'.U (s.1 k) ⊓ p ⁻¹ᵁ (W : P.Opens)) := by
  rw [← image_KW_U q p W K' (s.1 k)]
  exact (pW p W).ι.image_mono (Scheme.OrderedAffineCover.inter_le _ s k)

theorem image_inf (O₁ O₂ : ((pW p W) : Scheme.{u}).Opens) :
    (pW p W).ι ''ᵁ (O₁ ⊓ O₂) = (pW p W).ι ''ᵁ O₁ ⊓ (pW p W).ι ''ᵁ O₂ := by
  apply TopologicalSpace.Opens.ext
  simp only [Scheme.Hom.coe_image, TopologicalSpace.Opens.coe_inf]
  exact Set.image_inter (pW p W).ι.isOpenEmbedding.injective

theorem chW_inf_le_image_inter (s : (KW q p W K').Idx 1) :
    (K'.U (s.1 0) ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U (s.1 1) ⊓ p ⁻¹ᵁ (W : P.Opens)) ≤ (pW p W).ι ''ᵁ (KW q p W K').inter s := by
  rw [← image_KW_U q p W K' (s.1 0), ← image_KW_U q p W K' (s.1 1), ← image_inf]
  refine (pW p W).ι.image_mono (le_iInf fun k => ?_)
  fin_cases k
  · exact inf_le_left
  · exact inf_le_right

theorem image_inter_le_inf (s : (KW q p W K').Idx 1) :
    (pW p W).ι ''ᵁ (KW q p W K').inter s ≤ (K'.U (s.1 0) ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U (s.1 1) ⊓ p ⁻¹ᵁ (W : P.Opens)) :=
  le_inf (image_inter_le q p W K' s 0) (image_inter_le q p W K' s 1)

def e0 (x : (GW q p W G).cochain (KW q p W K') 0) (i : K'.ι) : G.obj ((K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))) :=
  G.res (image_inter_σ q p W K' i).ge
    (show G.obj ((pW p W).ι ''ᵁ (KW q p W K').inter (σ q p W K' i)) from x (σ q p W K' i))

theorem e0_apply (x : (GW q p W G).cochain (KW q p W K') 0) (i : K'.ι) :
    e0 q p W G K' x i = G.res (image_inter_σ q p W K' i).ge
      (show G.obj ((pW p W).ι ''ᵁ (KW q p W K').inter (σ q p W K' i)) from x (σ q p W K' i)) := rfl

theorem e0_add (x y : (GW q p W G).cochain (KW q p W K') 0) :
    e0 q p W G K' (x + y) = e0 q p W G K' x + e0 q p W G K' y :=
  funext fun _ => map_add (G.res _) _ _

theorem e0_zero : e0 q p W G K' (0 : (GW q p W G).cochain (KW q p W K') 0) = 0 :=
  funext fun _ => map_zero (G.res _)

theorem e0_neg (x : (GW q p W G).cochain (KW q p W K') 0) :
    e0 q p W G K' (-x) = -e0 q p W G K' x :=
  funext fun _ => map_neg (G.res _) _

theorem e0_sub (x y : (GW q p W G).cochain (KW q p W K') 0) :
    e0 q p W G K' (x - y) = e0 q p W G K' x - e0 q p W G K' y :=
  funext fun _ => map_sub (G.res _) _ _

def e0Hom : (GW q p W G).cochain (KW q p W K') 0 →+ (∀ i : K'.ι, G.obj ((K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)))) where
  toFun := e0 q p W G K'
  map_zero' := e0_zero q p W G K'
  map_add' := e0_add q p W G K'

@[scoped simp] theorem e0Hom_apply (x : (GW q p W G).cochain (KW q p W K') 0) :
    e0Hom q p W G K' x = e0 q p W G K' x := rfl

theorem e0_smulB (b : Bch W) (x : (GW q p W G).cochain (KW q p W K') 0) (i : K'.ι) :
    e0 q p W G K' (b • x) i =
      (p.appLE (W : P.Opens) ((K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right).hom b • e0 q p W G K' x i := by
  rw [e0_apply, e0_apply, Pi.smul_apply, GW_smul_def]
  erw [G.res_smul]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem e0_smulA (a : A) (x : (GW q p W G).cochain (KW q p W K') 0) (i : K'.ι) :
    e0 q p W G K' (fun s => (letI := modA q p W G ((KW q p W K').inter s); a • x s)) i =
      a • e0 q p W G K' x i :=
  LinearMap.map_smul (G.res _) a _

def e0inv (y : ∀ i : K'.ι, G.obj ((K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)))) : (GW q p W G).cochain (KW q p W K') 0 :=
  fun s => show G.obj ((pW p W).ι ''ᵁ (KW q p W K').inter s) from
    G.res (image_inter_le q p W K' s 0) (y (s.1 0))

theorem e0_e0inv (y : ∀ i : K'.ι, G.obj ((K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)))) : e0 q p W G K' (e0inv q p W G K' y) = y := by
  funext i
  show G.res _ (G.res _ (y i)) = y i
  rw [G.res_res]
  exact G.res_refl_apply _ _

theorem e0_surjective : Function.Surjective (e0 q p W G K') :=
  fun y => ⟨e0inv q p W G K' y, e0_e0inv q p W G K' y⟩

theorem res_congr_idx (x : (GW q p W G).cochain (KW q p W K') 0) {t t' : (KW q p W K').Idx 0} (h : t = t')
    {O : V'.Opens} (h1 : O ≤ (pW p W).ι ''ᵁ (KW q p W K').inter t) :
    G.res h1 (show G.obj ((pW p W).ι ''ᵁ (KW q p W K').inter t) from x t) =
      G.res (h ▸ h1) (show G.obj ((pW p W).ι ''ᵁ (KW q p W K').inter t') from x t') := by
  subst h; rfl

theorem face_zero_eq (s : (KW q p W K').Idx 1) : (KW q p W K').face s 0 = σ q p W K' (s.1 1) :=
  Subtype.ext (funext fun k => by
    rw [Scheme.OrderedAffineCover.face_val, σ_val, Function.comp_apply, Fin.fin_one_eq_zero k]
    rfl)

theorem face_one_eq (s : (KW q p W K').Idx 1) : (KW q p W K').face s 1 = σ q p W K' (s.1 0) :=
  Subtype.ext (funext fun k => by
    rw [Scheme.OrderedAffineCover.face_val, σ_val, Function.comp_apply, Fin.fin_one_eq_zero k]
    rfl)

theorem d0_apply (x : (GW q p W G).cochain (KW q p W K') 0) (s : (KW q p W K').Idx 1) :
    (GW q p W G).d (KW q p W K') 0 x s =
      (GW q p W G).res ((KW q p W K').inter_le_inter_face s 0) (x ((KW q p W K').face s 0)) -
        (GW q p W G).res ((KW q p W K').inter_le_inter_face s 1) (x ((KW q p W K').face s 1)) := by
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, sub_eq_add_neg]

def σ₂ {i j : K'.ι} (hij : i < j) : (KW q p W K').Idx 1 :=
  ⟨![i, j], Fin.strictMono_iff_lt_succ.mpr fun k => by fin_cases k; exact hij⟩

theorem σ₂_fst {i j : K'.ι} (hij : i < j) : (σ₂ q p W K' hij).1 0 = i := rfl
theorem σ₂_snd {i j : K'.ι} (hij : i < j) : (σ₂ q p W K' hij).1 1 = j := rfl

theorem d0_eq_zero_iff (x : (GW q p W G).cochain (KW q p W K') 0) :
    (GW q p W G).d (KW q p W K') 0 x = 0 ↔ ∀ i j : K'.ι,
      G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left (e0 q p W G K' x i)
        = G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right (e0 q p W G K' x j) := by
  constructor
  · intro hd i j
    have key : ∀ s : (KW q p W K').Idx 1,
        G.res (U := (K'.U (s.1 0) ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U (s.1 1) ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left
            (e0 q p W G K' x (s.1 0))
          = G.res (U := (K'.U (s.1 0) ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U (s.1 1) ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right
            (e0 q p W G K' x (s.1 1)) := by
      intro s
      have hs := congrFun hd s
      rw [Pi.zero_apply, d0_apply, sub_eq_zero] at hs
      rw [GW_res_apply, GW_res_apply] at hs
      rw [res_congr_idx q p W G K' x (face_zero_eq q p W K' s)] at hs
      rw [res_congr_idx q p W G K' x (face_one_eq q p W K' s)] at hs
      have hs' := congrArg (G.res (chW_inf_le_image_inter q p W K' s)) hs
      rw [G.res_res, G.res_res] at hs'
      rw [e0_apply, e0_apply, G.res_res, G.res_res]
      exact hs'.symm
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact key (σ₂ q p W K' hij)
    · rfl
    · have hk : G.res (U := (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left
              (e0 q p W G K' x j)
            = G.res (U := (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right
              (e0 q p W G K' x i) := key (σ₂ q p W K' hji)
      have h := congrArg (G.res (le_inf inf_le_right inf_le_left :
          (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens)) ≤
            (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)))) hk
      rw [G.res_res, G.res_res] at h
      exact h.symm
  · intro h
    funext s
    have hs := congrArg (G.res (image_inter_le_inf q p W K' s)) (h (s.1 0) (s.1 1))
    rw [e0_apply, e0_apply, G.res_res, G.res_res, G.res_res, G.res_res] at hs
    rw [Pi.zero_apply, d0_apply, sub_eq_zero]
    rw [GW_res_apply, GW_res_apply]
    rw [res_congr_idx q p W G K' x (face_zero_eq q p W K' s)]
    rw [res_congr_idx q p W G K' x (face_one_eq q p W K' s)]
    exact hs.symm

theorem mem_H0_iff (x : (GW q p W G).cochain (KW q p W K') 0) :
    x ∈ (GW q p W G).H0 (KW q p W K') ↔ ∀ i j : K'.ι,
      G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_left (e0 q p W G K' x i)
        = G.res (U := (K'.U i ⊓ p ⁻¹ᵁ (W : P.Opens)) ⊓ (K'.U j ⊓ p ⁻¹ᵁ (W : P.Opens))) inf_le_right (e0 q p W G K' x j) := by
  rw [LinearMap.mem_ker, d0_eq_zero_iff]

end Bridge0

end AlgebraicGeometry.OModulePresheaf.Rebase
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.AlgebraicGeometry.OModulePresheaf P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.AlgebraicGeometry.OModulePresheaf.Rebase"
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.AlgebraicGeometry.OModulePresheaf"
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.AlgebraicGeometry"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.AlgebraicGeometry.OModulePresheaf P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.AlgebraicGeometry.OModulePresheaf.Rebase"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.map_appLE IsLocallyNoetherian Scheme.Opens.ι_image_le Scheme.Opens.topIso_inv Surjective IsProper LocallyOfFiniteType.isLocallyNoetherian Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Hom.image_preimage_eq_opensRange_inf QuasiCompact IsAffine LocallyOfFiniteType Spec Scheme QuasiCompact.compactSpace_of_compactSpace Scheme.Hom.comp_appLE IsAffineOpen.isoSpec_hom_appTop IsSeparated IsLocallyNoetherian.component_noetherian Scheme.Opens.mem_basicOpen_toScheme IsAffineOpen IsNoetherian Scheme.Hom.preimage_iSup Scheme.Opens Scheme.Hom.coe_image Scheme.Hom.appLE_map Scheme.Opens.ι_image_top Scheme.Opens.opensRange_ι morphismRestrict_appLE Scheme.ΓSpecIso OModulePresheaf.cechPushforward.chart_le_preimage OModulePresheaf.cechPushforward Scheme.OrderedAffineCover Scheme.OrderedAffineCover.inter Scheme.OrderedAffineCover.face_val Scheme.OrderedAffineCover.inter_le OModulePresheaf OModulePresheaf.d_apply Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.OrderedAffineCover.fiberAffineOpen"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "cechPushforward.chart_le_preimage cechPushforward.mem_cocycles_iff cechPushforward Hom res_refl_apply res_res cochain d d_apply H0 IsCoherent IsQuasicoherent res res_smul res_refl isScalarTower module obj res_comp addCommGroup moduleSections d_zero_eq_zero_iff_existsUnique_of_isQuasicoherent"
namespace CechAffine
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

open Rebase

variable {A : Type u} [CommRing A] {P V' : Scheme.{u}}
  (q : P ⟶ Spec (CommRingCat.of A)) (p : V' ⟶ P) (W : P.affineOpens)

scoped instance isSeparated_qW [IsSeparated p] : IsSeparated (qW p W) := by
  unfold qW; infer_instance

theorem image_top : (pW p W).ι ''ᵁ ⊤ = pW p W := Scheme.Opens.ι_image_top _

theorem le_image_top : pW p W ≤ (pW p W).ι ''ᵁ ⊤ := (image_top p W).ge
theorem image_top_le : (pW p W).ι ''ᵁ ⊤ ≤ pW p W := (image_top p W).le

end AlgebraicGeometry.OModulePresheaf.CechAffine
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.AlgebraicGeometry.OModulePresheaf P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.AlgebraicGeometry.OModulePresheaf.Rebase P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.AlgebraicGeometry.OModulePresheaf.CechAffine"
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.AlgebraicGeometry.OModulePresheaf P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.AlgebraicGeometry.OModulePresheaf.Rebase"
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.AlgebraicGeometry.OModulePresheaf P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.AlgebraicGeometry.OModulePresheaf.Rebase"

open _root_.AlgebraicGeometry.OModulePresheaf _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.AlgebraicGeometry.OModulePresheaf AlgebraicGeometry.OModulePresheaf.Rebase AlgebraicGeometry.OModulePresheaf.CechAffine in

theorem solution
    {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsSeparated q]
    {V' : Scheme.{u}} (p : V' ⟶ P) [IsSeparated p] (K' : V'.OrderedAffineCover)
    (G : OModulePresheaf (p ≫ q)) (hqc : G.IsQuasicoherent)
    (W : P.affineOpens) (hW : IsAffineOpen (p ⁻¹ᵁ W.1)) :
    (∀ x y : G.obj (p ⁻¹ᵁ W.1),
        (∀ j : K'.ι, G.res (OModulePresheaf.cechPushforward.chart_le_preimage p K' W.1 j) x
          = G.res (OModulePresheaf.cechPushforward.chart_le_preimage p K' W.1 j) y) → x = y) ∧
      ∀ c : (OModulePresheaf.cechPushforward p q K' G).obj W.1,
        ∃ x : G.obj (p ⁻¹ᵁ W.1), ∀ j : K'.ι,
          c.1 j = G.res (OModulePresheaf.cechPushforward.chart_le_preimage p K' W.1 j) x := by
  classical
  haveI : IsAffine (pW p W) := hW
  have hqW := isQuasicoherent_GW q p W G hqc
  have hle : ∀ (s : (KW q p W K').Idx 0),
      (pW p W).ι ''ᵁ (KW q p W K').inter s ≤ K'.U (s.1 0) ⊓ p ⁻¹ᵁ (W : P.Opens) := fun s =>
    image_inter_le q p W K' s 0
  refine ⟨fun x y hxy => ?_, fun c => ?_⟩
  ·
    let x' : (GW q p W G).obj ⊤ := show G.obj ((pW p W).ι ''ᵁ ⊤) from G.res (image_top_le p W) x
    let y' : (GW q p W G).obj ⊤ := show G.obj ((pW p W).ι ''ᵁ ⊤) from G.res (image_top_le p W) y
    let c : (GW q p W G).cochain (KW q p W K') 0 := fun s => (GW q p W G).res le_top x'
    have hc : (GW q p W G).d (KW q p W K') 0 c = 0 := by
      refine (d0_eq_zero_iff q p W G K' c).2 fun i j => ?_
      simp only [e0_apply, c, GW_res_apply, x']
      rw [G.res_res, G.res_res, G.res_res, G.res_res, G.res_res, G.res_res]
    obtain ⟨z, hz, huniq⟩ :=
      (d_zero_eq_zero_iff_existsUnique_of_isQuasicoherent (GW q p W G) hqW (KW q p W K') c).1 hc
    have hx : x' = z := huniq x' fun s => rfl
    have hy : y' = z := huniq y' fun s => by
      show (GW q p W G).res le_top x' = (GW q p W G).res le_top y'
      rw [GW_res_apply, GW_res_apply]
      show G.res _ (G.res _ x) = G.res _ (G.res _ y)
      rw [G.res_res, G.res_res,
        ← G.res_res (hle s) (cechPushforward.chart_le_preimage p K' W.1 (s.1 0)),
        ← G.res_res (hle s) (cechPushforward.chart_le_preimage p K' W.1 (s.1 0)), hxy (s.1 0)]
    have hxy' : x' = y' := hx.trans hy.symm
    have hx2 : x = G.res (le_image_top p W) (show G.obj ((pW p W).ι ''ᵁ ⊤) from x') := by
      show x = G.res _ (G.res _ x); rw [G.res_res]; exact (G.res_refl_apply _ x).symm
    have hy2 : y = G.res (le_image_top p W) (show G.obj ((pW p W).ι ''ᵁ ⊤) from y') := by
      show y = G.res _ (G.res _ y); rw [G.res_res]; exact (G.res_refl_apply _ y).symm
    rw [hx2, hy2, hxy']
  ·
    let x₀ : (GW q p W G).cochain (KW q p W K') 0 := e0inv q p W G K' c.1
    have hx₀ : e0 q p W G K' x₀ = c.1 := e0_e0inv q p W G K' c.1
    have hd : (GW q p W G).d (KW q p W K') 0 x₀ = 0 := by
      refine (d0_eq_zero_iff q p W G K' x₀).2 ?_
      rw [hx₀]
      exact (cechPushforward.mem_cocycles_iff p q K' G W.1 c.1).1 c.2
    obtain ⟨z, hz, -⟩ :=
      (d_zero_eq_zero_iff_existsUnique_of_isQuasicoherent (GW q p W G) hqW (KW q p W K') x₀).1 hd
    refine ⟨G.res (le_image_top p W) (show G.obj ((pW p W).ι ''ᵁ ⊤) from z), fun j => ?_⟩
    rw [← hx₀, e0_apply, G.res_res]
    show G.res _ (x₀ (σ q p W K' j)) = _
    rw [hz (σ q p W K' j), GW_res_apply, G.res_res]

end S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage (solution)
