-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_TateLow
-- name    : GroundTheory_TateCohomology_TateLow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:00:08.748636+00:00
-- url     : https://prove2.me/theorems/5ed9fcee-0520-478a-85e8-2829b6604f1c
-- title:
--   Tate Low
-- statement:
--   Definitions and structural lemmas for Tate Low, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateLow.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ModuleHomologyData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.GroupCoh
open CategoryTheory Limits Representation groupCohomology groupHomology
universe u
section Tate
variable {R G : Type u} [CommRing R] [Group G] [Fintype G]
lemma iso_hom_inv_apply {A B : ModuleCat.{u} R} (e : A ≅ B) (x : B) :
    e.hom.hom (e.inv.hom x) = x := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Iso.inv_hom_id]
  rfl
lemma iso_inv_hom_apply {A B : ModuleCat.{u} R} (e : A ≅ B) (x : A) :
    e.inv.hom (e.hom.hom x) = x := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Iso.hom_inv_id]
  rfl
lemma iso_hom_injective {A B : ModuleCat.{u} R} (e : A ≅ B) : Function.Injective e.hom.hom :=
  fun a b h => by rw [← iso_inv_hom_apply e a, h, iso_inv_hom_apply]
lemma iso_inv_injective {A B : ModuleCat.{u} R} (e : A ≅ B) : Function.Injective e.inv.hom :=
  fun a b h => by rw [← iso_hom_inv_apply e a, h, iso_hom_inv_apply]
lemma repHom_norm_apply {X Y : Rep.{u} R G} (f : X ⟶ Y) (m : X) :
    f.hom (X.ρ.norm m) = Y.ρ.norm (f.hom m) := by
  simp [Representation.norm, map_sum, Rep.hom_comm_apply]
omit [Fintype G] in

lemma coinvariantsKer_le_comap {X Y : Rep.{u} R G} (f : X ⟶ Y) :
    Coinvariants.ker X.ρ ≤ (Coinvariants.ker Y.ρ).comap f.hom.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨g, m⟩, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap]
  have : f.hom.toLinearMap (X.ρ g m - m) = Y.ρ g (f.hom m) - f.hom m := by
    simp [Rep.hom_comm_apply]
  rw [this]
  exact Coinvariants.sub_mem_ker g _
noncomputable def normRangeInvariants (M : Rep.{u} R G) : Submodule R M.ρ.invariants :=
  (LinearMap.range M.ρ.norm).comap M.ρ.invariants.subtype
noncomputable def augmentationKerNorm (M : Rep.{u} R G) : Submodule R (LinearMap.ker M.ρ.norm) :=
  (Coinvariants.ker M.ρ).comap (LinearMap.ker M.ρ.norm).subtype
lemma mem_augmentationKerNorm_iff (M : Rep.{u} R G) (x : LinearMap.ker M.ρ.norm) :
    x ∈ augmentationKerNorm M ↔ (x : M) ∈ Coinvariants.ker M.ρ := Iff.rfl
variable (R G) in

noncomputable def tateZeroFunctor : Rep.{u} R G ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (M.ρ.invariants ⧸ normRangeInvariants M)
  map {X Y} f := ModuleCat.ofHom (Submodule.mapQ _ _ ((Rep.invariantsFunctor R G).map f).hom (by
    rintro x ⟨m, hm⟩
    exact ⟨f.hom m, by rw [← repHom_norm_apply, hm]; rfl⟩))
  map_id X := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl
noncomputable def kerNormMap {X Y : Rep.{u} R G} (f : X ⟶ Y) :
    LinearMap.ker X.ρ.norm →ₗ[R] LinearMap.ker Y.ρ.norm :=
  f.hom.toLinearMap.restrict (fun x hx => by
    simp only [LinearMap.mem_ker] at hx ⊢
    rw [show f.hom.toLinearMap x = f.hom x from rfl, ← repHom_norm_apply, hx, map_zero])
@[simp]
lemma kerNormMap_apply {X Y : Rep.{u} R G} (f : X ⟶ Y) (x : LinearMap.ker X.ρ.norm) :
    (kerNormMap f x : Y) = f.hom x := rfl
variable (R G) in

noncomputable def tateNegOneFunctor : Rep.{u} R G ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (LinearMap.ker M.ρ.norm ⧸ augmentationKerNorm M)
  map {X Y} f := ModuleCat.ofHom (Submodule.mapQ _ _ (kerNormMap f) (fun x hx =>
    coinvariantsKer_le_comap f hx))
  map_id X := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl
@[simp]
lemma tateZeroFunctor_obj (M : Rep.{u} R G) :
    (tateZeroFunctor R G).obj M = ModuleCat.of R (M.ρ.invariants ⧸ normRangeInvariants M) := rfl
@[simp]
lemma tateZeroFunctor_map_mk {X Y : Rep.{u} R G} (f : X ⟶ Y) (x : X.ρ.invariants) :
    ((tateZeroFunctor R G).map f).hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (((Rep.invariantsFunctor R G).map f).hom x) := rfl
@[simp]
lemma tateNegOneFunctor_obj (M : Rep.{u} R G) :
    (tateNegOneFunctor R G).obj M =
      ModuleCat.of R (LinearMap.ker M.ρ.norm ⧸ augmentationKerNorm M) := rfl
@[simp]
lemma tateNegOneFunctor_map_mk {X Y : Rep.{u} R G} (f : X ⟶ Y) (x : LinearMap.ker X.ρ.norm) :
    ((tateNegOneFunctor R G).map f).hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (kerNormMap f x) := rfl
end Tate
section TateIsos
variable {R G : Type u} [CommRing R] [Group G] [Fintype G]
lemma normRangeInvariants_le_comap {X Y : Rep.{u} R G} (f : X ⟶ Y) :
    normRangeInvariants X ≤ (normRangeInvariants Y).comap ((Rep.invariantsFunctor R G).map f).hom := by
  rintro x ⟨m, hm⟩
  exact ⟨f.hom m, by rw [← repHom_norm_apply, hm]; rfl⟩
noncomputable def tateZeroι (M : Rep.{u} R G) :
    M.ρ.invariants →ₗ[R] ((tateComplex M).sc' (-1) 0 1).X₂ :=
  (cochainsIso₀ M).inv.hom ∘ₗ M.ρ.invariants.subtype
lemma tateZeroι_injective (M : Rep.{u} R G) : Function.Injective (tateZeroι M) :=
  (iso_inv_injective (cochainsIso₀ M)).comp Subtype.val_injective
lemma tateZeroι_range (M : Rep.{u} R G) :
    LinearMap.range (tateZeroι M) = LinearMap.ker ((tateComplex M).sc' (-1) 0 1).g.hom := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    have e : ((inhomogeneousCochains M).d 0 1).hom ((cochainsIso₀ M).inv.hom x.1) =
        (cochainsIso₁ M).inv.hom ((d₀₁ M).hom x.1) := congr(($(eq_d₀₁_comp_inv M)).hom x.1)
    have hx : (d₀₁ M).hom x.1 = 0 := by
      have : x.1 ∈ LinearMap.ker (d₀₁ M).hom := by
        rw [d₀₁_ker_eq_invariants]
        exact x.2
      exact LinearMap.mem_ker.1 this
    rw [LinearMap.mem_ker]
    change ((inhomogeneousCochains M).d 0 1).hom ((cochainsIso₀ M).inv.hom x.1) = 0
    rw [e, hx, map_zero]
  · intro hy
    have hy' : ((inhomogeneousCochains M).d 0 1).hom y = 0 := LinearMap.mem_ker.1 hy
    have e : (d₀₁ M).hom ((cochainsIso₀ M).hom.hom y) =
        (cochainsIso₁ M).hom.hom (((inhomogeneousCochains M).d 0 1).hom y) :=
      congr(($(comp_d₀₁_eq M)).hom y)
    have hmem : (cochainsIso₀ M).hom.hom y ∈ M.ρ.invariants := by
      rw [← d₀₁_ker_eq_invariants, LinearMap.mem_ker, e, hy', map_zero]
    exact ⟨⟨_, hmem⟩, iso_inv_hom_apply (cochainsIso₀ M) y⟩
lemma tateZero_mem_iff (M : Rep.{u} R G) (x : M.ρ.invariants) :
    x ∈ normRangeInvariants M ↔
      tateZeroι M x ∈ LinearMap.range ((tateComplex M).sc' (-1) 0 1).f.hom := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨(chainsIso₀ M).inv.hom m, ?_⟩
    change (cochainsIso₀ M).inv.hom (M.ρ.norm ((chainsIso₀ M).hom.hom ((chainsIso₀ M).inv.hom m))) =
      (cochainsIso₀ M).inv.hom x.1
    rw [iso_hom_inv_apply, hm]
    rfl
  · rintro ⟨c, hc⟩
    refine ⟨(chainsIso₀ M).hom.hom c, ?_⟩
    have hc' : (cochainsIso₀ M).inv.hom (M.ρ.norm ((chainsIso₀ M).hom.hom c)) =
        (cochainsIso₀ M).inv.hom x.1 := hc
    exact iso_inv_injective _ hc'
noncomputable def tateZeroData (M : Rep.{u} R G) :
    ((tateComplex M).sc' (-1) 0 1).LeftHomologyData :=
  moduleLeftHomologyData _ M.ρ.invariants (tateZeroι M) (tateZeroι_injective M)
    (tateZeroι_range M) (normRangeInvariants M) (tateZero_mem_iff M)
noncomputable def tateZeroMapData {X Y : Rep.{u} R G} (f : X ⟶ Y) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor' _ _ (-1) 0 1).map
        ((tateComplexFunctor R G).map f)) (tateZeroData X) (tateZeroData Y) :=
  moduleLeftHomologyMapData _ _ _ _ _ _ _ _ _ _ _ _ _ ((Rep.invariantsFunctor R G).map f).hom
    (fun x => by
      have e : (cochainsIso₀ Y).hom.hom
          (((cochainsMap (MonoidHom.id G) f).f 0).hom ((cochainsIso₀ X).inv.hom x.1)) =
          f.hom ((cochainsIso₀ X).hom.hom ((cochainsIso₀ X).inv.hom x.1)) :=
        congr(($(cochainsMap_f_0_comp_cochainsIso₀ (f := MonoidHom.id G) (φ := f))).hom
          ((cochainsIso₀ X).inv.hom x.1))
      apply iso_hom_injective (cochainsIso₀ Y)
      change (cochainsIso₀ Y).hom.hom ((cochainsIso₀ Y).inv.hom (f.hom x.1)) =
        (cochainsIso₀ Y).hom.hom
          (((cochainsMap (MonoidHom.id G) f).f 0).hom ((cochainsIso₀ X).inv.hom x.1))
      rw [e, iso_hom_inv_apply, iso_hom_inv_apply])
    (normRangeInvariants_le_comap f)
variable (R G) in

noncomputable def tateCohomologyZeroIso :
    tateCohomologyFunctor (R := R) (G := G) 0 ≅ tateZeroFunctor R G :=
  Functor.isoWhiskerLeft (tateComplexFunctor R G)
      (HomologicalComplex.homologyFunctorIso' (ModuleCat.{u} R) (ComplexShape.up ℤ) (-1) 0 1
        (by simp) (by simp)) ≪≫
    NatIso.ofComponents (fun M => (tateZeroData M).homologyIso)
      (fun {X Y} f => (tateZeroMapData f).homologyMap_comm)
noncomputable def tateNegOneι (M : Rep.{u} R G) :
    LinearMap.ker M.ρ.norm →ₗ[R] ((tateComplex M).sc' (-2) (-1) 0).X₂ :=
  (chainsIso₀ M).inv.hom ∘ₗ (LinearMap.ker M.ρ.norm).subtype
lemma tateNegOneι_injective (M : Rep.{u} R G) : Function.Injective (tateNegOneι M) :=
  (iso_inv_injective (chainsIso₀ M)).comp Subtype.val_injective
lemma tateNegOneι_range (M : Rep.{u} R G) :
    LinearMap.range (tateNegOneι M) = LinearMap.ker ((tateComplex M).sc' (-2) (-1) 0).g.hom := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    change (cochainsIso₀ M).inv.hom
      (M.ρ.norm ((chainsIso₀ M).hom.hom ((chainsIso₀ M).inv.hom x.1))) = 0
    rw [iso_hom_inv_apply, LinearMap.mem_ker.1 x.2, map_zero]
  · intro hy
    have hy' : (cochainsIso₀ M).inv.hom (M.ρ.norm ((chainsIso₀ M).hom.hom y)) = 0 :=
      LinearMap.mem_ker.1 hy
    have hmem : (chainsIso₀ M).hom.hom y ∈ LinearMap.ker M.ρ.norm := by
      rw [LinearMap.mem_ker]
      apply iso_inv_injective (cochainsIso₀ M)
      rw [hy', map_zero]
    exact ⟨⟨_, hmem⟩, iso_inv_hom_apply (chainsIso₀ M) y⟩
lemma tateNegOne_mem_iff (M : Rep.{u} R G) (x : LinearMap.ker M.ρ.norm) :
    x ∈ augmentationKerNorm M ↔
      tateNegOneι M x ∈ LinearMap.range ((tateComplex M).sc' (-2) (-1) 0).f.hom := by
  rw [mem_augmentationKerNorm_iff, ← range_d₁₀_eq_coinvariantsKer]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨(chainsIso₁ M).inv.hom w, ?_⟩
    change ((inhomogeneousChains M).d 1 0).hom ((chainsIso₁ M).inv.hom w) =
      (chainsIso₀ M).inv.hom x.1
    apply iso_hom_injective (chainsIso₀ M)
    have e : (d₁₀ M).hom ((chainsIso₁ M).hom.hom ((chainsIso₁ M).inv.hom w)) =
        (chainsIso₀ M).hom.hom (((inhomogeneousChains M).d 1 0).hom ((chainsIso₁ M).inv.hom w)) :=
      congr(($(comp_d₁₀_eq M)).hom ((chainsIso₁ M).inv.hom w))
    rw [← e, iso_hom_inv_apply, iso_hom_inv_apply, hw]
  · rintro ⟨c, hc⟩
    have hc' : ((inhomogeneousChains M).d 1 0).hom c = (chainsIso₀ M).inv.hom x.1 := hc
    refine ⟨(chainsIso₁ M).hom.hom c, ?_⟩
    have e : (d₁₀ M).hom ((chainsIso₁ M).hom.hom c) =
        (chainsIso₀ M).hom.hom (((inhomogeneousChains M).d 1 0).hom c) :=
      congr(($(comp_d₁₀_eq M)).hom c)
    rw [e, hc', iso_hom_inv_apply]
noncomputable def tateNegOneData (M : Rep.{u} R G) :
    ((tateComplex M).sc' (-2) (-1) 0).LeftHomologyData :=
  moduleLeftHomologyData _ (LinearMap.ker M.ρ.norm) (tateNegOneι M) (tateNegOneι_injective M)
    (tateNegOneι_range M) (augmentationKerNorm M) (tateNegOne_mem_iff M)
noncomputable def tateNegOneMapData {X Y : Rep.{u} R G} (f : X ⟶ Y) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor' _ _ (-2) (-1) 0).map
        ((tateComplexFunctor R G).map f)) (tateNegOneData X) (tateNegOneData Y) :=
  moduleLeftHomologyMapData _ _ _ _ _ _ _ _ _ _ _ _ _ (kerNormMap f)
    (fun x => by
      have e : (chainsIso₀ Y).hom.hom
          (((chainsMap (MonoidHom.id G) f).f 0).hom ((chainsIso₀ X).inv.hom x.1)) =
          f.hom ((chainsIso₀ X).hom.hom ((chainsIso₀ X).inv.hom x.1)) :=
        congr(($(chainsMap_f_0_comp_chainsIso₀ (f := MonoidHom.id G) (φ := f))).hom
          ((chainsIso₀ X).inv.hom x.1))
      apply iso_hom_injective (chainsIso₀ Y)
      change (chainsIso₀ Y).hom.hom ((chainsIso₀ Y).inv.hom (f.hom x.1)) =
        (chainsIso₀ Y).hom.hom
          (((chainsMap (MonoidHom.id G) f).f 0).hom ((chainsIso₀ X).inv.hom x.1))
      rw [e, iso_hom_inv_apply, iso_hom_inv_apply])
    (fun x hx => coinvariantsKer_le_comap f hx)
variable (R G) in

noncomputable def tateCohomologyNegOneIso :
    tateCohomologyFunctor (R := R) (G := G) (-1) ≅ tateNegOneFunctor R G :=
  Functor.isoWhiskerLeft (tateComplexFunctor R G)
      (HomologicalComplex.homologyFunctorIso' (ModuleCat.{u} R) (ComplexShape.up ℤ) (-2) (-1) 0
        (by norm_num) (by norm_num)) ≪≫
    NatIso.ofComponents (fun M => (tateNegOneData M).homologyIso)
      (fun {X Y} f => (tateNegOneMapData f).homologyMap_comm)
end TateIsos
end GroundTheory.GroupCoh


