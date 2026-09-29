-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.exists_idealSheafData_ideal_basicOpen_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/be0ea181-a497-50fc-96f9-79e11948c078

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ofIdealTop
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_exists_idealSheafData_ideal_basicOpen_eq_span

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_idealSheafData_ideal_basicOpen_eq_span.AlgebraicGeometry HomogeneousLocalization"

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Opens.topIso_inv Scheme.IdealSheafData.equivOfIsAffine Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right Proj.opensRange_awayι Scheme.IdealSheafData.comap_comp Scheme.Hom Scheme.Hom.appLE_comp_appLE Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left Proj.basicOpenIsoSpec IsAffine Spec Scheme.Hom.id_appTop Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Proj.awayι Scheme.IdealSheafData.equivOfIsAffine_apply Scheme.Hom.comp_appTop Proj Proj.pullbackAwayιIso isAffineOpen_top Scheme.IdealSheafData.equivOfIsAffine_symm_apply Proj.isAffineOpen_basicOpen Proj.basicOpen Proj.basicOpenIsoAway_hom Scheme.Opens Scheme.IdealSheafData.ofIdealTop Proj.awayToSection Proj.basicOpenToSpec_app_top Proj.basicOpenIsoSpec_hom Scheme.Opens.ι_preimage_self Scheme.Opens.ι_appLE Scheme.IdealSheafData Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app ProjSpace.X_mem_one ProjSpace.affineOpenCover Scheme.IdealSheafData.ideal_comap_of_le Scheme.IdealSheafData.exists_comap_eq_of_openCover Scheme.IdealSheafData.comap_ofIdealTop"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "X_mem_one affineOpenCover map"
namespace K0
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

variable (n : ℕ) (A : Type) [CommRing A] (I : Ideal (MvPolynomial (Fin (n + 1)) A))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A
local notation "S" => MvPolynomial (Fin (n + 1)) A

theorem pow_mem (f : S) (hf : f ∈ 𝒜 1) (e : ℕ) : f ^ e ∈ 𝒜 e := by
  simpa using SetLike.pow_mem_graded e hf

def gens (f : S) (hf : f ∈ 𝒜 1) : Set (Away 𝒜 f) :=
  { z | ∃ (d : ℕ) (F : S) (hF : F.IsHomogeneous d), F ∈ I ∧
      z = HomogeneousLocalization.mk (x := Submonoid.powers f)
        { deg := d
          num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
          den := ⟨f ^ d, pow_mem n A f hf d⟩
          den_mem := ⟨d, rfl⟩ } }

def chartIdeal (f : S) (hf : f ∈ 𝒜 1) : Ideal (Away 𝒜 f) := Ideal.span (gens n A I f hf)

def overlapUnit (f g x : S) (hg : g ∈ 𝒜 1) (hx : x = f * g) (hxm : x ∈ 𝒜 2) : Away 𝒜 x :=
  HomogeneousLocalization.mk
    { deg := 2
      num := ⟨g ^ 2, pow_mem n A g hg 2⟩
      den := ⟨x, hxm⟩
      den_mem := ⟨1, pow_one x⟩ }

theorem awayMap_gen (f g x : S) (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (hx : x = f * g) (hx' : x = g * f)
    (d : ℕ) (F : S) (hF : F.IsHomogeneous d) :
    awayMap 𝒜 hg hx (HomogeneousLocalization.mk
        { deg := d
          num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
          den := ⟨f ^ d, pow_mem n A f hf d⟩
          den_mem := ⟨d, rfl⟩ }) =
      overlapUnit n A f g x hg hx (hx ▸ SetLike.mul_mem_graded hf hg) ^ d *
      awayMap 𝒜 hf hx' (HomogeneousLocalization.mk
        { deg := d
          num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
          den := ⟨g ^ d, pow_mem n A g hg d⟩
          den_mem := ⟨d, rfl⟩ }) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow, val_awayMap_mk, val_awayMap_mk,
    overlapUnit, HomogeneousLocalization.val_mk, Localization.mk_pow, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow]
  subst hx
  ring

theorem map_chartIdeal_le (f g x : S) (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (hx : x = f * g) (hx' : x = g * f) :
    (chartIdeal n A I f hf).map (awayMap 𝒜 hg hx) ≤ (chartIdeal n A I g hg).map (awayMap 𝒜 hf hx') := by
  rw [chartIdeal, chartIdeal, Ideal.map_span, Ideal.map_span]
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨z, ⟨d, F, hF, hFI, rfl⟩, rfl⟩
  rw [awayMap_gen n A f g x hf hg hx hx' d F hF]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, ⟨d, F, hF, hFI, rfl⟩, rfl⟩)

theorem map_chartIdeal_eq (f g x : S) (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (hx : x = f * g) (hx' : x = g * f) :
    (chartIdeal n A I f hf).map (awayMap 𝒜 hg hx) = (chartIdeal n A I g hg).map (awayMap 𝒜 hf hx') :=
  le_antisymm (map_chartIdeal_le n A I f g x hf hg hx hx') (map_chartIdeal_le n A I g f x hg hf hx' hx)

def chartSheaf (f : S) (hf : f ∈ 𝒜 1) : (Spec (.of (Away 𝒜 f))).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    ((chartIdeal n A I f hf).map (Scheme.ΓSpecIso (.of (Away 𝒜 f))).inv.hom)

theorem chartSheaf_comap_specMap (f g x : S) (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (hx : x = f * g) (hx' : x = g * f) :
    (chartSheaf n A I f hf).comap (Spec.map (CommRingCat.ofHom (awayMap 𝒜 hg hx))) =
      (chartSheaf n A I g hg).comap (Spec.map (CommRingCat.ofHom (awayMap 𝒜 hf hx'))) := by
  rw [chartSheaf, chartSheaf, Scheme.IdealSheafData.comap_ofIdealTop, Scheme.IdealSheafData.comap_ofIdealTop,
    Ideal.map_map, Ideal.map_map]
  have nat : ∀ {R T : CommRingCat.{0}} (φ : R ⟶ T),
      (Spec.map φ).appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom = (Scheme.ΓSpecIso T).inv.hom.comp φ.hom := by
    intro R T φ
    have := Scheme.ΓSpecIso_inv_naturality φ
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, this]
  rw [nat, nat, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, ← Ideal.map_map, ← Ideal.map_map,
    map_chartIdeal_eq n A I f g x hf hg hx hx']

end AlgebraicGeometry.ProjSpace.K0

end

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Opens.topIso_inv Scheme.IdealSheafData.equivOfIsAffine Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right Proj.opensRange_awayι Scheme.IdealSheafData.comap_comp Scheme.Hom Scheme.Hom.appLE_comp_appLE Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left Proj.basicOpenIsoSpec IsAffine Spec Scheme.Hom.id_appTop Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Proj.awayι Scheme.IdealSheafData.equivOfIsAffine_apply Scheme.Hom.comp_appTop Proj Proj.pullbackAwayιIso isAffineOpen_top Scheme.IdealSheafData.equivOfIsAffine_symm_apply Proj.isAffineOpen_basicOpen Proj.basicOpen Proj.basicOpenIsoAway_hom Scheme.Opens Scheme.IdealSheafData.ofIdealTop Proj.awayToSection Proj.basicOpenToSpec_app_top Proj.basicOpenIsoSpec_hom Scheme.Opens.ι_preimage_self Scheme.Opens.ι_appLE Scheme.IdealSheafData Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app ProjSpace.X_mem_one ProjSpace.affineOpenCover Scheme.IdealSheafData.ideal_comap_of_le Scheme.IdealSheafData.exists_comap_eq_of_openCover Scheme.IdealSheafData.comap_ofIdealTop"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "X_mem_one affineOpenCover map"
namespace K0
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

variable (n : ℕ) (A : Type) [CommRing A] (I : Ideal (MvPolynomial (Fin (n + 1)) A))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A
local notation "S" => MvPolynomial (Fin (n + 1)) A

theorem le_preimage_awayι (f : S) (hf : f ∈ 𝒜 1) :
    (⊤ : (Spec (.of (Away 𝒜 f))).Opens) ≤ Proj.awayι 𝒜 f hf one_pos ⁻¹ᵁ Proj.basicOpen 𝒜 f := by
  rintro x -
  show (Proj.awayι 𝒜 f hf one_pos).base x ∈ Proj.basicOpen 𝒜 f
  rw [← Proj.opensRange_awayι 𝒜 f hf one_pos]
  exact ⟨x, rfl⟩

theorem ofIdealTop_ideal_top {Y : Scheme.{0}} [IsAffine Y] (J : Ideal Γ(Y, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop J).ideal ⟨⊤, isAffineOpen_top Y⟩ = J := by
  rw [← Scheme.IdealSheafData.equivOfIsAffine_symm_apply, ← Scheme.IdealSheafData.equivOfIsAffine_apply]
  exact Scheme.IdealSheafData.equivOfIsAffine.apply_symm_apply J

theorem appLE_awayToSection (f : S) (hf : f ∈ 𝒜 1) (z : Away 𝒜 f) :
    (Proj.awayι 𝒜 f hf one_pos).appLE (Proj.basicOpen 𝒜 f) ⊤ (le_preimage_awayι n A f hf)
        (Proj.awayToSection 𝒜 f z) =
      (Scheme.ΓSpecIso (.of (Away 𝒜 f))).inv z := by
  set e := Proj.basicOpenIsoSpec 𝒜 f hf one_pos with he
  have e₁ : (⊤ : (Proj.basicOpen 𝒜 f : Scheme.{0}).Opens) ≤ (Proj.basicOpen 𝒜 f).ι ⁻¹ᵁ Proj.basicOpen 𝒜 f := by
    rw [Scheme.Opens.ι_preimage_self]
  have e₂ : (⊤ : (Spec (.of (Away 𝒜 f))).Opens) ≤ e.inv ⁻¹ᵁ ⊤ := le_top

  have h1 : (Proj.awayι 𝒜 f hf one_pos).appLE (Proj.basicOpen 𝒜 f) ⊤ (le_preimage_awayι n A f hf) =
      (Proj.basicOpen 𝒜 f).ι.appLE (Proj.basicOpen 𝒜 f) ⊤ e₁ ≫ e.inv.appLE ⊤ ⊤ e₂ :=
    (Scheme.Hom.appLE_comp_appLE e.inv (Proj.basicOpen 𝒜 f).ι (Proj.basicOpen 𝒜 f) ⊤ ⊤ e₁ e₂).symm

  have h2 : (Proj.basicOpen 𝒜 f).ι.appLE (Proj.basicOpen 𝒜 f) ⊤ e₁ = (Proj.basicOpen 𝒜 f).topIso.inv := by
    rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    rfl

  have h3 : e.inv.appLE ⊤ ⊤ e₂ = e.inv.appTop := Scheme.Hom.appLE_eq_app _

  have h4 : e.hom.appTop = (Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection 𝒜 f ≫ (Proj.basicOpen 𝒜 f).topIso.inv := by
    rw [he, Proj.basicOpenIsoSpec_hom]
    exact Proj.basicOpenToSpec_app_top 𝒜 f

  have h5 : ∀ y, e.inv.appTop (e.hom.appTop y) = y := fun y => by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e.inv_hom_id, Scheme.Hom.id_appTop]
    rfl
  rw [h1, CommRingCat.comp_apply, h2, h3]
  have h6 : (Proj.basicOpen 𝒜 f).topIso.inv (Proj.awayToSection 𝒜 f z) =
      e.hom.appTop ((Scheme.ΓSpecIso _).inv z) := by
    rw [h4, CommRingCat.comp_apply, CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  rw [h6, h5]

theorem bijective_appLE (f : S) (hf : f ∈ 𝒜 1) :
    Function.Bijective
      ((Proj.awayι 𝒜 f hf one_pos).appLE (Proj.basicOpen 𝒜 f) ⊤ (le_preimage_awayι n A f hf)) := by
  have hτ : Function.Bijective (Proj.awayToSection 𝒜 f) := by
    have : IsIso (Proj.awayToSection 𝒜 f) := by
      rw [← Proj.basicOpenIsoAway_hom 𝒜 f hf one_pos]; infer_instance
    exact ConcreteCategory.bijective_of_isIso _
  have hΓ : Function.Bijective ((Scheme.ΓSpecIso (.of (Away 𝒜 f))).inv) :=
    ConcreteCategory.bijective_of_isIso _
  let eτ := Equiv.ofBijective _ hτ
  have heq : ((Proj.awayι 𝒜 f hf one_pos).appLE (Proj.basicOpen 𝒜 f) ⊤ (le_preimage_awayι n A f hf) :
        Γ(Proj 𝒜, Proj.basicOpen 𝒜 f) → Γ(Spec (.of (Away 𝒜 f)), ⊤)) =
      (Scheme.ΓSpecIso (.of (Away 𝒜 f))).inv ∘ eτ.symm := by
    funext y
    rw [Function.comp_apply, ← appLE_awayToSection n A f hf (eτ.symm y)]
    congr 1
    exact (eτ.apply_symm_apply y).symm
  rw [heq]
  exact hΓ.comp eτ.symm.bijective

theorem ideal_eq_of_map_appLE (f : S) (hf : f ∈ 𝒜 1) (𝔧 : Ideal Γ(Proj 𝒜, Proj.basicOpen 𝒜 f))
    (h : (chartIdeal n A I f hf).map (Scheme.ΓSpecIso (.of (Away 𝒜 f))).inv.hom =
      𝔧.map ((Proj.awayι 𝒜 f hf one_pos).appLE (Proj.basicOpen 𝒜 f) ⊤ (le_preimage_awayι n A f hf)).hom) :
    𝔧 = (chartIdeal n A I f hf).map (Proj.awayToSection 𝒜 f).hom := by
  have hψ := bijective_appLE n A f hf
  rw [← Ideal.comap_map_of_bijective _ hψ (I := 𝔧), ← h,
    ← Ideal.comap_map_of_bijective _ hψ (I := (chartIdeal n A I f hf).map (Proj.awayToSection 𝒜 f).hom),
    Ideal.map_map]
  congr 2
  ext z
  exact (appLE_awayToSection n A f hf z).symm

theorem compat (i j : Fin (n + 1)) {V : Scheme.{0}}
    (a : V ⟶ Spec (.of (Away 𝒜 (X i)))) (b : V ⟶ Spec (.of (Away 𝒜 (X j))))
    (hab : a ≫ Proj.awayι 𝒜 (X i) (ProjSpace.X_mem_one A n i) one_pos =
      b ≫ Proj.awayι 𝒜 (X j) (ProjSpace.X_mem_one A n j) one_pos) :
    (chartSheaf n A I (X i) (ProjSpace.X_mem_one A n i)).comap a =
      (chartSheaf n A I (X j) (ProjSpace.X_mem_one A n j)).comap b := by
  obtain ⟨c, hca, hcb⟩ : ∃ c : V ⟶ pullback (Proj.awayι 𝒜 (X i) (ProjSpace.X_mem_one A n i) one_pos)
      (Proj.awayι 𝒜 (X j) (ProjSpace.X_mem_one A n j) one_pos),
      c ≫ pullback.fst _ _ = a ∧ c ≫ pullback.snd _ _ = b :=
    ⟨pullback.lift a b hab, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  subst hca hcb
  have hx : (X i * X j : S) = X i * X j := rfl
  have hfst : pullback.fst (Proj.awayι 𝒜 (X i) (ProjSpace.X_mem_one A n i) one_pos)
        (Proj.awayι 𝒜 (X j) (ProjSpace.X_mem_one A n j) one_pos) =
      (Proj.pullbackAwayιIso 𝒜 (ProjSpace.X_mem_one A n i) one_pos (ProjSpace.X_mem_one A n j) one_pos hx).hom ≫
        Spec.map (CommRingCat.ofHom (awayMap 𝒜 (ProjSpace.X_mem_one A n j) hx)) :=
    (Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left ..).symm
  have hsnd : pullback.snd (Proj.awayι 𝒜 (X i) (ProjSpace.X_mem_one A n i) one_pos)
        (Proj.awayι 𝒜 (X j) (ProjSpace.X_mem_one A n j) one_pos) =
      (Proj.pullbackAwayιIso 𝒜 (ProjSpace.X_mem_one A n i) one_pos (ProjSpace.X_mem_one A n j) one_pos hx).hom ≫
        Spec.map (CommRingCat.ofHom (awayMap 𝒜 (ProjSpace.X_mem_one A n i) (hx.trans (mul_comm _ _)))) :=
    (Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right ..).symm
  rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, hfst, hsnd,
    Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp,
    chartSheaf_comap_specMap n A I (X i) (X j) (X i * X j) _ _ hx (hx.trans (mul_comm _ _))]

theorem main :
    ∃ 𝓘 : (Proj 𝒜).IdealSheafData, ∀ i : Fin (n + 1),
      𝓘.ideal ⟨Proj.basicOpen 𝒜 (X i), Proj.isAffineOpen_basicOpen 𝒜 (X i) (ProjSpace.X_mem_one A n i) one_pos⟩ =
        (chartIdeal n A I (X i) (ProjSpace.X_mem_one A n i)).map (Proj.awayToSection 𝒜 (X i)).hom := by
  obtain ⟨I₀, hI₀⟩ := Scheme.IdealSheafData.exists_comap_eq_of_openCover
    (ProjSpace.affineOpenCover A n).openCover
    (fun i => chartSheaf n A I (X i) (ProjSpace.X_mem_one A n i))
    (fun i j V a b hab => compat n A I i j a b hab)
  refine ⟨I₀, fun i => ?_⟩
  have hc : I₀.comap (Proj.awayι 𝒜 (X i) (ProjSpace.X_mem_one A n i) one_pos) =
      chartSheaf n A I (X i) (ProjSpace.X_mem_one A n i) := hI₀ i
  have h2 := AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_le I₀
    (Proj.awayι 𝒜 (X i) (ProjSpace.X_mem_one A n i) one_pos)
    ⟨Proj.basicOpen 𝒜 (X i), Proj.isAffineOpen_basicOpen 𝒜 (X i) (ProjSpace.X_mem_one A n i) one_pos⟩
    ⟨⊤, isAffineOpen_top _⟩ (le_preimage_awayι n A (X i) (ProjSpace.X_mem_one A n i))
  rw [hc, chartSheaf, ofIdealTop_ideal_top] at h2
  exact ideal_eq_of_map_appLE n A I (X i) _ _ h2

end AlgebraicGeometry.ProjSpace.K0

end

p2m_open "MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_idealSheafData_ideal_basicOpen_eq_span.AlgebraicGeometry AlgebraicGeometry.HilbertFunctor"

theorem solution
    (n : ℕ) (A : Type) [CommRing A] (I : Ideal (MvPolynomial (Fin (n + 1)) A)) :
    ∃ 𝓘 : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)).IdealSheafData,
      ∀ i : Fin (n + 1),
        𝓘.ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i) (ProjSpace.X_mem_one A n i) one_pos⟩ =
        Ideal.span { s | ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d),
          F ∈ I ∧
          s = (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                  den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ }) } := by
  obtain ⟨𝓘, h𝓘⟩ := AlgebraicGeometry.ProjSpace.K0.main n A I
  refine ⟨𝓘, fun i => ?_⟩
  rw [h𝓘 i, AlgebraicGeometry.ProjSpace.K0.chartIdeal, Ideal.map_span]
  congr 1
  ext s
  constructor
  · rintro ⟨z, ⟨d, F, hF, hFI, rfl⟩, rfl⟩
    exact ⟨d, F, hF, hFI, rfl⟩
  · rintro ⟨d, F, hF, hFI, rfl⟩
    exact ⟨_, ⟨d, F, hF, hFI, rfl⟩, rfl⟩

end S_AlgebraicGeometry_ProjSpace_exists_idealSheafData_ideal_basicOpen_eq_span
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_exists_idealSheafData_ideal_basicOpen_eq_span (solution)
