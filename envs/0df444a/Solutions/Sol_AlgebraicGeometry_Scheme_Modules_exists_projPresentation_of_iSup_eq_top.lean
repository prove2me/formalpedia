-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_projPresentation_of_iSup_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/e18e6486-45c9-50b8-9ac2-758803a6a121

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top

set_option autoImplicit false

universe u

set_option autoImplicit false

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.resLE_comp_ι Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc Spec.map_inj Spec.map_comp_assoc Scheme.toSpecΓ_naturality_assoc Proj.opensRange_awayι Scheme.Hom SpecMap_preimage_basicOpen Proj.basicOpenIsoSpec isPullback_opens_inf Spec Spec.map RingedSpace.isUnit_res_basicOpen Scheme.Opens.toSpecΓ_preimage_basicOpen Scheme Proj.awayι Scheme.Hom.comp_base Proj Proj.awayι_preimage_basicOpen Scheme.Cover.glueMorphisms Proj.basicOpenIsoSpec_inv_ι toSpecΓ_SpecMap_ΓSpecIso_inv Proj.basicOpen Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc IsAffineOpen Scheme.Modules Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Cover.hom_ext Scheme.Opens.toSpecΓ_SpecMap_appLE Proj.SpecMap_awayMap_awayι Scheme.Hom.comp_preimage Proj.awayToSection Proj.basicOpenIsoSpec_hom toSpecΓ RingedSpace Scheme.Cover Scheme.ΓSpecIso ProjSpace.π ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.ratio ProjSpace.val_algebraMap"
p2m_open "AlgebraicGeometry"

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.resLE_comp_ι Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc toSpecΓ_naturality_assoc Hom mk Γ isoSpec_hom Opens.toSpecΓ_preimage_basicOpen OpenCover Hom.comp_base basicOpen Cover.glueMorphisms openCoverOfIsOpenCover Opens.toSpecΓ_SpecMap_presheaf_map_assoc isBasis_affineOpens Modules Opens homOfLE_ι Hom.appLE_map Hom.app_eq_appLE toSpecΓ_preimage_basicOpen Cover.hom_ext Opens.toSpecΓ_SpecMap_appLE Hom.comp_preimage Modules.map_smul basicOpen_le Cover ΓSpecIso toSpecΓ evaluation"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext pullback presheaf Hom isSheaf map_smul ProjPresentation"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme"

namespace LinSys

noncomputable section

variable {X : Scheme.{u}} (M : X.Modules)

abbrev resTop (s : Γ(M, ⊤)) (V : X.Opens) : Γ(M, V) :=
  M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s

def IsFrameOn (s : Γ(M, ⊤)) (V : X.Opens) : Prop :=
  ∀ V' : X.Opens, V' ≤ V →
    Function.Bijective fun g : Γ(X, V') => g • (M.presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op s : Γ(M, V'))

variable {M}

theorem resTop_map' {s : Γ(M, ⊤)} {V W : X.Opens} (ι : W ⟶ V) :
    M.presheaf.map ι.op (resTop M s V) = resTop M s W := by
  simp only [resTop, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

theorem resTop_map {s : Γ(M, ⊤)} {V W : X.Opens} (h : W ≤ V) :
    M.presheaf.map (homOfLE h).op (resTop M s V) = resTop M s W := by
  simp only [resTop, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

theorem resTop_top (s : Γ(M, ⊤)) : resTop M s ⊤ = s := by
  simp only [resTop]
  have : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) = 𝟙 _ := rfl
  rw [this, op_id, M.presheaf.map_id]
  rfl

namespace IsFrameOn

variable {s t : Γ(M, ⊤)} {V W : X.Opens}

theorem mono (h : IsFrameOn M s V) (hWV : W ≤ V) : IsFrameOn M s W :=
  fun V' hV' => h V' (hV'.trans hWV)

theorem bijective (h : IsFrameOn M s V) :
    Function.Bijective fun g : Γ(X, V) => g • resTop M s V := h V le_rfl

theorem injective (h : IsFrameOn M s V) {g g' : Γ(X, V)}
    (hg : g • resTop M s V = g' • resTop M s V) : g = g' :=
  h.bijective.1 hg

noncomputable def coef (h : IsFrameOn M s V) (m : Γ(M, V)) : Γ(X, V) :=
  (Equiv.ofBijective _ h.bijective).symm m

theorem coef_smul (h : IsFrameOn M s V) (m : Γ(M, V)) : h.coef m • resTop M s V = m :=
  (Equiv.ofBijective _ h.bijective).apply_symm_apply m

theorem coef_eq_iff (h : IsFrameOn M s V) (m : Γ(M, V)) (g : Γ(X, V)) :
    h.coef m = g ↔ g • resTop M s V = m := by
  constructor
  · rintro rfl; exact h.coef_smul m
  · intro hg; exact h.injective ((h.coef_smul m).trans hg.symm)

theorem coef_smul_resTop (h : IsFrameOn M s V) (g : Γ(X, V)) : h.coef (g • resTop M s V) = g :=
  (h.coef_eq_iff _ _).2 rfl

theorem coef_resTop (h : IsFrameOn M s V) : h.coef (resTop M s V) = 1 :=
  (h.coef_eq_iff _ _).2 (one_smul _ _)

theorem map_coef' (h : IsFrameOn M s V) (ι : W ⟶ V) (m : Γ(M, V)) :
    X.presheaf.map ι.op (h.coef m) = (h.mono ι.le).coef (M.presheaf.map ι.op m) := by
  symm
  rw [coef_eq_iff, ← resTop_map' ι, ← Modules.map_smul, coef_smul]

theorem map_coef (h : IsFrameOn M s V) (hWV : W ≤ V) (m : Γ(M, V)) :
    X.presheaf.map (homOfLE hWV).op (h.coef m) = (h.mono hWV).coef (M.presheaf.map (homOfLE hWV).op m) :=
  h.map_coef' (homOfLE hWV) m

theorem coef_add (h : IsFrameOn M s V) (m m' : Γ(M, V)) : h.coef (m + m') = h.coef m + h.coef m' := by
  rw [coef_eq_iff, add_smul, coef_smul, coef_smul]

theorem coef_smul' (h : IsFrameOn M s V) (g : Γ(X, V)) (m : Γ(M, V)) : h.coef (g • m) = g * h.coef m := by
  rw [coef_eq_iff, mul_smul, coef_smul]

theorem of_eq_unit_smul (hs : IsFrameOn M s V) (u : Γ(X, V)) (hu : IsUnit u)
    (ht : resTop M t V = u • resTop M s V) : IsFrameOn M t V := by
  intro V' hV'
  have ht' : resTop M t V' = X.presheaf.map (homOfLE hV').op u • resTop M s V' := by
    rw [← resTop_map hV', ht, Modules.map_smul, resTop_map]
  set w := X.presheaf.map (homOfLE hV').op u with hw
  have hu' : IsUnit w := hu.map _
  have hb : Function.Bijective (fun g : Γ(X, V') => g * w) := by
    obtain ⟨winv, hw1, hw2⟩ : ∃ winv, w * winv = 1 ∧ winv * w = 1 :=
      ⟨((hu'.unit⁻¹ : Γ(X, V')ˣ) : Γ(X, V')), hu'.mul_val_inv, hu'.val_inv_mul⟩
    refine ⟨fun a b h => ?_, fun y => ⟨y * winv, ?_⟩⟩
    · have := congr_arg (· * winv) h
      simpa only [mul_assoc, hw1, mul_one] using this
    · simp only [mul_assoc, hw2, mul_one]
  have key : (fun g : Γ(X, V') => g • resTop M t V') =
      (fun g : Γ(X, V') => g • resTop M s V') ∘ fun g => g * w := by
    funext g
    simp only [Function.comp_apply, ht', mul_smul]
  change Function.Bijective fun g : Γ(X, V') => g • resTop M t V'
  rw [key]
  exact (hs V' hV').comp hb

theorem isUnit_of_eq_smul (hs : IsFrameOn M s V) (ht : IsFrameOn M t V) (g : Γ(X, V))
    (hg : resTop M t V = g • resTop M s V) : IsUnit g := by
  obtain ⟨g', hg'⟩ := ht.bijective.2 (resTop M s V)
  simp only at hg'
  rw [hg, ← mul_smul] at hg'
  have h1 : g' * g = 1 := hs.injective (hg'.trans (one_smul _ _).symm)
  exact isUnit_iff_exists_inv'.mpr ⟨g', h1⟩

theorem of_forall_exists (V : X.Opens)
    (H : ∀ x ∈ V, ∃ W : X.Opens, W ≤ V ∧ x ∈ W ∧ IsFrameOn M s W) : IsFrameOn M s V := by
  intro V' hV'

  let ι := {W : X.Opens // W ≤ V' ∧ IsFrameOn M s W}
  let U : ι → X.Opens := fun W => W.1
  have hcover : V' ≤ iSup U := by
    intro x hx
    obtain ⟨W, hWV, hxW, hW⟩ := H x (hV' hx)
    exact Opens.mem_iSup.2 ⟨⟨W ⊓ V', inf_le_right, hW.mono inf_le_left⟩, ⟨hxW, hx⟩⟩
  let Msh : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  constructor
  · intro g g' hgg'
    refine X.sheaf.eq_of_locally_eq' U V' (fun W => homOfLE W.2.1) hcover g g' fun W => ?_
    apply (W.2.2).injective
    have := congr_arg (M.presheaf.map (homOfLE W.2.1).op) hgg'
    simp only [Modules.map_smul, resTop_map] at this
    exact this
  · intro m
    let sf : ∀ W : ι, Γ(X, U W) := fun W => (W.2.2).coef (M.presheaf.map (homOfLE W.2.1).op m)
    have hsf : TopCat.Presheaf.IsCompatible X.presheaf U sf := by
      intro W₁ W₂
      simp only [sf]
      change X.presheaf.map _ _ = X.presheaf.map _ _
      rw [(W₁.2.2).map_coef', (W₂.2.2).map_coef']
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      congr 1
    obtain ⟨g, hg, -⟩ := X.sheaf.existsUnique_gluing' U V' (fun W => homOfLE W.2.1) hcover sf hsf
    let g' : Γ(X, V') := g
    have hg' : ∀ W : ι, X.presheaf.map (homOfLE W.2.1).op g' = sf W := hg
    refine ⟨g', ?_⟩
    refine Msh.eq_of_locally_eq' U V' (fun W => homOfLE W.2.1) hcover _ _ fun W => ?_
    change M.presheaf.map (homOfLE W.2.1).op (g' • resTop M s V') = M.presheaf.map (homOfLE W.2.1).op m
    rw [Modules.map_smul, resTop_map, hg' W]
    exact (W.2.2).coef_smul _

def maxOpen (M : X.Modules) (s : Γ(M, ⊤)) : X.Opens := sSup {W : X.Opens | IsFrameOn M s W}

theorem le_maxOpen (h : IsFrameOn M s V) : V ≤ maxOpen M s := le_sSup h

theorem maxOpen_isFrameOn (s : Γ(M, ⊤)) : IsFrameOn M s (maxOpen M s) := by
  apply of_forall_exists
  intro x hx
  simp only [maxOpen] at hx
  obtain ⟨W, hW, hxW⟩ := Opens.mem_sSup.1 hx
  exact ⟨W, le_sSup hW, hxW, hW⟩

end IsFrameOn

end

end LinSys

end Scheme.Modules

end AlgebraicGeometry

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.resLE_comp_ι Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc Spec.map_inj Spec.map_comp_assoc Scheme.toSpecΓ_naturality_assoc Proj.opensRange_awayι Scheme.Hom SpecMap_preimage_basicOpen Proj.basicOpenIsoSpec isPullback_opens_inf Spec Spec.map RingedSpace.isUnit_res_basicOpen Scheme.Opens.toSpecΓ_preimage_basicOpen Scheme Proj.awayι Scheme.Hom.comp_base Proj Proj.awayι_preimage_basicOpen Scheme.Cover.glueMorphisms Proj.basicOpenIsoSpec_inv_ι toSpecΓ_SpecMap_ΓSpecIso_inv Proj.basicOpen Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc IsAffineOpen Scheme.Modules Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Cover.hom_ext Scheme.Opens.toSpecΓ_SpecMap_appLE Proj.SpecMap_awayMap_awayι Scheme.Hom.comp_preimage Proj.awayToSection Proj.basicOpenIsoSpec_hom toSpecΓ RingedSpace Scheme.Cover Scheme.ΓSpecIso ProjSpace.π ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.ratio ProjSpace.val_algebraMap"
p2m_open "AlgebraicGeometry"

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace MvPolynomial HomogeneousLocalization

namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.resLE_comp_ι Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc toSpecΓ_naturality_assoc Hom mk Γ isoSpec_hom Opens.toSpecΓ_preimage_basicOpen OpenCover Hom.comp_base basicOpen Cover.glueMorphisms openCoverOfIsOpenCover Opens.toSpecΓ_SpecMap_presheaf_map_assoc isBasis_affineOpens Modules Opens homOfLE_ι Hom.appLE_map Hom.app_eq_appLE toSpecΓ_preimage_basicOpen Cover.hom_ext Opens.toSpecΓ_SpecMap_appLE Hom.comp_preimage Modules.map_smul basicOpen_le Cover ΓSpecIso toSpecΓ evaluation"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext pullback presheaf Hom isSheaf map_smul ProjPresentation"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme"

namespace LinSys

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {M : X.Modules} {N : ℕ}
  (σ : Fin (N + 1) → Γ(M, ⊤))

def algR (V : X.Opens) : R →+* Γ(X, V) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop ≫ X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom

theorem map_comp_algR {V W : X.Opens} (ι : W ⟶ V) :
    (X.presheaf.map ι.op).hom.comp (algR f V) = algR f W := by
  change (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop ≫ X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op) ≫
    X.presheaf.map ι.op).hom = _
  simp only [algR, Category.assoc, ← Functor.map_comp, ← op_comp]
  rfl

theorem map_algR {V W : X.Opens} (ι : W ⟶ V) (r : R) :
    X.presheaf.map ι.op (algR f V r) = algR f W r := by
  rw [← map_comp_algR f ι]; rfl

variable {σ}

namespace IsFrameOn

variable {i j : Fin (N + 1)} {V W : X.Opens}

abbrev trans (hi : IsFrameOn M (σ i) V) (k : Fin (N + 1)) : Γ(X, V) := hi.coef (resTop M (σ k) V)

theorem trans_smul (hi : IsFrameOn M (σ i) V) (k : Fin (N + 1)) :
    hi.trans k • resTop M (σ i) V = resTop M (σ k) V := hi.coef_smul _

theorem trans_self (hi : IsFrameOn M (σ i) V) : hi.trans i = 1 := hi.coef_resTop

theorem map_trans (hi : IsFrameOn M (σ i) V) (ι : W ⟶ V) (k : Fin (N + 1)) :
    X.presheaf.map ι.op (hi.trans k) = (hi.mono ι.le).trans k := by
  rw [trans, map_coef', resTop_map']

theorem trans_mul_trans (hi : IsFrameOn M (σ i) V) (hj : IsFrameOn M (σ j) V) (k : Fin (N + 1)) :
    hi.trans k * hj.trans i = hj.trans k := by
  symm
  rw [trans, coef_eq_iff, mul_smul, trans_smul, trans_smul]

theorem trans_mul_trans_self (hi : IsFrameOn M (σ i) V) (hj : IsFrameOn M (σ j) V) :
    hi.trans j * hj.trans i = 1 := by
  rw [trans_mul_trans, trans_self]

theorem isUnit_trans (hi : IsFrameOn M (σ i) V) (hj : IsFrameOn M (σ j) V) : IsUnit (hi.trans j) :=
  isUnit_iff_exists_inv.mpr ⟨hj.trans i, hi.trans_mul_trans_self hj⟩

def evalHom (hi : IsFrameOn M (σ i) V) : MvPolynomial (Fin (N + 1)) R →+* Γ(X, V) :=
  MvPolynomial.eval₂Hom (algR f V) (fun k => hi.trans k)

@[scoped simp] theorem evalHom_X (hi : IsFrameOn M (σ i) V) (k : Fin (N + 1)) :
    evalHom f hi (MvPolynomial.X k) = hi.trans k := by
  simp [evalHom]

@[scoped simp] theorem evalHom_C (hi : IsFrameOn M (σ i) V) (r : R) :
    evalHom f hi (MvPolynomial.C r) = algR f V r := by
  simp [evalHom]

theorem evalHom_X_self (hi : IsFrameOn M (σ i) V) : evalHom f hi (MvPolynomial.X i) = 1 := by
  rw [evalHom_X, trans_self]

theorem isUnit_evalHom_X_self (hi : IsFrameOn M (σ i) V) : IsUnit (evalHom f hi (MvPolynomial.X i)) := by
  rw [evalHom_X_self]; exact isUnit_one

theorem map_comp_evalHom (hi : IsFrameOn M (σ i) V) (ι : W ⟶ V) :
    (X.presheaf.map ι.op).hom.comp (evalHom f hi) = evalHom f (hi.mono ι.le) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.coe_comp, Function.comp_apply, evalHom_C]
    exact map_algR f ι r
  · intro k
    simp only [RingHom.coe_comp, Function.comp_apply, evalHom_X]
    exact hi.map_trans ι k

def chartHom (hi : IsFrameOn M (σ i) V) :
    Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) R)
      →+* Γ(X, V) :=
  (IsLocalization.Away.lift (S := Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) R))
      (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) R) (g := evalHom f hi) (isUnit_evalHom_X_self f hi)).comp
    (algebraMap _ (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) R)))

theorem chartHom_mk (hi : IsFrameOn M (σ i) V) (d : ℕ) (a : MvPolynomial (Fin (N + 1)) R)
    (ha : a ∈ (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (d • 1)) :
    chartHom f hi (Away.mk _ (ProjSpace.X_mem_one R N i) d a ha) = evalHom f hi a := by
  simp only [chartHom, RingHom.coe_comp, Function.comp_apply, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk]
  rw [Localization.mk_eq_mk', IsLocalization.Away.lift, IsLocalization.lift_mk'_spec]
  simp [map_pow, trans_self]

theorem chartHom_ratio (hi : IsFrameOn M (σ i) V) (k : Fin (N + 1)) :
    chartHom f hi (ProjSpace.ratio R N i k) = hi.trans k := by
  rw [ProjSpace.ratio, chartHom_mk, evalHom_X]

theorem chartHom_algebraMap (hi : IsFrameOn M (σ i) V) (r : R) :
    chartHom f hi (algebraMap R _ r) = algR f V r := by
  simp only [chartHom, RingHom.coe_comp, Function.comp_apply, HomogeneousLocalization.algebraMap_apply,
    ProjSpace.val_algebraMap]
  rw [IsLocalization.Away.lift, IsLocalization.lift_eq]
  exact evalHom_C f hi r

theorem chartHom_comp_algebraMap (hi : IsFrameOn M (σ i) V) :
    (chartHom f hi).comp (algebraMap R _) = algR f V :=
  RingHom.ext (chartHom_algebraMap f hi)

theorem map_comp_chartHom (hi : IsFrameOn M (σ i) V) (ι : W ⟶ V) :
    (X.presheaf.map ι.op).hom.comp (chartHom f hi) = chartHom f (hi.mono ι.le) := by
  apply RingHom.ext
  intro z
  obtain ⟨d, a, ha, rfl⟩ := Away.mk_surjective _ (ProjSpace.X_mem_one R N i) z
  simp only [RingHom.coe_comp, Function.comp_apply, chartHom_mk]
  rw [← map_comp_evalHom f hi ι]
  rfl

theorem map_chartHom (hi : IsFrameOn M (σ i) V) (ι : W ⟶ V) (z) :
    X.presheaf.map ι.op (chartHom f hi z) = chartHom f (hi.mono ι.le) z := by
  rw [← map_comp_chartHom f hi ι]; rfl

def chart (hi : IsFrameOn M (σ i) V) :
    (V : Scheme.{u}) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) :=
  V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (chartHom f hi)) ≫
    Proj.awayι _ (MvPolynomial.X i) (ProjSpace.X_mem_one R N i) one_pos

theorem homOfLE_chart (hi : IsFrameOn M (σ i) V) (h : W ≤ V) :
    X.homOfLE h ≫ chart f hi = chart f (hi.mono h) := by
  simp only [chart]
  rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc W V h, ← Spec.map_comp_assoc]
  congr 3
  rw [← CommRingCat.ofHom_hom (X.presheaf.map (homOfLE h).op), ← CommRingCat.ofHom_comp]
  congr 1
  exact map_comp_chartHom f hi (homOfLE h)

theorem chart_π (hi : IsFrameOn M (σ i) V) : chart f hi ≫ ProjSpace.π R N = V.ι ≫ f := by
  simp only [chart, Category.assoc]
  rw [ProjSpace.awayι_comp_π, ← Spec.map_comp, ← CommRingCat.ofHom_comp, chartHom_comp_algebraMap]
  simp only [algR, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc]
  rw [Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc, ← Scheme.toSpecΓ_naturality_assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv (.of R), Category.comp_id]

end IsFrameOn
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn"

end LinSys
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys"

end Scheme.Modules
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme"

end AlgebraicGeometry
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.resLE_comp_ι Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc Spec.map_inj Spec.map_comp_assoc Scheme.toSpecΓ_naturality_assoc Proj.opensRange_awayι Scheme.Hom SpecMap_preimage_basicOpen Proj.basicOpenIsoSpec isPullback_opens_inf Spec Spec.map RingedSpace.isUnit_res_basicOpen Scheme.Opens.toSpecΓ_preimage_basicOpen Scheme Proj.awayι Scheme.Hom.comp_base Proj Proj.awayι_preimage_basicOpen Scheme.Cover.glueMorphisms Proj.basicOpenIsoSpec_inv_ι toSpecΓ_SpecMap_ΓSpecIso_inv Proj.basicOpen Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc IsAffineOpen Scheme.Modules Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Cover.hom_ext Scheme.Opens.toSpecΓ_SpecMap_appLE Proj.SpecMap_awayMap_awayι Scheme.Hom.comp_preimage Proj.awayToSection Proj.basicOpenIsoSpec_hom toSpecΓ RingedSpace Scheme.Cover Scheme.ΓSpecIso ProjSpace.π ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.ratio ProjSpace.val_algebraMap"
p2m_open "AlgebraicGeometry"

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace MvPolynomial HomogeneousLocalization

namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.resLE_comp_ι Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc toSpecΓ_naturality_assoc Hom mk Γ isoSpec_hom Opens.toSpecΓ_preimage_basicOpen OpenCover Hom.comp_base basicOpen Cover.glueMorphisms openCoverOfIsOpenCover Opens.toSpecΓ_SpecMap_presheaf_map_assoc isBasis_affineOpens Modules Opens homOfLE_ι Hom.appLE_map Hom.app_eq_appLE toSpecΓ_preimage_basicOpen Cover.hom_ext Opens.toSpecΓ_SpecMap_appLE Hom.comp_preimage Modules.map_smul basicOpen_le Cover ΓSpecIso toSpecΓ evaluation"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext pullback presheaf Hom isSheaf map_smul ProjPresentation"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme"

namespace LinSys

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

theorem eval₂_mul_of_isHomogeneous {R ι S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (g : ι → S) (c : S)
    {p : MvPolynomial ι R} {n : ℕ} (hp : p.IsHomogeneous n) :
    MvPolynomial.eval₂ φ (fun k => c * g k) p = c ^ n * MvPolynomial.eval₂ φ g p := by
  classical
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ k ∈ d.support, d k = n := by
    have := hp (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {M : X.Modules} {N : ℕ}
  {σ : Fin (N + 1) → Γ(M, ⊤)}

namespace IsFrameOn

variable {i j : Fin (N + 1)} {V : X.Opens}

theorem XX_mem_two (i j : Fin (N + 1)) :
    (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin (N + 1)) R) ∈
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) 2 :=
  SetLike.mul_mem_graded (ProjSpace.X_mem_one R N i) (ProjSpace.X_mem_one R N j)

theorem XX_eq_left (i j : Fin (N + 1)) :
    (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin (N + 1)) R) = MvPolynomial.X i * MvPolynomial.X j :=
  rfl

theorem XX_eq_right (i j : Fin (N + 1)) :
    (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin (N + 1)) R) = MvPolynomial.X j * MvPolynomial.X i :=
  mul_comm _ _

theorem evalHom_eq_mul_evalHom (hi : IsFrameOn M (σ i) V) (hj : IsFrameOn M (σ j) V)
    {a : MvPolynomial (Fin (N + 1)) R} {n : ℕ} (ha : a.IsHomogeneous n) :
    evalHom f hj a = hj.trans i ^ n * evalHom f hi a := by
  have htr : (fun k => hj.trans k) = fun k => hj.trans i * hi.trans k := by
    funext k; rw [mul_comm, trans_mul_trans]
  simp only [evalHom, MvPolynomial.coe_eval₂Hom]
  rw [htr, eval₂_mul_of_isHomogeneous _ _ _ ha]

def chartHom₂ {k : Fin (N + 1)} (hk : IsFrameOn M (σ k) V) (i j : Fin (N + 1))
    (hu : IsUnit (evalHom f hk (MvPolynomial.X i * MvPolynomial.X j))) :
    Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
        (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin (N + 1)) R) →+* Γ(X, V) :=
  (IsLocalization.Away.lift
      (S := Localization.Away (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin (N + 1)) R))
      (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin (N + 1)) R) (g := evalHom f hk) hu).comp
    (algebraMap _ (Localization.Away (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin (N + 1)) R)))

theorem chartHom₂_mk_mul {k : Fin (N + 1)} (hk : IsFrameOn M (σ k) V) (i j : Fin (N + 1))
    (hu : IsUnit (evalHom f hk (MvPolynomial.X i * MvPolynomial.X j))) {e : ℕ}
    (hx2 : (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin (N + 1)) R) ∈
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) e)
    (d : ℕ) (a : MvPolynomial (Fin (N + 1)) R)
    (ha : a ∈ (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (d • e)) :
    chartHom₂ f hk i j hu (Away.mk _ hx2 d a ha) *
        evalHom f hk (MvPolynomial.X i * MvPolynomial.X j) ^ d = evalHom f hk a := by
  simp only [chartHom₂, RingHom.coe_comp, Function.comp_apply, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk]
  rw [Localization.mk_eq_mk', ← map_pow,
    ← IsLocalization.Away.lift_eq (S := Localization.Away
      (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin (N + 1)) R)) _ hu
      ((MvPolynomial.X i * MvPolynomial.X j) ^ d),
    ← map_mul]
  erw [IsLocalization.mk'_spec]
  exact IsLocalization.Away.lift_eq _ hu a

theorem isUnit_evalHom_XX_left (hi : IsFrameOn M (σ i) V) (hj : IsFrameOn M (σ j) V) :
    IsUnit (evalHom f hi (MvPolynomial.X i * MvPolynomial.X j)) := by
  rw [map_mul, evalHom_X_self, one_mul, evalHom_X]
  exact hi.isUnit_trans hj

theorem isUnit_evalHom_XX_right (hi : IsFrameOn M (σ i) V) (hj : IsFrameOn M (σ j) V) :
    IsUnit (evalHom f hj (MvPolynomial.X i * MvPolynomial.X j)) := by
  rw [map_mul, evalHom_X_self, mul_one, evalHom_X]
  exact hj.isUnit_trans hi

theorem chartHom₂_left_mk (hi : IsFrameOn M (σ i) V) (hj : IsFrameOn M (σ j) V) {e : ℕ}
    (hx2 : (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin (N + 1)) R) ∈
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) e)
    (d : ℕ) (a : MvPolynomial (Fin (N + 1)) R)
    (ha : a ∈ (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (d • e)) :
    chartHom₂ f hi i j (isUnit_evalHom_XX_left f hi hj) (Away.mk _ hx2 d a ha) =
      evalHom f hi a * hj.trans i ^ d := by
  have h := chartHom₂_mk_mul f hi i j (isUnit_evalHom_XX_left f hi hj) hx2 d a ha
  rw [map_mul, evalHom_X_self, one_mul, evalHom_X] at h

  calc _ = chartHom₂ f hi i j (isUnit_evalHom_XX_left f hi hj) (Away.mk _ hx2 d a ha) *
        (hi.trans j * hj.trans i) ^ d := by rw [hi.trans_mul_trans_self hj, one_pow, mul_one]
    _ = _ := by rw [mul_pow, ← mul_assoc, h]

theorem chartHom₂_right_mk (hi : IsFrameOn M (σ i) V) (hj : IsFrameOn M (σ j) V) {e : ℕ}
    (hx2 : (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin (N + 1)) R) ∈
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) e)
    (d : ℕ) (a : MvPolynomial (Fin (N + 1)) R)
    (ha : a ∈ (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (d • e)) :
    chartHom₂ f hj i j (isUnit_evalHom_XX_right f hi hj) (Away.mk _ hx2 d a ha) =
      evalHom f hj a * hi.trans j ^ d := by
  have h := chartHom₂_mk_mul f hj i j (isUnit_evalHom_XX_right f hi hj) hx2 d a ha
  rw [map_mul, evalHom_X_self, mul_one, evalHom_X] at h
  calc _ = chartHom₂ f hj i j (isUnit_evalHom_XX_right f hi hj) (Away.mk _ hx2 d a ha) *
        (hj.trans i * hi.trans j) ^ d := by rw [hj.trans_mul_trans_self hi, one_pow, mul_one]
    _ = _ := by rw [mul_pow, ← mul_assoc, h]

theorem chartHom₂_left_eq_right (hi : IsFrameOn M (σ i) V) (hj : IsFrameOn M (σ j) V) :
    chartHom₂ f hi i j (isUnit_evalHom_XX_left f hi hj) = chartHom₂ f hj i j (isUnit_evalHom_XX_right f hi hj) := by
  apply RingHom.ext
  intro z
  obtain ⟨d, a, ha, rfl⟩ := Away.mk_surjective _ (XX_mem_two (R := R) i j) z
  rw [chartHom₂_left_mk f hi hj, chartHom₂_right_mk f hi hj]
  have ha' : a.IsHomogeneous (d * 2) := by
    simpa [MvPolynomial.mem_homogeneousSubmodule] using ha
  rw [evalHom_eq_mul_evalHom f hi hj ha']

  have h1 : hj.trans i * hi.trans j = 1 := hj.trans_mul_trans_self hi
  symm
  calc hj.trans i ^ (d * 2) * evalHom f hi a * hi.trans j ^ d
        = evalHom f hi a * hj.trans i ^ d * (hj.trans i * hi.trans j) ^ d := by ring
    _ = evalHom f hi a * hj.trans i ^ d := by rw [h1, one_pow, mul_one]

theorem chartHom₂_left_comp_awayMap (hi : IsFrameOn M (σ i) V) (hj : IsFrameOn M (σ j) V) :
    (chartHom₂ f hi i j (isUnit_evalHom_XX_left f hi hj)).comp
      (awayMap _ (ProjSpace.X_mem_one R N j) (XX_eq_left i j)) = chartHom f hi := by
  apply RingHom.ext
  intro z
  obtain ⟨d, a, ha, rfl⟩ := Away.mk_surjective _ (ProjSpace.X_mem_one R N i) z
  rw [RingHom.comp_apply, awayMap_mk, chartHom_mk, chartHom₂_left_mk f hi hj]
  simp only [map_mul, map_pow, evalHom_X]
  rw [mul_assoc, ← mul_pow, hi.trans_mul_trans_self hj, one_pow, mul_one]

theorem chartHom₂_right_comp_awayMap (hi : IsFrameOn M (σ i) V) (hj : IsFrameOn M (σ j) V) :
    (chartHom₂ f hj i j (isUnit_evalHom_XX_right f hi hj)).comp
      (awayMap _ (ProjSpace.X_mem_one R N i) (XX_eq_right i j)) = chartHom f hj := by
  apply RingHom.ext
  intro z
  obtain ⟨d, a, ha, rfl⟩ := Away.mk_surjective _ (ProjSpace.X_mem_one R N j) z
  rw [RingHom.comp_apply, awayMap_mk, chartHom_mk, chartHom₂_right_mk f hi hj]
  simp only [map_mul, map_pow, evalHom_X]
  rw [mul_assoc, ← mul_pow, hj.trans_mul_trans_self hi, one_pow, mul_one]

theorem chart_eq_chart (hi : IsFrameOn M (σ i) V) (hj : IsFrameOn M (σ j) V) : chart f hi = chart f hj := by
  simp only [chart]
  rw [← chartHom₂_left_comp_awayMap f hi hj, ← chartHom₂_right_comp_awayMap f hi hj]
  simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  rw [Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι, chartHom₂_left_eq_right f hi hj]

end IsFrameOn
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry"

end LinSys
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry"

end Scheme.Modules
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry"

end AlgebraicGeometry
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.resLE_comp_ι Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc Spec.map_inj Spec.map_comp_assoc Scheme.toSpecΓ_naturality_assoc Proj.opensRange_awayι Scheme.Hom SpecMap_preimage_basicOpen Proj.basicOpenIsoSpec isPullback_opens_inf Spec Spec.map RingedSpace.isUnit_res_basicOpen Scheme.Opens.toSpecΓ_preimage_basicOpen Scheme Proj.awayι Scheme.Hom.comp_base Proj Proj.awayι_preimage_basicOpen Scheme.Cover.glueMorphisms Proj.basicOpenIsoSpec_inv_ι toSpecΓ_SpecMap_ΓSpecIso_inv Proj.basicOpen Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc IsAffineOpen Scheme.Modules Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Cover.hom_ext Scheme.Opens.toSpecΓ_SpecMap_appLE Proj.SpecMap_awayMap_awayι Scheme.Hom.comp_preimage Proj.awayToSection Proj.basicOpenIsoSpec_hom toSpecΓ RingedSpace Scheme.Cover Scheme.ΓSpecIso ProjSpace.π ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.ratio ProjSpace.val_algebraMap"
p2m_open "AlgebraicGeometry"

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace MvPolynomial HomogeneousLocalization

namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.resLE_comp_ι Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc toSpecΓ_naturality_assoc Hom mk Γ isoSpec_hom Opens.toSpecΓ_preimage_basicOpen OpenCover Hom.comp_base basicOpen Cover.glueMorphisms openCoverOfIsOpenCover Opens.toSpecΓ_SpecMap_presheaf_map_assoc isBasis_affineOpens Modules Opens homOfLE_ι Hom.appLE_map Hom.app_eq_appLE toSpecΓ_preimage_basicOpen Cover.hom_ext Opens.toSpecΓ_SpecMap_appLE Hom.comp_preimage Modules.map_smul basicOpen_le Cover ΓSpecIso toSpecΓ evaluation"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext pullback presheaf Hom isSheaf map_smul ProjPresentation"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme"

namespace LinSys

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {M : X.Modules} {N : ℕ}
  (σ : Fin (N + 1) → Γ(M, ⊤))

def Umax (k : Fin (N + 1)) : X.Opens := IsFrameOn.maxOpen M (σ k)

theorem isFrameOn_Umax (k : Fin (N + 1)) : IsFrameOn M (σ k) (Umax σ k) :=
  IsFrameOn.maxOpen_isFrameOn _

variable {σ} in
theorem le_Umax {k : Fin (N + 1)} {V : X.Opens} (h : IsFrameOn M (σ k) V) : V ≤ Umax σ k :=
  IsFrameOn.le_maxOpen h

abbrev chartMax (k : Fin (N + 1)) :
    (Umax σ k : Scheme.{u}) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) :=
  IsFrameOn.chart f (isFrameOn_Umax σ k)

variable (hcov : IsOpenCover (Umax (M := M) σ))

def cover : X.OpenCover := X.openCoverOfIsOpenCover (Umax σ) hcov

theorem charts_compatible (k l : Fin (N + 1)) :
    pullback.fst ((Umax σ k).ι) ((Umax σ l).ι) ≫ chartMax f σ k =
      pullback.snd ((Umax σ k).ι) ((Umax σ l).ι) ≫ chartMax f σ l := by
  rw [← cancel_epi (isPullback_opens_inf (Umax σ k) (Umax σ l)).isoPullback.hom]
  simp only [IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc, chartMax,
    IsFrameOn.homOfLE_chart]
  exact IsFrameOn.chart_eq_chart f _ _

private def _root_.AlgebraicGeometry.Scheme.Modules.LinSys.toProj : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) :=
  (cover σ hcov).glueMorphisms (fun k => chartMax f σ k) (charts_compatible f σ)

p2m_export "AlgebraicGeometry.Scheme.Modules.LinSys" "toProj"
theorem ι_toProj (k : Fin (N + 1)) : (Umax σ k).ι ≫ toProj f σ hcov = chartMax f σ k :=
  (cover σ hcov).ι_glueMorphisms (fun k => chartMax f σ k) (charts_compatible f σ) k

theorem homOfLE_ι_toProj {k : Fin (N + 1)} {V : X.Opens} (h : IsFrameOn M (σ k) V) :
    V.ι ≫ toProj f σ hcov = IsFrameOn.chart f h := by
  rw [← X.homOfLE_ι (le_Umax h), Category.assoc, ι_toProj, chartMax, IsFrameOn.homOfLE_chart]

theorem toProj_π : toProj f σ hcov ≫ ProjSpace.π R N = f := by
  refine Scheme.Cover.hom_ext (cover σ hcov) _ _ fun k => ?_
  change (Umax σ k).ι ≫ _ = (Umax σ k).ι ≫ f
  rw [← Category.assoc, ι_toProj, chartMax, IsFrameOn.chart_π]

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry"

end LinSys
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry"

end Scheme.Modules
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry"

end AlgebraicGeometry
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.resLE_comp_ι Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc Spec.map_inj Spec.map_comp_assoc Scheme.toSpecΓ_naturality_assoc Proj.opensRange_awayι Scheme.Hom SpecMap_preimage_basicOpen Proj.basicOpenIsoSpec isPullback_opens_inf Spec Spec.map RingedSpace.isUnit_res_basicOpen Scheme.Opens.toSpecΓ_preimage_basicOpen Scheme Proj.awayι Scheme.Hom.comp_base Proj Proj.awayι_preimage_basicOpen Scheme.Cover.glueMorphisms Proj.basicOpenIsoSpec_inv_ι toSpecΓ_SpecMap_ΓSpecIso_inv Proj.basicOpen Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc IsAffineOpen Scheme.Modules Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Cover.hom_ext Scheme.Opens.toSpecΓ_SpecMap_appLE Proj.SpecMap_awayMap_awayι Scheme.Hom.comp_preimage Proj.awayToSection Proj.basicOpenIsoSpec_hom toSpecΓ RingedSpace Scheme.Cover Scheme.ΓSpecIso ProjSpace.π ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.ratio ProjSpace.val_algebraMap"
p2m_open "AlgebraicGeometry"

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace MvPolynomial HomogeneousLocalization

namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.resLE_comp_ι Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc toSpecΓ_naturality_assoc Hom mk Γ isoSpec_hom Opens.toSpecΓ_preimage_basicOpen OpenCover Hom.comp_base basicOpen Cover.glueMorphisms openCoverOfIsOpenCover Opens.toSpecΓ_SpecMap_presheaf_map_assoc isBasis_affineOpens Modules Opens homOfLE_ι Hom.appLE_map Hom.app_eq_appLE toSpecΓ_preimage_basicOpen Cover.hom_ext Opens.toSpecΓ_SpecMap_appLE Hom.comp_preimage Modules.map_smul basicOpen_le Cover ΓSpecIso toSpecΓ evaluation"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext pullback presheaf Hom isSheaf map_smul ProjPresentation"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme"

namespace LinSys

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {M : X.Modules} {N : ℕ}

theorem appLE_awayToSection_of_fac {A τ : Type u} [CommRing A] [SetLike τ A] [AddSubgroupClass τ A]
    (𝒜 : ℕ → τ) [GradedRing 𝒜]
    {g : A} {m : ℕ} (g_deg : g ∈ 𝒜 m) (hm : 0 < m)
    (φ : X ⟶ Proj 𝒜) {V : X.Opens} (hV : IsAffineOpen V) (ψ : Away 𝒜 g →+* Γ(X, V))
    (hfac : V.ι ≫ φ = V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ Proj.awayι 𝒜 g g_deg hm)
    (hle : V ≤ φ ⁻¹ᵁ Proj.basicOpen 𝒜 g) (z : Away 𝒜 g) :
    φ.appLE (Proj.basicOpen 𝒜 g) V hle (Proj.awayToSection 𝒜 g z) = ψ z := by
  have h1 : φ.resLE _ V hle =
      V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ (Proj.basicOpenIsoSpec 𝒜 g g_deg hm).inv := by
    rw [← cancel_mono (Proj.basicOpen 𝒜 g).ι, Scheme.Hom.resLE_comp_ι, hfac]
    simp only [Category.assoc, Proj.basicOpenIsoSpec_inv_ι]
  have h2 := Scheme.Opens.toSpecΓ_SpecMap_appLE φ (Proj.basicOpen 𝒜 g) V hle
  rw [h1] at h2
  have h3 : V.toSpecΓ ≫ Spec.map (Proj.awayToSection 𝒜 g ≫ φ.appLE (Proj.basicOpen 𝒜 g) V hle) =
      V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) := by
    have e : (Proj.basicOpen 𝒜 g).toSpecΓ ≫ Spec.map (Proj.awayToSection 𝒜 g) =
        (Proj.basicOpenIsoSpec 𝒜 g g_deg hm).hom := by
      rw [Proj.basicOpenIsoSpec_hom]; rfl
    rw [Spec.map_comp, reassoc_of% h2]
    try simp only [Category.assoc]
    rw [e, Iso.inv_hom_id, Category.comp_id]
  haveI : IsIso V.toSpecΓ := by rw [← hV.isoSpec_hom]; infer_instance
  rw [cancel_epi] at h3
  have h4 := Spec.map_inj.mp h3
  have := congr_arg (fun t => t.hom z) h4
  simpa using this

variable (σ : Fin (N + 1) → Γ(M, ⊤)) (hcov : IsOpenCover (Umax (M := M) σ))

theorem Umax_le_preimage (k : Fin (N + 1)) :
    Umax σ k ≤ toProj f σ hcov ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X k) := by
  intro x hx
  change (toProj f σ hcov).base x ∈
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X k)
  have : (toProj f σ hcov).base x = (chartMax f σ k).base ⟨x, hx⟩ := by
    rw [← ι_toProj f σ hcov k]; rfl
  rw [this, chartMax, IsFrameOn.chart]
  simp only [Scheme.Hom.comp_base, TopCat.comp_app]
  rw [← Proj.opensRange_awayι _ (MvPolynomial.X k) (ProjSpace.X_mem_one R N k) one_pos]
  exact ⟨_, rfl⟩

variable {σ} in
theorem chart_preimage_basicOpen {k : Fin (N + 1)} {V : X.Opens} (h : IsFrameOn M (σ k) V)
    (i : Fin (N + 1)) :
    IsFrameOn.chart f h ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (MvPolynomial.X i) = V.ι ⁻¹ᵁ X.basicOpen (h.trans i) := by
  simp only [IsFrameOn.chart, Scheme.Hom.comp_preimage]
  rw [Proj.awayι_preimage_basicOpen _ (ProjSpace.X_mem_one R N k) one_pos (ProjSpace.X_mem_one R N i)
    one_pos, SpecMap_preimage_basicOpen, Scheme.Opens.toSpecΓ_preimage_basicOpen]
  congr 2
  change IsFrameOn.chartHom f h (Away.mk _ (ProjSpace.X_mem_one R N k) 1 (MvPolynomial.X i ^ 1) _) = _
  rw [IsFrameOn.chartHom_mk, map_pow, IsFrameOn.evalHom_X, pow_one]

theorem preimage_le_Umax (i : Fin (N + 1)) :
    toProj f σ hcov ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)
      ≤ Umax σ i := by
  intro x hx
  obtain ⟨k, hk⟩ := hcov.exists_mem x
  have hx' : (⟨x, hk⟩ : Umax σ k) ∈ ((Umax σ k).ι ≫ toProj f σ hcov) ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) := hx
  rw [ι_toProj, chartMax, chart_preimage_basicOpen] at hx'
  have hxB : x ∈ X.basicOpen ((isFrameOn_Umax σ k).trans i) := hx'

  have hB : X.basicOpen ((isFrameOn_Umax σ k).trans i) ≤ Umax σ k := X.basicOpen_le _
  have hframeB : IsFrameOn M (σ i) (X.basicOpen ((isFrameOn_Umax σ k).trans i)) := by
    refine IsFrameOn.of_eq_unit_smul ((isFrameOn_Umax σ k).mono hB)
      (X.presheaf.map (homOfLE hB).op ((isFrameOn_Umax σ k).trans i))
      (RingedSpace.isUnit_res_basicOpen _ _) ?_
    rw [← resTop_map hB, ← resTop_map hB, ← Modules.map_smul, IsFrameOn.trans_smul]
  exact le_Umax hframeB hxB

theorem preimage_eq_Umax (i : Fin (N + 1)) :
    toProj f σ hcov ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)
      = Umax σ i :=
  le_antisymm (preimage_le_Umax f σ hcov i) (Umax_le_preimage f σ hcov i)

theorem isFrameOn_preimage (i : Fin (N + 1)) :
    IsFrameOn M (σ i) (toProj f σ hcov ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) :=
  (isFrameOn_Umax σ i).mono (preimage_le_Umax f σ hcov i)

theorem map_app_awayToSection_ratio (i j : Fin (N + 1)) {V : X.Opens} (hVaff : IsAffineOpen V)
    (hV : V ≤ toProj f σ hcov ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) :
    X.presheaf.map (homOfLE hV).op
      ((toProj f σ hcov).app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
        (MvPolynomial.X i)) (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio R N i j))) =
      ((isFrameOn_preimage f σ hcov i).mono hV).trans j := by
  have hVi : IsFrameOn M (σ i) V := (isFrameOn_preimage f σ hcov i).mono hV
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  rw [appLE_awayToSection_of_fac (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
    (ProjSpace.X_mem_one R N i) one_pos (toProj f σ hcov) hVaff (IsFrameOn.chartHom f hVi)
    (homOfLE_ι_toProj f σ hcov hVi) hV]
  exact IsFrameOn.chartHom_ratio f hVi j

theorem app_ratio_smul (i j : Fin (N + 1)) :
    ((toProj f σ hcov).app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
        (MvPolynomial.X i)) (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio R N i j))) •
      resTop M (σ i) (toProj f σ hcov ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) =
    resTop M (σ j) (toProj f σ hcov ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) := by
  set W := toProj f σ hcov ⁻¹ᵁ
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) with hW

  let ι := {V : X.Opens // V ≤ W ∧ IsAffineOpen V}
  let U : ι → X.Opens := fun V => V.1
  have hcover : W ≤ iSup U := by
    intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
    exact Opens.mem_iSup.2 ⟨⟨V, hVW, hV⟩, hxV⟩
  let Msh : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  refine Msh.eq_of_locally_eq' U W (fun V => homOfLE V.2.1) hcover _ _ fun V => ?_
  change M.presheaf.map (homOfLE V.2.1).op (_ • _) = M.presheaf.map (homOfLE V.2.1).op _
  rw [Modules.map_smul, resTop_map, resTop_map, map_app_awayToSection_ratio f σ hcov i j V.2.2 V.2.1,
    IsFrameOn.trans_smul]

def projPresentation : M.ProjPresentation f N where
  σ := σ
  toProj := toProj f σ hcov
  toProj_π := toProj_π f σ hcov
  frame := fun i V hV => isFrameOn_preimage f σ hcov i V hV
  app_ratio_smul := fun i j => app_ratio_smul f σ hcov i j

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry"

end LinSys
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry"

end Scheme.Modules
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry"

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom.resLE_comp_ι Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc toSpecΓ_naturality_assoc Hom mk Γ isoSpec_hom Opens.toSpecΓ_preimage_basicOpen OpenCover Hom.comp_base basicOpen Cover.glueMorphisms openCoverOfIsOpenCover Opens.toSpecΓ_SpecMap_presheaf_map_assoc isBasis_affineOpens Modules Opens homOfLE_ι Hom.appLE_map Hom.app_eq_appLE toSpecΓ_preimage_basicOpen Cover.hom_ext Opens.toSpecΓ_SpecMap_appLE Hom.comp_preimage Modules.map_smul basicOpen_le Cover ΓSpecIso toSpecΓ evaluation" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext pullback presheaf Hom isSheaf map_smul ProjPresentation" end Scheme.Modules
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules" in
attribute [local instance] MvPolynomial.gradedAlgebra in

theorem Scheme.Modules.exists_projPresentation_of_iSup_eq_top'
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (M : X.Modules)
    (N : ℕ) (σ : Fin (N + 1) → Γ(M, ⊤))
    (U : Fin (N + 1) → X.Opens) (hU : iSup U = ⊤)
    (hframe : ∀ i (V : X.Opens), V ≤ U i →
       Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ i) : Γ(M, V))) :
    ∃ 𝔓 : M.ProjPresentation f N, 𝔓.σ = σ ∧ ∀ i, U i ≤ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i) := by
  have hUle : ∀ i, U i ≤ Scheme.Modules.LinSys.Umax σ i := fun i =>
    Scheme.Modules.LinSys.le_Umax (hframe i)
  have hcov : IsOpenCover (Scheme.Modules.LinSys.Umax (M := M) σ) := by
    change iSup _ = ⊤
    exact top_le_iff.mp (hU ▸ iSup_mono hUle)
  exact ⟨Scheme.Modules.LinSys.projPresentation f σ hcov, rfl, fun i =>
    (hUle i).trans (Scheme.Modules.LinSys.Umax_le_preimage f σ hcov i)⟩

end AlgebraicGeometry
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys.IsFrameOn P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules.LinSys P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (M : X.Modules)
    (N : ℕ) (σ : Fin (N + 1) → Γ(M, ⊤))
    (U : Fin (N + 1) → X.Opens) (hU : iSup U = ⊤)
    (hframe : ∀ i (V : X.Opens), V ≤ U i →
       Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ i) : Γ(M, V))) :
    ∃ 𝔓 : M.ProjPresentation f N, 𝔓.σ = σ ∧ ∀ i, U i ≤ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i) :=
  AlgebraicGeometry.Scheme.Modules.exists_projPresentation_of_iSup_eq_top' f M N σ U hU hframe

end S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top (solution)
