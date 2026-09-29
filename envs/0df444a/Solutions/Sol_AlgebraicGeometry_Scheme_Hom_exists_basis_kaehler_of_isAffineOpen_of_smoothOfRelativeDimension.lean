-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/4d8ba412-4544-5194-b352-93852caa2e7f

import Mathlib
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_kaehlerToSections_bijective_of_isAffineOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension

set_option autoImplicit false

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace TensorProduct

universe u

namespace KAFrameGC6

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

noncomputable abbrev pmap {W W' : X.Opens} (i : W' ≤ W) (w : (f.kaehlerPresheaf.obj (op W) : Type u)) :
    (f.kaehlerPresheaf.obj (op W') : Type u) :=
  (f.kaehlerPresheaf.map (homOfLE i).op).hom w

noncomputable abbrev res {W' W : X.Opens} (i : W' ≤ W) (s : (Γ(f.kaehler, W) : Type u)) :
    (Γ(f.kaehler, W') : Type u) :=
  f.kaehler.val.presheaf.map (homOfLE i).op s

lemma res_toSh {W' W : X.Opens} (i : W' ≤ W) (w : (f.kaehlerPresheaf.obj (op W) : Type u)) :
    res f i (f.kaehlerToSections W w) = f.kaehlerToSections W' (pmap f i w) := by
  have hnat := (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    f.kaehlerPresheaf)).naturality (homOfLE i).op
  exact (congrArg (fun φ => φ.hom w) hnat).symm

lemma algebraMap_sections_eq {U W : X.Opens} (h : W ≤ U) (a : A) :
    letI := f.sectionsAlgebra U
    letI := f.sectionsAlgebra W
    algebraMap A Γ(X, W) a = (X.presheaf.map (homOfLE h).op).hom (algebraMap A Γ(X, U) a) := by
  have := congrArg (fun φ => φ.hom a) (f.constToPresheaf.naturality (homOfLE h).op)
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, CommRingCat.hom_comp] at this
  exact this

theorem main (d : ℕ) [SmoothOfRelativeDimension d f] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ e : Fin d → Γ(f.kaehler, U),
      ∀ (W : X.Opens) (hW : W ≤ U), IsAffineOpen W →
        ∃ b : Module.Basis (Fin d) Γ(X, W) Γ(f.kaehler, W),
          ∀ i, b i = f.kaehler.presheaf.map (homOfLE hW).op (e i) := by
  classical

  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hloc : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d)
      (f.appLE ⊤ V le_top).hom :=
    HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension d) f inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  obtain ⟨s, hs, hP⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).mp hloc

  have hcov : V ≤ ⨆ t : (↑s : Set Γ(X, V)), X.basicOpen (t : Γ(X, V)) :=
    hV.self_le_iSup_basicOpen_iff.mpr hs
  obtain ⟨⟨t, hts⟩, hxt⟩ : ∃ t : (↑s : Set Γ(X, V)), x ∈ X.basicOpen (t : Γ(X, V)) :=
    Opens.mem_iSup.mp (hcov hxV)
  have hU : IsAffineOpen (X.basicOpen t) := hV.basicOpen t
  haveI : IsLocalization.Away t Γ(X, X.basicOpen t) := hV.isLocalization_basicOpen t
  have hstd : RingHom.IsStandardSmoothOfRelativeDimension d
      ((algebraMap Γ(X, V) Γ(X, X.basicOpen t)).comp (f.appLE ⊤ V le_top).hom) :=
    hP t (Finset.mem_coe.mp hts) Γ(X, X.basicOpen t)

  letI algU : Algebra A Γ(X, X.basicOpen t) := f.sectionsAlgebra (X.basicOpen t)
  have hstdU : Algebra.IsStandardSmoothOfRelativeDimension d A Γ(X, X.basicOpen t) := by
    have h1 : (algebraMap Γ(X, V) Γ(X, X.basicOpen t)).comp (f.appLE ⊤ V le_top).hom =
        (f.appLE ⊤ (X.basicOpen t) le_top).hom := by
      change (f.appLE ⊤ V le_top ≫ X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom = _
      rw [Scheme.Hom.appLE_map]
    rw [h1] at hstd
    have h2 := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2
      (f.appLE ⊤ (X.basicOpen t) le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm hstd
    have h3 : (f.appLE ⊤ (X.basicOpen t) le_top).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm.toRingHom =
          (f.constToPresheaf.app (op (X.basicOpen t))).hom := by
      ext a; rfl
    rw [h3] at h2
    exact h2

  obtain ⟨b₀⟩ : Nonempty (Module.Basis (Fin d) Γ(X, X.basicOpen t) (Ω[Γ(X, X.basicOpen t)⁄A])) := by
    obtain ⟨ι, σ, _, _, P, hP⟩ := hstdU.out
    letI := Fintype.ofFinite ι
    letI := Fintype.ofFinite σ
    have hcard : Fintype.card ((Set.range P.map)ᶜ : Set ι) = d := by
      rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj, ← hP,
        Algebra.Presentation.dimension, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact ⟨P.basisKaehler.reindex (Fintype.equivFinOfCardEq hcard)⟩

  refine ⟨X.basicOpen t, hxt, fun i => f.kaehlerToSections (X.basicOpen t)
    (show (f.kaehlerPresheaf.obj (op (X.basicOpen t)) : Type u) from b₀ i), ?_⟩
  intro W hW hWaff
  letI algW : Algebra A Γ(X, W) := f.sectionsAlgebra W
  letI algUW : Algebra Γ(X, X.basicOpen t) Γ(X, W) := (X.presheaf.map (homOfLE hW).op).hom.toAlgebra
  haveI : IsScalarTower A Γ(X, X.basicOpen t) Γ(X, W) :=
    IsScalarTower.of_algebraMap_eq fun a => algebraMap_sections_eq f hW a

  haveI : Algebra.FormallyEtale Γ(X, X.basicOpen t) Γ(X, W) := by
    have hE : RingHom.Etale ((𝟙 X : X ⟶ X).appLE (X.basicOpen t) W hW).hom :=
      HasRingHomProperty.appLE (P := @Etale) (𝟙 X) inferInstance ⟨X.basicOpen t, hU⟩ ⟨W, hWaff⟩ hW
    have hE' : RingHom.Etale (X.presheaf.map (homOfLE hW).op).hom := hE
    exact hE'.formallyEtale
  let κ := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A Γ(X, X.basicOpen t) Γ(X, W)
  let bW : Module.Basis (Fin d) Γ(X, W) (Ω[Γ(X, W)⁄A]) :=
    (Algebra.TensorProduct.basis Γ(X, W) b₀).map κ
  have hbW : ∀ i, bW i = pmap f hW (show (f.kaehlerPresheaf.obj (op (X.basicOpen t)) : Type u) from b₀ i) := by
    intro i
    change κ (Algebra.TensorProduct.basis Γ(X, W) b₀ i) = _
    rw [Algebra.TensorProduct.basis_apply]
    change KaehlerDifferential.mapBaseChange A Γ(X, X.basicOpen t) Γ(X, W) (1 ⊗ₜ b₀ i) = _
    rw [KaehlerDifferential.mapBaseChange_tmul, one_smul]
    rfl

  have hbij := AlgebraicGeometry.Scheme.Hom.kaehlerToSections_bijective_of_isAffineOpen f hWaff
  let τ : (Ω[Γ(X, W)⁄A]) ≃ₗ[Γ(X, W)] (Γ(f.kaehler, W) : Type u) :=
    LinearEquiv.ofBijective (f.kaehlerToSectionsₗ W) hbij
  refine ⟨bW.map τ, fun i => ?_⟩
  rw [Module.Basis.map_apply, hbW]
  change f.kaehlerToSections W (pmap f hW _) = _
  rw [← res_toSh]
  rfl

end KAFrameGC6

theorem solution
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (d : ℕ) [SmoothOfRelativeDimension d f] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ e : Fin d → Γ(f.kaehler, U),
      ∀ (W : X.Opens) (hW : W ≤ U), IsAffineOpen W →
        ∃ b : Module.Basis (Fin d) Γ(X, W) Γ(f.kaehler, W),
          ∀ i, b i = f.kaehler.presheaf.map (homOfLE hW).op (e i) :=
  KAFrameGC6.main f d x

end S_AlgebraicGeometry_Scheme_Hom_exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension (solution)
