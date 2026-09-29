-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_opens_forall_range_subset_iff_eq_univ_of_forall_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/5ffeeb4e-ce8a-5833-8d50-4e6868ebfa6e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_opens_forall_range_subset_iff_eq_univ_of_forall_isOpen

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

noncomputable section

namespace O0

variable (E : Scheme.{u})
  (U : ∀ (R : Type u) [CommRing R], (Spec (CommRingCat.of R) ⟶ E) → Set ↥(Spec (CommRingCat.of R)))
  (hUopen : ∀ (R : Type u) [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E), IsOpen (U R s))
  (hU : ∀ (R R' : Type u) [CommRing R] [CommRing R'] (ψ : R →+* R') (s : Spec (CommRingCat.of R) ⟶ E),
      U R' (Spec.map (CommRingCat.ofHom ψ) ≫ s) = (Spec.map (CommRingCat.ofHom ψ)).base ⁻¹' (U R s))

def chartSet (W : E.affineOpens) : Set E := W.2.fromSpec.base '' (U (Γ(E, W)) W.2.fromSpec)

include hUopen in
theorem isOpen_chartSet (W : E.affineOpens) : IsOpen (chartSet E U W) :=
  W.2.fromSpec.isOpenEmbedding.isOpenMap _ (hUopen _ _)

def Vopen : E.Opens := ⟨⋃ W : E.affineOpens, chartSet E U W, isOpen_iUnion fun W => isOpen_chartSet E U hUopen W⟩

theorem mem_Vopen_iff (e : E) : e ∈ (Vopen E U hUopen : Set E) ↔ ∃ W : E.affineOpens, e ∈ chartSet E U W := by
  show e ∈ (⋃ W : E.affineOpens, chartSet E U W) ↔ _
  exact Set.mem_iUnion

section AffinePoints

variable (R : Type u) [CommRing R]

def ψV (V : (Spec (CommRingCat.of R)).affineOpens) : R →+* Γ(Spec (CommRingCat.of R), V) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ (Spec (CommRingCat.of R)).presheaf.map (homOfLE le_top).op).hom

theorem fromSpec_eq_specMap_ψV (V : (Spec (CommRingCat.of R)).affineOpens) :
    V.2.fromSpec = Spec.map (CommRingCat.ofHom (ψV R V)) := by
  rw [ψV, CommRingCat.ofHom_hom, Spec.map_comp, ← IsAffineOpen.fromSpec_toSpecΓ, Category.assoc,
    ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

end AffinePoints

variable {E}

include hU in

theorem exists_local {R : Type u} [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E)
    (W : E.affineOpens) (x : ↥(Spec (CommRingCat.of R))) (hx : s.base x ∈ (W.1 : Set E)) :
    ∃ (V : (Spec (CommRingCat.of R)).affineOpens) (θ : Γ(E, W) ⟶ Γ(Spec (CommRingCat.of R), V))
      (y : ↥(Spec Γ(Spec (CommRingCat.of R), V))),
      V.2.fromSpec.base y = x ∧
      Spec.map θ ≫ W.2.fromSpec = V.2.fromSpec ≫ s ∧
      V.2.fromSpec.base ⁻¹' (U R s) = (Spec.map θ).base ⁻¹' (U (Γ(E, W)) W.2.fromSpec) := by
  obtain ⟨V, hVaff, hxV, hVle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Spec (CommRingCat.of R)).isBasis_affineOpens) (show x ∈ s ⁻¹ᵁ W.1 from hx)
  let VV : (Spec (CommRingCat.of R)).affineOpens := ⟨V, hVaff⟩
  have hrange : Set.range (VV.2.fromSpec ≫ s).base ⊆ Set.range W.1.ι.base := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hy : VV.2.fromSpec.base y ∈ (V : Set _) := by
      have : VV.2.fromSpec.base y ∈ Set.range VV.2.fromSpec.base := ⟨y, rfl⟩
      rwa [IsAffineOpen.range_fromSpec] at this
    rw [Scheme.Hom.comp_apply]
    exact hVle hy
  obtain ⟨θ, hθ⟩ := Spec.map_surjective (IsOpenImmersion.lift W.1.ι _ hrange ≫ W.2.isoSpec.hom)
  have hfac : Spec.map θ ≫ W.2.fromSpec = VV.2.fromSpec ≫ s := by
    rw [hθ, Category.assoc, ← IsAffineOpen.isoSpec_inv_ι (hU := W.2), W.2.isoSpec.hom_inv_id_assoc, IsOpenImmersion.lift_fac]
  have hxr : x ∈ Set.range VV.2.fromSpec.base := by rw [IsAffineOpen.range_fromSpec]; exact hxV
  obtain ⟨y, hy⟩ := hxr
  refine ⟨VV, θ, y, hy, hfac, ?_⟩
  have h1 := hU (Γ(E, W)) (Γ(Spec (CommRingCat.of R), V)) θ.hom W.2.fromSpec
  rw [CommRingCat.ofHom_hom] at h1
  have h2 := hU R (Γ(Spec (CommRingCat.of R), V)) (ψV R VV) s
  rw [← fromSpec_eq_specMap_ψV] at h2
  rw [← h1, ← h2, hfac]

include hUopen hU in
theorem preimage_Vopen_eq {R : Type u} [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E) :
    s.base ⁻¹' (Vopen E U hUopen : Set E) = U R s := by
  ext x
  simp only [Set.mem_preimage, mem_Vopen_iff]
  constructor
  · rintro ⟨W, z, hz, hzx⟩

    have hxW : s.base x ∈ (W.1 : Set E) := by
      rw [← hzx, ← IsAffineOpen.range_fromSpec (hU := W.2)]; exact ⟨z, rfl⟩
    obtain ⟨V, θ, y, hyx, hfac, hpre⟩ := exists_local U hU s W x hxW
    have hzy : (Spec.map θ).base y = z := by
      apply W.2.fromSpec.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hfac, Scheme.Hom.comp_apply, hyx, hzx]
    have : y ∈ V.2.fromSpec.base ⁻¹' (U R s) := by
      rw [hpre, Set.mem_preimage, hzy]; exact hz
    rw [Set.mem_preimage] at this
    rw [← hyx]; exact this
  · intro hx
    obtain ⟨W', hW', hxW, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp E.isBasis_affineOpens)
      (TopologicalSpace.Opens.mem_top (s.base x))
    let W : E.affineOpens := ⟨W', hW'⟩
    obtain ⟨V, θ, y, hyx, hfac, hpre⟩ := exists_local U hU s W x hxW
    have hy : y ∈ V.2.fromSpec.base ⁻¹' (U R s) := by rw [Set.mem_preimage, hyx]; exact hx
    rw [hpre] at hy
    refine ⟨W, (Spec.map θ).base y, hy, ?_⟩
    rw [← Scheme.Hom.comp_apply, hfac, Scheme.Hom.comp_apply, hyx]

include hUopen hU in
theorem main : ∃ V : E.Opens,
      (∀ (R : Type u) [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E), s.base ⁻¹' (V : Set E) = U R s) ∧
      ∀ (R : Type u) [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E),
        Set.range s.base ⊆ (V : Set E) ↔ U R s = Set.univ := by
  refine ⟨Vopen E U hUopen, fun R _ s => preimage_Vopen_eq U hUopen hU s, fun R _ s => ?_⟩
  rw [← Set.preimage_eq_univ_iff, preimage_Vopen_eq U hUopen hU s]

end O0

end

theorem solution
    (E : Scheme.{u})
    (U : ∀ (R : Type u) [CommRing R], (Spec (CommRingCat.of R) ⟶ E) → Set ↥(Spec (CommRingCat.of R)))
    (hUopen : ∀ (R : Type u) [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E), IsOpen (U R s))
    (hU : ∀ (R R' : Type u) [CommRing R] [CommRing R'] (ψ : R →+* R') (s : Spec (CommRingCat.of R) ⟶ E),
      U R' (Spec.map (CommRingCat.ofHom ψ) ≫ s) = (Spec.map (CommRingCat.ofHom ψ)).base ⁻¹' (U R s)) :
    ∃ V : E.Opens,
      (∀ (R : Type u) [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E), s.base ⁻¹' (V : Set E) = U R s) ∧
      ∀ (R : Type u) [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E),
        Set.range s.base ⊆ (V : Set E) ↔ U R s = Set.univ :=
  O0.main U hUopen hU

end S_AlgebraicGeometry_Scheme_exists_opens_forall_range_subset_iff_eq_univ_of_forall_isOpen
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_opens_forall_range_subset_iff_eq_univ_of_forall_isOpen (solution)
