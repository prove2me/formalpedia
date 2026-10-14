-- Prove2me | solution 1 for AlgebraicGeometry.SmoothProperCurve.exists_linearEquiv_cech_pushforward_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-13T17:43:52.984716+00:00
-- url     : https://prove2.me/submissions/4d47f251-df84-4f3e-80e9-0604991cc125

import Definitions.Def_AlgebraicGeometry_CurveDegreeTests
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_H1_sectionsOf_of_isInvertible

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover.FinitePushforward
open CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

/-- The inverse image of the two affine charts under an affine morphism. -/
def inverseImage (𝒰 : Y.TwoAffineOpenCover) (g : X ⟶ Y) [IsAffineHom g] :
    X.TwoAffineOpenCover where
  U0 := g ⁻¹ᵁ 𝒰.U0
  U1 := g ⁻¹ᵁ 𝒰.U1
  isAffineOpen_U0 := 𝒰.isAffineOpen_U0.preimage g
  isAffineOpen_U1 := 𝒰.isAffineOpen_U1.preimage g
  sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒰.sup_eq_top]; rfl
  isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒰.isAffineOpen_inf.preimage g

/-- Scalar restriction agrees with the structure morphism after composition. -/
def sectionsEquiv (c : Y ⟶ Spec (.of R)) (g : X ⟶ Y) (M : X.Modules) (U : Y.Opens) :
    letI := moduleSectionsOfHom c ((Scheme.Modules.pushforward g).obj M) U
    letI := moduleSectionsOfHom (g ≫ c) M (g ⁻¹ᵁ U)
    Γ((Scheme.Modules.pushforward g).obj M, U) ≃ₗ[R] Γ(M, g ⁻¹ᵁ U) := by
  letI := moduleSectionsOfHom c ((Scheme.Modules.pushforward g).obj M) U
  letI := moduleSectionsOfHom (g ≫ c) M (g ⁻¹ᵁ U)
  refine
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := ?_ }
  intro r x
  let y : Γ(M, g ⁻¹ᵁ U) := x
  change ((g.app U).hom ((c.appLE ⊤ U le_top).hom
      ((Scheme.ΓSpecIso (.of R)).inv.hom r))) • y =
    ((g ≫ c).appLE ⊤ (g ⁻¹ᵁ U) le_top).hom
      ((Scheme.ΓSpecIso (.of R)).inv.hom r) • y
  congr 1
  change ((c.appLE ⊤ U le_top ≫ g.app U).hom _) = _
  rw [g.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]

/-- The inverse-image and pushforward complexes have the same degree-zero terms. -/
def degreeZeroEquiv (𝒰 : Y.TwoAffineOpenCover) (c : Y ⟶ Spec (.of R))
    (g : X ⟶ Y) [IsAffineHom g] (M : X.Modules) :
    ((𝒰.sectionsOf c ((Scheme.Modules.pushforward g).obj M)).M0 ×
      (𝒰.sectionsOf c ((Scheme.Modules.pushforward g).obj M)).M1) ≃ₗ[R]
    (((inverseImage 𝒰 g).sectionsOf (g ≫ c) M).M0 ×
      ((inverseImage 𝒰 g).sectionsOf (g ≫ c) M).M1) :=
  (sectionsEquiv c g M 𝒰.U0).prodCongr (sectionsEquiv c g M 𝒰.U1)

/-- The degree-one terms agree on the inverse image of the intersection. -/
def degreeOneEquiv (𝒰 : Y.TwoAffineOpenCover) (c : Y ⟶ Spec (.of R))
    (g : X ⟶ Y) [IsAffineHom g] (M : X.Modules) :
    (𝒰.sectionsOf c ((Scheme.Modules.pushforward g).obj M)).M01 ≃ₗ[R]
      ((inverseImage 𝒰 g).sectionsOf (g ≫ c) M).M01 :=
  sectionsEquiv c g M (𝒰.U0 ⊓ 𝒰.U1)

/-- These identifications respect the two restriction maps and their difference. -/
theorem cechDiff_commutes (𝒰 : Y.TwoAffineOpenCover) (c : Y ⟶ Spec (.of R))
    (g : X ⟶ Y) [IsAffineHom g] (M : X.Modules)
    (s : (𝒰.sectionsOf c ((Scheme.Modules.pushforward g).obj M)).M0 ×
      (𝒰.sectionsOf c ((Scheme.Modules.pushforward g).obj M)).M1) :
    ((inverseImage 𝒰 g).sectionsOf (g ≫ c) M).cechDiff (degreeZeroEquiv 𝒰 c g M s) =
      degreeOneEquiv 𝒰 c g M ((𝒰.sectionsOf c ((Scheme.Modules.pushforward g).obj M)).cechDiff s) :=
  rfl

/-- The kernel comparison induced by the isomorphism of complexes. -/
def pushforwardH0Equiv (𝒰 : Y.TwoAffineOpenCover) (c : Y ⟶ Spec (.of R))
    (g : X ⟶ Y) [IsAffineHom g] (M : X.Modules) :
    (𝒰.sectionsOf c ((Scheme.Modules.pushforward g).obj M)).H0 ≃ₗ[R]
      ((inverseImage 𝒰 g).sectionsOf (g ≫ c) M).H0 := by
  apply (degreeZeroEquiv 𝒰 c g M).ofSubmodules
  ext s
  constructor
  · rintro ⟨t, ht, rfl⟩
    change _ = 0
    exact (cechDiff_commutes 𝒰 c g M t).trans
      ((congrArg (degreeOneEquiv 𝒰 c g M) ht).trans (map_zero _))
  · intro hs
    refine ⟨(degreeZeroEquiv 𝒰 c g M).symm s, ?_, by simp⟩
    apply (degreeOneEquiv 𝒰 c g M).injective
    rw [map_zero, ← cechDiff_commutes, LinearEquiv.apply_symm_apply]
    exact hs

/-- The cokernel comparison induced by the same isomorphism of complexes. -/
def pushforwardH1Equiv (𝒰 : Y.TwoAffineOpenCover) (c : Y ⟶ Spec (.of R))
    (g : X ⟶ Y) [IsAffineHom g] (M : X.Modules) :
    (𝒰.sectionsOf c ((Scheme.Modules.pushforward g).obj M)).H1 ≃ₗ[R]
      ((inverseImage 𝒰 g).sectionsOf (g ≫ c) M).H1 := by
  apply Submodule.Quotient.equiv _ _ (degreeOneEquiv 𝒰 c g M)
  ext s
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨degreeZeroEquiv 𝒰 c g M t, cechDiff_commutes 𝒰 c g M t⟩
  · rintro ⟨t, rfl⟩
    refine ⟨_, ⟨(degreeZeroEquiv 𝒰 c g M).symm t, rfl⟩, ?_⟩
    exact (cechDiff_commutes 𝒰 c g M ((degreeZeroEquiv 𝒰 c g M).symm t)).symm.trans
      (congrArg ((inverseImage 𝒰 g).sectionsOf (g ≫ c) M).cechDiff
        ((degreeZeroEquiv 𝒰 c g M).apply_symm_apply t))

end AlgebraicGeometry.Scheme.TwoAffineOpenCover.FinitePushforward

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlobalSections
open CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

theorem restrict_comp (M : X.Modules) {U V W : X.Opens}
    (hUV : V ≤ U) (hVW : W ≤ V) (s : Γ(M, U)) :
    M.presheaf.map (homOfLE hVW).op (M.presheaf.map (homOfLE hUV).op s) =
      M.presheaf.map (homOfLE (hVW.trans hUV)).op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restriction of a global section to a compatible pair on the two charts. -/
def toH0 (𝒰 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R)) (M : X.Modules) :
    letI := moduleSectionsOfHom c M ⊤
    Γ(M, ⊤) →ₗ[R] (𝒰.sectionsOf c M).H0 := by
  letI := moduleSectionsOfHom c M ⊤
  letI := moduleSectionsOfHom c M 𝒰.U0
  letI := moduleSectionsOfHom c M 𝒰.U1
  refine LinearMap.codRestrict _
    ((restrictSections c M (le_top : 𝒰.U0 ≤ ⊤)).prod
      (restrictSections c M (le_top : 𝒰.U1 ≤ ⊤))) ?_
  intro s
  apply (TwoChartCech.Sections.mem_H0_iff _ _).mpr
  change M.presheaf.map _ (M.presheaf.map _ s) = M.presheaf.map _ (M.presheaf.map _ s)
  rw [restrict_comp, restrict_comp]

/-- Uniqueness in the sheaf condition makes global restriction injective. -/
theorem toH0_injective (𝒰 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (M : X.Modules) : Function.Injective (toH0 𝒰 c M) := by
  intro s t h
  have h0 := congrArg (fun z : (𝒰.sectionsOf c M).H0 => z.val.1) h
  have h1 := congrArg (fun z : (𝒰.sectionsOf c M).H0 => z.val.2) h
  apply M.isSheaf.section_ext
  intro x hx
  have hxU : x ∈ 𝒰.U0 ⊔ 𝒰.U1 := by rw [𝒰.sup_eq_top]; trivial
  rcases hxU with hx0 | hx1
  · exact ⟨𝒰.U0, le_top, hx0, h0⟩
  · exact ⟨𝒰.U1, le_top, hx1, h1⟩

/-- Existence in the sheaf condition glues every compatible pair. -/
theorem toH0_surjective (𝒰 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (M : X.Modules) : Function.Surjective (toH0 𝒰 c M) := by
  intro s
  let W : Bool → X.Opens := fun b => if b then 𝒰.U1 else 𝒰.U0
  let sf : ∀ b : Bool, Γ(M, W b) := fun b => by
    cases b
    · exact s.val.1
    · exact s.val.2
  have hc : TopCat.Presheaf.IsCompatible M.presheaf W sf := by
    intro i j
    cases i <;> cases j
    · rfl
    · exact (TwoChartCech.Sections.mem_H0_iff _ _).mp s.property
    · apply (ConcreteCategory.bijective_of_isIso
        (M.presheaf.map (eqToHom (inf_comm 𝒰.U0 𝒰.U1)).op)).injective
      change M.presheaf.map (homOfLE (inf_comm 𝒰.U0 𝒰.U1).le).op
          (M.presheaf.map (homOfLE (inf_le_left : 𝒰.U1 ⊓ 𝒰.U0 ≤ 𝒰.U1)).op s.val.2) =
        M.presheaf.map (homOfLE (inf_comm 𝒰.U0 𝒰.U1).le).op
          (M.presheaf.map (homOfLE (inf_le_right : 𝒰.U1 ⊓ 𝒰.U0 ≤ 𝒰.U0)).op s.val.1)
      rw [restrict_comp, restrict_comp]
      exact ((TwoChartCech.Sections.mem_H0_iff _ _).mp s.property).symm
    · rfl
  have hcover : (⊤ : X.Opens) ≤ iSup W := by
    rw [iSup_bool_eq]
    change ⊤ ≤ 𝒰.U1 ⊔ 𝒰.U0
    rw [sup_comm, 𝒰.sup_eq_top]
  obtain ⟨t, ht, _⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    W ⊤ (fun _ => homOfLE le_top) hcover sf hc
  refine ⟨t, Subtype.ext (Prod.ext (ht false) (ht true))⟩

/-- The degree-zero Cech module is the module of global sections. -/
def globalSectionsEquiv (𝒰 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R)) (M : X.Modules) :
    letI := moduleSectionsOfHom c M ⊤
    Γ(M, ⊤) ≃ₗ[R] (𝒰.sectionsOf c M).H0 :=
  LinearEquiv.ofBijective (toH0 𝒰 c M) ⟨toH0_injective 𝒰 c M, toH0_surjective 𝒰 c M⟩

/-- Degree-zero cover independence needs only the sheaf condition. -/
def H0CoverEquiv (𝒰 𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R)) (M : X.Modules) :
    (𝒰.sectionsOf c M).H0 ≃ₗ[R] (𝒱.sectionsOf c M).H0 :=
  (globalSectionsEquiv 𝒰 c M).symm.trans (globalSectionsEquiv 𝒱 c M)

end AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlobalSections

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.TwoAffineOpenCover
open AlgebraicGeometry.Scheme.TwoAffineOpenCover.FinitePushforward
open AlgebraicGeometry.Scheme.TwoAffineOpenCover.GlobalSections
universe u

theorem solution
    (K : Type u) [Field K] {C D : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) (δ : D ⟶ Spec (.of K))
    [IsIntegral C] [IsIntegral D] [IsProper c] [IsProper δ]
    [SmoothOfRelativeDimension 1 c] [SmoothOfRelativeDimension 1 δ]
    (g : D ⟶ C) [IsFinite g] (hg : g ≫ c = δ)
    (𝒰 : C.TwoAffineOpenCover) (𝒱 : D.TwoAffineOpenCover)
    (M : D.Modules) (hM : Scheme.Modules.IsInvertible M) :
    Nonempty ((𝒱.sectionsOf δ M).H0 ≃ₗ[K]
      (𝒰.sectionsOf c ((Scheme.Modules.pushforward g).obj M)).H0) ∧
    Nonempty ((𝒱.sectionsOf δ M).H1 ≃ₗ[K]
      (𝒰.sectionsOf c ((Scheme.Modules.pushforward g).obj M)).H1) := by
  subst δ
  refine ⟨⟨(H0CoverEquiv 𝒱 (inverseImage 𝒰 g) (g ≫ c) M).trans
    (pushforwardH0Equiv 𝒰 c g M).symm⟩, ?_⟩
  obtain ⟨e⟩ := exists_linearEquiv_H1_sectionsOf_of_isInvertible
    K (g ≫ c) 𝒱 (inverseImage 𝒰 g) M hM
  exact ⟨e.trans (pushforwardH1Equiv 𝒰 c g M).symm⟩
