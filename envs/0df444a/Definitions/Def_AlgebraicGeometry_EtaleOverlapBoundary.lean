-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleOverlapBoundary
-- name    : AlgebraicGeometry_EtaleOverlapBoundary
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-26T02:57:21.642808+00:00
-- url     : https://prove2.me/theorems/3242de84-a8e2-4275-bbae-f93f0f9ff4c6
-- title:
--   Mayer–Vietoris boundary on a two-open cover
-- statement:
--   If first cohomology vanishes on both opens, each degree-one class comes from a section of the overlap.
-- source:
--   Mayer–Vietoris and the finite model method for étale cohomology.

import Definitions.Def_AlgebraicGeometry_EtaleOpenCoefficientComparison
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponEtaleExtensionByZero (restrict)
open PhilipponEtalePullbackComposition (pullbackCompIso)
open PhilipponEtaleSmallSite (pullbackSheaves)


namespace PhilipponEtaleMayerVietoris

universe u

variable {X : Scheme.{u}} (U V : X.Opens)

private abbrev terminal (X : Scheme.{u}) : X.Etale := Scheme.Etale.mk (𝟙 X)
private abbrev openChart (U : X.Opens) : X.Etale := Scheme.Etale.mk U.ι

private def inclusion (U : X.Opens) : openChart U ⟶ terminal X :=
  MorphismProperty.Over.homMk U.ι (Category.comp_id _) trivial

private def intersectionMap {U V : X.Opens} (h : U ≤ V) : openChart U ⟶ openChart V :=
  MorphismProperty.Over.homMk (X.homOfLE h) (X.homOfLE_ι h) trivial

private def square : Square X.Etale where
  X₁ := openChart (U ⊓ V)
  X₂ := openChart U
  X₃ := openChart V
  X₄ := terminal X
  f₁₂ := intersectionMap inf_le_left
  f₁₃ := intersectionMap inf_le_right
  f₂₄ := inclusion U
  f₃₄ := inclusion V
  fac := MorphismProperty.Over.Hom.ext
    ((X.homOfLE_ι inf_le_left).trans (X.homOfLE_ι inf_le_right).symm)

private abbrev underlying (X : Scheme.{u}) : X.Etale ⥤ Scheme.{u} :=
  Scheme.Etale.forget X ⋙ Over.forget X

private instance (U : X.Opens) : Mono (inclusion U) :=
  Functor.mono_of_mono_map (underlying X) (inferInstanceAs (Mono U.ι))

private theorem isPullback_square : (square U V).IsPullback :=
  IsPullback.of_map (underlying X) (square U V).fac (isPullback_opens_inf U V)

private theorem opens_cover (h : U ⊔ V = ⊤) :
    Sieve.ofTwoArrows (inclusion U) (inclusion V) ∈ X.smallEtaleTopology (terminal X) := by
  rw [Sieve.ofTwoArrows, Scheme.ofArrows_mem_smallEtaleTopology_iff]
  refine Set.eq_univ_of_forall ?_
  intro x
  have hx : x ∈ U ⊔ V := h.symm ▸ (show x ∈ (⊤ : X.Opens) from trivial)
  rcases hx with hx | hx
  · exact Set.mem_iUnion.mpr ⟨WalkingPair.left, ⟨⟨x, hx⟩, rfl⟩⟩
  · exact Set.mem_iUnion.mpr ⟨WalkingPair.right, ⟨⟨x, hx⟩, rfl⟩⟩

/-- Two open subschemes covering a scheme give a Mayer–Vietoris square in
the small étale site. -/
def mayerVietoris (h : U ⊔ V = ⊤) : X.smallEtaleTopology.MayerVietorisSquare := by
  let : Mono (square U V).f₂₄ := inferInstanceAs (Mono (inclusion U))
  let : Mono (square U V).f₃₄ := inferInstanceAs (Mono (inclusion V))
  exact GrothendieckTopology.MayerVietorisSquare.mk_of_isPullback
    (J := X.smallEtaleTopology) (square U V) (isPullback_square U V) (opens_cover U V h)

private def terminalChartIsTerminal (X : Scheme.{u}) : IsTerminal (terminal X) :=
  IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) _ Over.mkIdTerminal

/-- The connecting map from degree-zero cohomology of the overlap to degree-one
cohomology of the whole scheme. -/
def overlapBoundary (h : U ⊔ V = ⊤)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    F.H' 0 (openChart (U ⊓ V)) →+ F.H 1 :=
  ((PhilipponSheafCohomology.terminalComparison X.smallEtaleTopology
    (terminalChartIsTerminal X) F 1).symm.toAddMonoidHom).comp
      (((mayerVietoris U V h).δ F 0 1 rfl).hom)

/-- The overlap boundary commutes with a change of coefficient sheaf. -/
theorem overlapBoundary_naturality (h : U ⊔ V = ⊤)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (a : F ⟶ G)
    (t : F.H' 0 (openChart (U ⊓ V))) :
    overlapBoundary U V h G (t.comp (Ext.mk₀ a) rfl) =
      Sheaf.H.map a 1 (overlapBoundary U V h F t) := by
  let S := mayerVietoris U V h
  let e := PhilipponSheafCohomology.freeTerminalIso X.smallEtaleTopology (terminalChartIsTerminal X)
  let d := S.shortComplex_shortExact.extClass
  change (Ext.mk₀ e.inv).comp (d.comp (t.comp (Ext.mk₀ a) rfl) rfl) rfl =
    ((Ext.mk₀ e.inv).comp (d.comp t rfl) rfl).comp (Ext.mk₀ a) rfl
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero]

/-- If degree-one cohomology vanishes on both members of the cover, every
degree-one class is the boundary of a section on the overlap. -/
theorem overlapBoundary_surjective (h : U ⊔ V = ⊤)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (hU : Subsingleton (((restrict U.ι).obj F).H 1))
    (hV : Subsingleton (((restrict V.ι).obj F).H 1)) :
    Function.Surjective (overlapBoundary U V h F) := by
  let S := mayerVietoris U V h
  let e := PhilipponSheafCohomology.terminalComparison X.smallEtaleTopology
    (terminalChartIsTerminal X) F 1
  let _ := hU
  let _ := hV
  have z₂ : IsZero (F.H' 1 S.X₂) := AddCommGrpCat.isZero_iff_subsingleton.mpr
    ((PhilipponEtaleOpenCohomology.openComparison U.ι F 1).injective.subsingleton)
  have z₃ : IsZero (F.H' 1 S.X₃) := AddCommGrpCat.isZero_iff_subsingleton.mpr
    ((PhilipponEtaleOpenCohomology.openComparison V.ι F 1).injective.subsingleton)
  have hTo : S.toBiprod F 1 = 0 := by
    apply biprod.hom_ext
    · exact z₂.eq_of_tgt _ _
    · exact z₃.eq_of_tgt _ _
  have hexact : Function.Exact (S.δ F 0 1 rfl) (S.toBiprod F 1) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp ((S.sequence_exact F 0 1 rfl).exact 2)
  intro x
  obtain ⟨t, ht⟩ := (hexact (e x)).mp (by rw [hTo]; rfl)
  exact ⟨t, e.symm_apply_eq.mpr ht⟩

end PhilipponEtaleMayerVietoris

end

end


