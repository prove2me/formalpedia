-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.isInvertible_I
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/3333f517-177f-5fec-8b43-0f74a13976a0

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_ker_graphOver_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_of_isInvertible_comap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme.Hom.le_ker_comp SmoothOfRelativeDimension Scheme.Hom IsFinite Scheme Smooth Scheme.ker_eq_top_of_isEmpty Scheme.IdealSheafData.ker_fst_of_isClosedImmersion Scheme.IdealSheafData.ker_subschemeι Scheme.Hom.one_le_finrank_map Flat IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Hom.ker Scheme.Hom.one_le_finrank_iff_surjective Scheme.IdealSheafData graphOver graphOver_fst graphOver_snd graphOver_snd_assoc RelEffCartierDiv mapOnProdOver mapOnProdOver_fst mapOnProdOver_snd isPullback_mapOnProdOver Scheme.IdealSheafData.isInvertible_top Scheme.Hom.isInvertible_ker_of_comp_eq_id RelEffCartierDiv.exists_I_eq_ker_graphOver_mul Scheme.IdealSheafData.isInvertible_of_isInvertible_comap"
namespace RelEffCartierDiv
p2m_export "AlgebraicGeometry.RelEffCartierDiv" "pullbackAlong I flat isFinite finrank_eq locallyOfFinitePresentation exists_I_eq_ker_graphOver_mul"
namespace CartierInduction
p2m_open "AlgebraicGeometry.RelEffCartierDiv AlgebraicGeometry"

variable {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]

theorem I_eq_top_of_degree_zero {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f 0 g) :
    D.I = ⊤ := by
  have := D.isFinite
  have := D.flat
  have hempty : IsEmpty ↥D.I.subscheme := by
    by_contra h
    rw [not_isEmpty_iff] at h
    obtain ⟨x⟩ := h
    have h1 := Scheme.Hom.one_le_finrank_map (D.I.subschemeι ≫ pullback.snd f g) x
    rw [D.finrank_eq] at h1
    exact Nat.not_succ_le_zero 0 h1
  rw [← D.I.ker_subschemeι]
  exact Scheme.ker_eq_top_of_isEmpty _

theorem step (r : ℕ)
    (ih : ∀ {T : Scheme.{u}} {g : T ⟶ S} (E : RelEffCartierDiv f r g), E.I.IsInvertible)
    {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f (r + 1) g) : D.I.IsInvertible := by
  have := D.isFinite
  have := D.flat
  have := D.locallyOfFinitePresentation

  let π : D.I.subscheme ⟶ T := D.I.subschemeι ≫ pullback.snd f g
  haveI : Surjective π := by
    refine (Scheme.Hom.one_le_finrank_iff_surjective π).mp fun t => ?_
    show 1 ≤ (D.I.subschemeι ≫ pullback.snd f g).finrank t
    rw [D.finrank_eq t]
    exact Nat.succ_le_succ (Nat.zero_le r)
  let g' : D.I.subscheme ⟶ S := π ≫ g
  have hπ : π ≫ g = g' := rfl
  let D' : RelEffCartierDiv f (r + 1) g' := D.pullbackAlong π hπ

  let a : D.I.subscheme ⟶ 𝒞 := D.I.subschemeι ≫ pullback.fst f g
  have ha : a ≫ f = g' := by
    simp only [a, g', π, Category.assoc, pullback.condition]
  have hgraph : graphOver f a ha ≫ mapOnProdOver f π hπ = D.I.subschemeι := by
    apply pullback.hom_ext
    · rw [Category.assoc, mapOnProdOver_fst, graphOver_fst]
    · rw [Category.assoc, mapOnProdOver_snd, graphOver_snd_assoc]
  have hle : D'.I ≤ (graphOver f a ha).ker := by
    change D.I.comap (mapOnProdOver f π hπ) ≤ _
    have hcomap : D.I.comap (mapOnProdOver f π hπ) =
        (pullback.fst (mapOnProdOver f π hπ) D.I.subschemeι).ker := by
      rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, Scheme.IdealSheafData.ker_subschemeι]
    rw [hcomap]
    have hfac : pullback.lift (graphOver f a ha) (𝟙 _) (by rw [hgraph, Category.id_comp]) ≫
        pullback.fst (mapOnProdOver f π hπ) D.I.subschemeι = graphOver f a ha :=
      pullback.lift_fst _ _ _
    exact le_of_le_of_eq (Scheme.Hom.le_ker_comp _ _) (congrArg Scheme.Hom.ker hfac)

  obtain ⟨E, hE⟩ := RelEffCartierDiv.exists_I_eq_ker_graphOver_mul D' a ha hle

  have hgr : (graphOver f a ha).ker.IsInvertible := by
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    haveI : SmoothOfRelativeDimension 1 (pullback.snd f g') :=
      MorphismProperty.pullback_snd _ _ inferInstance
    exact Scheme.Hom.isInvertible_ker_of_comp_eq_id (graphOver f a ha) (graphOver_snd f a ha)
  have hD' : (D.I.comap (mapOnProdOver f π hπ)).IsInvertible := by
    change D'.I.IsInvertible
    rw [hE]
    exact hgr.mul (ih E)

  have hbc := (isPullback_mapOnProdOver f π hπ).flip
  haveI : IsFinite (mapOnProdOver f π hπ) := MorphismProperty.of_isPullback hbc inferInstance
  haveI : Flat (mapOnProdOver f π hπ) := MorphismProperty.of_isPullback hbc inferInstance
  haveI : Surjective (mapOnProdOver f π hπ) := MorphismProperty.of_isPullback hbc inferInstance
  exact Scheme.IdealSheafData.isInvertible_of_isInvertible_comap (mapOnProdOver f π hπ) D.I hD'

theorem isInvertible : ∀ (r : ℕ) {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g),
    D.I.IsInvertible
  | 0, _, _, D => by
    rw [I_eq_top_of_degree_zero D]
    exact Scheme.IdealSheafData.isInvertible_top
  | r + 1, _, _, D => step r (fun E => isInvertible r E) D

end AlgebraicGeometry.RelEffCartierDiv.CartierInduction

theorem solution {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {r : ℕ} {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g) : D.I.IsInvertible :=
  AlgebraicGeometry.RelEffCartierDiv.CartierInduction.isInvertible r D

end S_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I (solution)
