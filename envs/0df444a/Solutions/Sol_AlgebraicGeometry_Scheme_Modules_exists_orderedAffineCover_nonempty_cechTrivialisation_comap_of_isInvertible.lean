-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_orderedAffineCover_nonempty_cechTrivialisation_comap_of_isInvertible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/bde7c190-3815-5699-9e79-0cef055ac24c

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_orderedAffineCover_nonempty_cechTrivialisation_comap_of_isInvertible

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

namespace TrivCoverPen

open TopologicalSpace Opposite

noncomputable def restrictTriv {Y : Scheme.{u}} {M : Y.Modules} {V W : Y.Opens} (h : W ≤ V)
    (τ : (Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit ((V : Scheme.{u})).ringCatSheaf) :
    (Scheme.Modules.pullback W.ι).obj M ≅ SheafOfModules.unit ((W : Scheme.{u})).ringCatSheaf :=
  ((Scheme.Modules.pullbackCongr (Y.homOfLE_ι h)).app M).symm ≪≫
    ((Scheme.Modules.pullbackComp (Y.homOfLE h) V.ι).app M).symm ≪≫
    (Scheme.Modules.pullback (Y.homOfLE h)).mapIso τ ≪≫
    Scheme.Modules.pullbackUnitIso (Y.homOfLE h)

theorem isZero_of_isEmpty {Y : Scheme.{u}} [IsEmpty Y] (M : SheafOfModules.{u} Y.ringCatSheaf) :
    Limits.IsZero M := by
  rw [Limits.IsZero.iff_id_eq_zero]
  apply (SheafOfModules.toSheaf Y.ringCatSheaf).map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun U => ?_)
  have hU : U.unop = ⊥ := by
    ext y; exact (IsEmpty.false y).elim
  have hT := TopCat.Sheaf.isTerminalOfEqEmpty (X := Y.carrier)
    ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M) hU
  exact hT.hom_ext _ _

theorem nonempty_iso_of_isEmpty {Y : Scheme.{u}} [IsEmpty Y] (M N : Y.Modules) : Nonempty (M ≅ N) := by
  let e : @Iso (SheafOfModules.{u} Y.ringCatSheaf) _ M N := (isZero_of_isEmpty M).iso (isZero_of_isEmpty N)
  exact ⟨⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩

end TrivCoverPen

theorem solution
    {X X₀ : Scheme.{u}} [CompactSpace X] (g : X₀ ⟶ X) [IsClosedImmersion g]
    (𝓛₀ : X₀.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀) :
    ∃ 𝒰 : X.OrderedAffineCover, Nonempty (Scheme.Modules.CechTrivialisation (𝒰.comap g) 𝓛₀) := by
  classical
  have htriv := h𝓛₀.exists_trivialization

  have key : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj 𝓛₀ ≅
        SheafOfModules.unit ((g ⁻¹ᵁ U : Scheme.{u})).ringCatSheaf) := by
    intro x
    by_cases hx : x ∈ Set.range g.base
    · obtain ⟨x₀, rfl⟩ := hx
      obtain ⟨V₀, hxV₀, ⟨τ⟩⟩ := htriv x₀
      obtain ⟨V', hV'open, hV'⟩ := g.isClosedEmbedding.isInducing.isOpen_iff.mp V₀.isOpen
      have hxV' : g.base x₀ ∈ V' := by
        rw [← Set.mem_preimage, hV']; exact hxV₀
      obtain ⟨_, ⟨U, hUaff, rfl⟩, hxU, hUV'⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxV' hV'open
      refine ⟨U, hUaff, hxU, ⟨TrivCoverPen.restrictTriv ?_ τ⟩⟩
      intro y hy
      have hy' : g.base y ∈ V' := hUV' hy
      rw [← Set.mem_preimage, hV'] at hy'
      exact hy'
    · obtain ⟨_, ⟨U, hUaff, rfl⟩, hxU, hUc⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ (Set.range g.base)ᶜ from hx) g.isClosedEmbedding.isClosed_range.isOpen_compl
      refine ⟨U, hUaff, hxU, ?_⟩
      have hbot : g ⁻¹ᵁ U = ⊥ := le_bot_iff.mp fun y hy => (hUc hy ⟨y, rfl⟩).elim
      by_cases hne : Nonempty X₀
      · obtain ⟨x₁⟩ := hne
        obtain ⟨V₁, -, ⟨τ₁⟩⟩ := htriv x₁
        exact ⟨TrivCoverPen.restrictTriv (show g ⁻¹ᵁ U ≤ V₁ from hbot ▸ bot_le) τ₁⟩
      · haveI : IsEmpty ((g ⁻¹ᵁ U : X₀.Opens) : Scheme.{u}) := ⟨fun y => hne ⟨(g ⁻¹ᵁ U).ι.base y⟩⟩
        exact TrivCoverPen.nonempty_iso_of_isEmpty _ _
  choose U hUaff hxU hτ using key

  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (U x : Set X))
    (fun x => (U x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  letI : LinearOrder (↥t) := LinearOrder.lift' (Fintype.equivFin (↥t)) (Fintype.equivFin (↥t)).injective
  refine ⟨{ ι := ↥t
            U := fun w => U w.1
            isAffineOpen := fun w => hUaff w.1
            iSup_eq_top := ?_ }, ⟨fun w => (hτ w.1).some⟩⟩
  refine top_le_iff.mp fun y _ => ?_
  obtain ⟨w, hw, hyw⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨w, hw⟩, hyw⟩

end S_AlgebraicGeometry_Scheme_Modules_exists_orderedAffineCover_nonempty_cechTrivialisation_comap_of_isInvertible
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_orderedAffineCover_nonempty_cechTrivialisation_comap_of_isInvertible (solution)
