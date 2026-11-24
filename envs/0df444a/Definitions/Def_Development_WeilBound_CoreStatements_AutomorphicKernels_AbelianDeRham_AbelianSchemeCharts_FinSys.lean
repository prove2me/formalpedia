-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianSchemeCharts_FinSys
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianSchemeCharts_FinSys
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T22:13:39.516335+00:00
-- url     : https://prove2.me/theorems/48f881b6-28c8-43e6-8546-9043c64d347b
-- title:
--   Fin Sys
-- statement:
--   Definitions and structural lemmas for Fin Sys, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/AbelianDeRham/AbelianSchemeCharts/FinSys.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
attribute [local instance] Over.cartesianMonoidalCategory
namespace MainStatements.Hodge.Sh
def NEFin (J : Type) : Type := {t : Finset J // t.Nonempty}
open Classical in

instance (J : Type) : SemilatticeInf (NEFin J) where
  le a b := b.1 ⊆ a.1
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ hab hbc := Finset.Subset.trans hbc hab
  le_antisymm a b hab hba := Subtype.ext (Finset.Subset.antisymm hba hab)
  inf a b := ⟨a.1 ∪ b.1, a.2.mono Finset.subset_union_left⟩
  inf_le_left _ _ := Finset.subset_union_left
  inf_le_right _ _ := Finset.subset_union_right
  le_inf _ _ _ hab hac := Finset.union_subset hab hac
instance (J : Type) [Finite J] : Finite (NEFin J) :=
  inferInstanceAs (Finite {t : Finset J // t.Nonempty})
theorem isAffineOpen_inf_of_isSeparated {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
    (hs : IsSeparated s) {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) := by
  have := hs
  exact (isAffineHom_diagonal_iff (f := s)).mp inferInstance ⊤ (isAffineOpen_top _) U (by simp) V (by simp) hU hV
def sysOfCover {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hs : IsSeparated s) {J : Type}
    (U : J → X.affineOpens) (hU : ⨆ i, (U i).1 = ⊤) : Sys X (NEFin J) where
  u a := ⟨a.1.inf' a.2 fun i ↦ (U i).1,
    Finset.inf'_induction a.2 _ (fun _ h₁ _ h₂ ↦ isAffineOpen_inf_of_isSeparated s hs h₁ h₂) fun i _ ↦ (U i).2⟩
  map_inf a b := by
    classical
    exact Finset.inf'_union a.2 b.2 _
  cover := by
    refine eq_top_iff.2 fun x _ ↦ ?_
    have hx : x ∈ ⨆ i, (U i).1 := hU ▸ trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨{i}, Finset.singleton_nonempty i⟩, ?_⟩
    simpa using hi
end MainStatements.Hodge.Sh


