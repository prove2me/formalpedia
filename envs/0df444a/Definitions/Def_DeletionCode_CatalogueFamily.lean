-- Prove2me | Definitions.Def_DeletionCode_CatalogueFamily
-- name    : DeletionCode_CatalogueFamily
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:21:35.156503+00:00
-- url     : https://prove2.me/theorems/9ef7d4b1-3c86-458b-9fba-86bd1375075c
-- title:
--   Catalogue Family
-- statement:
--   Definitions and structural lemmas for Catalogue Family, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueFamily.lean

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_CanonicalIndex
import Theorems.Thm_DeletionCode_CanonicalIndex_flat_rule_spectrum
import Theorems.Thm_DeletionCode_CatalogueBridge_ValidCatalogue_geometry
import Theorems.Thm_DeletionCode_CatalogueBridge_differentLengths
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm

set_option autoImplicit true
namespace DeletionCode.CatalogueFamily
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport SignedRuleCount RuleReconstruction RuleSetGraph SupportComponents
open CanonicalIndex ConnectedBlocks
open scoped BigOperators
structure PresentedFamily (t k R : ℕ) (G : Fin R → Gram (windowLength k) → ℤ) where
  E : EditedFamily (Fin (2 * t * R)) k
  rank : ∀ b, E.rank b = (CanonicalIndex.group t R b).val
  geometry : BubbleGeometry E.family (windowLength k)
  disjoint : ∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i)
  rule_eq : ∀ r : Fin R,
    ruleSpectrum E.family (windowLength k) (groupBubbles (CanonicalIndex.group t R) r) = G r
def singleFamily {t k : ℕ} (words : Fin (2 * t) → BubbleWord k) :
    EditedFamily (Fin (2 * t)) k :=
  indexedFamily words (fun _ => (0 : Fin 1))
theorem flat_extra_eq {t k R : ℕ}
    (words : Fin R → Fin (2 * t) → BubbleWord k) (b : Fin (2 * t * R)) (side : Bool) :
    (flatFamily t R words).family.extra b side =
      (singleFamily (words (CanonicalIndex.group t R b))).family.extra
        (indexEquiv t R b).2 side := rfl
theorem flat_vertex_eq {t k R : ℕ}
    (words : Fin R → Fin (2 * t) → BubbleWord k) (b : Fin (2 * t * R))
    (side : Bool) (i : ℕ) :
    vertex (flatFamily t R words).family (windowLength k) b side i =
      vertex (singleFamily (words (CanonicalIndex.group t R b))).family
        (windowLength k) (indexEquiv t R b).2 side i := rfl
noncomputable def ofCatalogue {t k R : ℕ} (G : Fin R → Gram (windowLength k) → ℤ)
    (hcat : ∀ r, CatalogueRule t k (G r)) : PresentedFamily t k R G := by
  classical
  let words : Fin R → Fin (2 * t) → BubbleWord k := fun r => Classical.choose (hcat r)
  have hvalid (r : Fin R) : ValidCatalogue (words r) (fun _ => (0 : Fin 1)) :=
    (Classical.choose_spec (hcat r)).1
  have hvalue (r : Fin R) :
      ruleSpectrum (singleFamily (words r)).family (windowLength k) Finset.univ = G r :=
    (Classical.choose_spec (hcat r)).2.2
  refine ⟨flatFamily t R words, fun _ => rfl, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, CatalogueBridge.differentLengths (flatFamily t R words)⟩
    · intro b side
      exact (hvalid (CanonicalIndex.group t R b)).simple (indexEquiv t R b).2 side
    · intro b i j hi hj heq
      exact (hvalid (CanonicalIndex.group t R b)).endpoints (indexEquiv t R b).2 i j hi hj heq
  · intro i a ha b hb hab sa sb j l hj hl
    have hra := (Finset.mem_filter.mp ha).2
    have hrb := (Finset.mem_filter.mp hb).2
    change (CanonicalIndex.group t R a).val = i at hra
    change (CanonicalIndex.group t R b).val = i at hrb
    have hgroup : CanonicalIndex.group t R b = CanonicalIndex.group t R a :=
      Fin.ext (hrb.trans hra.symm)
    have hlocal_ne : (indexEquiv t R a).2 ≠ (indexEquiv t R b).2 := by
      intro heq
      apply hab
      apply (indexEquiv t R).injective
      exact Prod.ext hgroup.symm heq
    have hj' : j ≤ (singleFamily (words (CanonicalIndex.group t R a))).family.extra
        (indexEquiv t R a).2 sa + 1 := hj
    have hl' : l ≤ (singleFamily (words (CanonicalIndex.group t R a))).family.extra
        (indexEquiv t R b).2 sb + 1 := by
      simpa only [flat_extra_eq, hgroup] using hl
    have hdis := (hvalid (CanonicalIndex.group t R a)).within_rule_disjoint (0 : Fin 1)
      (indexEquiv t R a).2 (by simp) (indexEquiv t R b).2 (by simp)
      hlocal_ne sa sb j l hj' hl'
    simpa only [flat_vertex_eq, hgroup, singleFamily] using hdis
  · intro r
    calc
      ruleSpectrum (flatFamily t R words).family (windowLength k)
          (groupBubbles (CanonicalIndex.group t R) r) =
          fun g => ∑ j : Fin (2 * t),
            bubbleSpectrum (pairFamily t R words).family (windowLength k) (r, j) g :=
        flat_rule_spectrum t R words r
      _ = ruleSpectrum (singleFamily (words r)).family (windowLength k) Finset.univ := by
        funext g
        apply Finset.sum_congr rfl
        intro j hj
        rfl
      _ = G r := hvalue r
namespace PresentedFamily
variable {t k R : ℕ} {G : Fin R → Gram (windowLength k) → ℤ}
theorem rule_set (P : PresentedFamily t k R G) :
    rulesOfFamily P.E (CanonicalIndex.group t R) = Finset.univ.image G := by
  classical
  unfold rulesOfFamily
  apply Finset.image_congr
  intro r hr
  exact P.rule_eq r
noncomputable def componentEquiv (P : PresentedFamily t k R G) :
    RuleSetComponents (Finset.univ.image G) ≃ GraphComponents P.E.family (windowLength k) := by
  rw [← P.rule_set]
  exact ruleSetComponentEquiv P.E (CanonicalIndex.group t R) P.rank P.geometry P.disjoint
theorem incident_of_hasVertex (P : PresentedFamily t k R G)
    (b : Fin (2 * t * R)) (v : Vertex (windowLength k))
    (hv : HasVertex P.E.family (windowLength k) b v) : Incident (Finset.univ.image G) v := by
  rw [← P.rule_set]
  exact (incident_iff_supported P.E (CanonicalIndex.group t R) P.rank P.geometry P.disjoint v).mpr
    ⟨b, hv⟩
noncomputable def bubbleComponent (P : PresentedFamily t k R G)
    (b : Fin (2 * t * R)) : RuleSetComponents (Finset.univ.image G) :=
  Quotient.mk (ruleSetSetoid (Finset.univ.image G))
    ⟨representative P.E.family (windowLength k) b,
      P.incident_of_hasVertex b _ ⟨false, 0, by omega, rfl⟩⟩
end PresentedFamily
end DeletionCode.CatalogueFamily


