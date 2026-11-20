-- Prove2me | Definitions.Def_DeletionCode_GeneratingEnumeration
-- name    : DeletionCode_GeneratingEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:24:32.55552+00:00
-- url     : https://prove2.me/theorems/19ee44f4-1a3c-409f-8bcf-18ba1f503965
-- title:
--   Generating Enumeration
-- statement:
--   Definitions and structural lemmas for Generating Enumeration, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingEnumeration.lean

import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_ManuscriptCounting
import Definitions.Def_DeletionCode_CatalogueFamily
import Mathlib.Data.Finset.Sort
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_CanonicalIndex_flat_rule_spectrum
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
attribute [local simp] DeletionCode.BlockPartition.mem_attachedBlocks
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks
attribute [local simp] DeletionCode.ComponentFibers.mem_fiber
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk


set_option autoImplicit true
namespace DeletionCode.GeneratingEnumeration
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport SignedRuleCount RuleReconstruction RuleSetGraph SupportComponents
open CanonicalIndex ConnectedBlocks FiniteGenerating
open scoped BigOperators
structure CataloguePresentation (t k R : ℕ) (rules : Fin R → Gram (windowLength k) → ℤ) where
  words : Fin R → Fin (2 * t) → BubbleWord k
  valid : ValidCatalogue (flatten t R words) (group t R)
  balanced : OrientationBalanced t (flatten t R words) (group t R)
  rule_eq : ∀ r : Fin R,
    ruleSpectrum (flatFamily t R words).family (windowLength k)
      (groupBubbles (group t R) r) = rules r
def singleFamily {t k : ℕ} (words : Fin (2 * t) → BubbleWord k) :
    EditedFamily (Fin (2 * t)) k :=
  indexedFamily words (fun _ => (0 : Fin 1))
theorem flat_extra_eq {t k R : ℕ}
    (words : Fin R → Fin (2 * t) → BubbleWord k) (b : Fin (2 * t * R)) (side : Bool) :
    (flatFamily t R words).family.extra b side =
      (singleFamily (words (group t R b))).family.extra (indexEquiv t R b).2 side := rfl
theorem flat_vertex_eq {t k R : ℕ}
    (words : Fin R → Fin (2 * t) → BubbleWord k) (b : Fin (2 * t * R))
    (side : Bool) (i : ℕ) :
    vertex (flatFamily t R words).family (windowLength k) b side i =
      vertex (singleFamily (words (group t R b))).family
        (windowLength k) (indexEquiv t R b).2 side i := rfl
theorem orientation_count {t k R : ℕ}
    (words : Fin R → Fin (2 * t) → BubbleWord k) (r : Fin R) (o : Orientation) :
    (Finset.univ.filter (fun b : Fin (2 * t * R) =>
      group t R b = r ∧ (flatten t R words b).orientation = o)).card =
    (Finset.univ.filter (fun j : Fin (2 * t) => (words r j).orientation = o)).card := by
  classical
  apply Finset.card_bij (fun b _ => (indexEquiv t R b).2)
  · intro b hb
    obtain ⟨hgroup, ho⟩ := (Finset.mem_filter.mp hb).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change (words (group t R b) (indexEquiv t R b).2).orientation = o at ho
    simpa only [hgroup] using ho
  · intro a ha b hb hab
    apply (indexEquiv t R).injective
    exact Prod.ext
      (((Finset.mem_filter.mp ha).2.1).trans ((Finset.mem_filter.mp hb).2.1).symm) hab
  · intro j hj
    refine ⟨(indexEquiv t R).symm (r, j), ?_, by simp⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, by simp [group], ?_⟩
    simpa only [flatten_at_pair] using (Finset.mem_filter.mp hj).2
noncomputable def presentationOfCatalogue {t k R : ℕ}
    (rules : Fin R → Gram (windowLength k) → ℤ)
    (hcat : ∀ r, CatalogueRule t k (rules r)) : CataloguePresentation t k R rules := by
  classical
  let words : Fin R → Fin (2 * t) → BubbleWord k := fun r => Classical.choose (hcat r)
  have hvalid (r : Fin R) : ValidCatalogue (words r) (fun _ => (0 : Fin 1)) :=
    (Classical.choose_spec (hcat r)).1
  have hbalanced (r : Fin R) : OrientationBalanced t (words r) (fun _ => (0 : Fin 1)) :=
    (Classical.choose_spec (hcat r)).2.1
  have hvalue (r : Fin R) :
      ruleSpectrum (singleFamily (words r)).family (windowLength k) Finset.univ = rules r :=
    (Classical.choose_spec (hcat r)).2.2
  refine ⟨words, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro b
      exact (hvalid (group t R b)).boundary (indexEquiv t R b).2
    · intro b side
      exact (hvalid (group t R b)).simple (indexEquiv t R b).2 side
    · intro b i j hi hj heq
      exact (hvalid (group t R b)).endpoints (indexEquiv t R b).2 i j hi hj heq
    · intro r a ha b hb hab sa sb j l hj hl
      have hra := (Finset.mem_filter.mp ha).2
      have hrb := (Finset.mem_filter.mp hb).2
      have hgroup : group t R b = group t R a := hrb.trans hra.symm
      have hlocal_ne : (indexEquiv t R a).2 ≠ (indexEquiv t R b).2 := by
        intro heq
        apply hab
        apply (indexEquiv t R).injective
        exact Prod.ext hgroup.symm heq
      have hj' : j ≤ (singleFamily (words (group t R a))).family.extra
          (indexEquiv t R a).2 sa + 1 := hj
      have hl' : l ≤ (singleFamily (words (group t R a))).family.extra
          (indexEquiv t R b).2 sb + 1 := by
        change l ≤ (flatFamily t R words).family.extra b sb + 1 at hl
        simpa only [flat_extra_eq, hgroup] using hl
      have hd := (hvalid (group t R a)).within_rule_disjoint (0 : Fin 1)
        (indexEquiv t R a).2 (by simp) (indexEquiv t R b).2 (by simp)
        hlocal_ne sa sb j l hj' hl'
      change vertex (flatFamily t R words).family (windowLength k) a sa j ≠
        vertex (flatFamily t R words).family (windowLength k) b sb l
      simpa only [flat_vertex_eq, hgroup, singleFamily] using hd
  · intro r
    constructor
    · rw [orientation_count]
      simpa using (hbalanced r (0 : Fin 1)).1
    · rw [orientation_count]
      simpa using (hbalanced r (0 : Fin 1)).2
  · intro r
    calc
      ruleSpectrum (flatFamily t R words).family (windowLength k)
          (groupBubbles (group t R) r) =
          fun g => ∑ j : Fin (2 * t),
            bubbleSpectrum (pairFamily t R words).family (windowLength k) (r, j) g :=
        flat_rule_spectrum t R words r
      _ = ruleSpectrum (singleFamily (words r)).family (windowLength k) Finset.univ := by
        funext g
        apply Finset.sum_congr rfl
        intro j hj
        rfl
      _ = rules r := hvalue r
end DeletionCode.GeneratingEnumeration


