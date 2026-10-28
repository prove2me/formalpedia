-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_FiniteIntervalSummand_IntervalExistence20261025_Defs
-- name    : LPCA_Solutions_LPCA_FiniteIntervalSummand_IntervalExistence20261025_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-26T02:46:17.713143+00:00
-- url     : https://prove2.me/theorems/17fb4312-8f0d-4b04-9c3b-48c1778b5b48
-- title:
--   Finite Interval Summand — finite interval-decomposition dependencies
-- statement:
--   Selected constructions and proved compatibility results for finite interval summand, used in finite interval-decomposition existence for original homogeneous Ext persistence. The formal declarations retain their exact objects, hypotheses and structure maps.
--
--   Every nonzero diagram over a finite linear order has an actual nonempty
--   scalar interval as a retract. No pointwise finite-dimensionality is needed
--   for this first splitting step.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Theorem3.10, interval-decomposition existence part, with formalization dependencies. Certified Lean source: Solutions/LPCA_FiniteIntervalSummand.lean, selected declarations in lines 15–54; source SHA-256 a1a360929e26e2beeefb884927b4b7f8a3f5dc8f7970d65074fa658307d84206; exact-source certificate Sapelo2 job 49312860.

import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFunctor_Defs
import Definitions.Def_LPCA_Solutions_LPCA_IntervalPersistence_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_OrderedIntervalSplitting_IntervalExistence20261025_Defs

set_option autoImplicit false

namespace LPCA

open CategoryTheory

universe u v

variable {k : Type u} [Field k]
variable {ι : Type v} [LinearOrder ι] [Fintype ι]

/-- Every nonzero diagram over a finite linear order has an actual nonempty
scalar interval as a retract. No pointwise finite-dimensionality is needed
for this first splitting step. -/
theorem finiteOrderedDiagram_has_interval_retract (F : ι ⥤ ModuleCat.{u} k)
    (hnonzero : ∃ t, Nontrivial (F.obj t)) :
    ∃ i j : ι, i ≤ j ∧
      ∃ (inc : orderedInterval k i j ⟶ F) (ret : F ⟶ orderedInterval k i j),
        inc ≫ ret = 𝟙 (orderedInterval k i j) := by
  classical
  let S : Finset ι := Finset.univ.filter (fun t => Nontrivial (F.obj t))
  have hS : S.Nonempty := by
    obtain ⟨t, ht⟩ := hnonzero
    exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩⟩
  let i := S.min' hS
  have hi : Nontrivial (F.obj i) := (Finset.mem_filter.mp (S.min'_mem hS)).2
  have hbefore : ∀ t, t < i → Subsingleton (F.obj t) := by
    intro t hti
    apply not_nontrivial_iff_subsingleton.mp
    intro ht
    have htS : t ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩
    exact (not_le_of_gt hti) (S.min'_le t htS)
  haveI := hi
  obtain ⟨v, hv⟩ := exists_ne (0 : F.obj i)
  let J : Finset ι := Finset.univ.filter
    (fun t => ∃ h : i ≤ t, (F.map (homOfLE h)) v ≠ 0)
  have hiJ : i ∈ J := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_refl i, ?_⟩
    simpa using hv
  have hJ : J.Nonempty := ⟨i, hiJ⟩
  let j := J.max' hJ
  obtain ⟨hij, hvj⟩ := (Finset.mem_filter.mp (J.max'_mem hJ)).2
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hvj
  have hafter : ∀ t, j < t → ∀ h : i ≤ t, (F.map (homOfLE h)) v = 0 := by
    intro t hjt hit
    by_contra hne
    have htJ : t ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hit, hne⟩
    exact (not_le_of_gt hjt) (J.le_max' t htJ)
  exact ⟨i, j, hij, orderedIntervalInclusion F i j v hafter,
    orderedIntervalRetraction F i j φ hbefore,
    orderedInterval_inclusion_retraction F i j hij v φ hφ hafter hbefore⟩

end LPCA


