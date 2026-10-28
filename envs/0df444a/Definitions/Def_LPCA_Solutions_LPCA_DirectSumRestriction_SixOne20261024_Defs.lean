-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_DirectSumRestriction_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_DirectSumRestriction_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:04:27.055514+00:00
-- url     : https://prove2.me/theorems/ac182a09-a2ae-4812-a43d-cdd418f1848e
-- title:
--   Direct Sum Restriction — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for direct sum restriction used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
--
--   Restricting a direct sum to a set of indices is an equivalence whenever
--   all omitted summands are zero. Its forward map is actual coordinate restriction.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_DirectSumRestriction.lean, selected declarations in lines 15–52; source SHA-256 fccddb79eced2654fb9c920d38d138db1af378ff09b15d49db56163a297953ac; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.DirectSum.Module

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

universe u

variable (R : Type u) [Ring R]
variable {I : Type u} [DecidableEq I]
variable (A : I → Type u) [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]

/-- Restricting a direct sum to a set of indices is an equivalence whenever
all omitted summands are zero. Its forward map is actual coordinate restriction. -/
noncomputable def directSumRestrictionEquiv (p : I → Prop) [DecidablePred p]
    (hzero : ∀ i, ¬ p i → Subsingleton (A i)) :
    DirectSum I A ≃ₗ[R] DirectSum {i // p i} (fun i => A i.1) := by
  let r := DFinsupp.subtypeDomainLinearMap (γ := R) (β := A) p
  let inc : DirectSum {i // p i} (fun i => A i.1) →ₗ[R] DirectSum I A :=
    DirectSum.toModule R {i // p i} (DirectSum I A)
      (fun i => DirectSum.lof R I A i.1)
  apply LinearEquiv.ofBijective r
  constructor
  · intro x y h
    apply DFinsupp.ext
    intro i
    by_cases hi : p i
    · exact congrArg (fun z => z ⟨i, hi⟩) h
    · exact (hzero i hi).elim _ _
  · have hr : r.comp inc = LinearMap.id := by
      apply DirectSum.linearMap_ext
      intro i
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      change r (inc (DirectSum.lof R {i // p i} (fun i => A i.1) i x)) = _
      dsimp only [inc]
      rw [DirectSum.toModule_lof]
      apply DFinsupp.ext
      intro j
      change (DFinsupp.single (β := A) i.1 x) j.1 =
        (DFinsupp.single (β := fun t : {i // p i} => A t.1) i x) j
      by_cases hij : i = j
      · subst j
        simp
      · have hv : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
        simp [DFinsupp.single_apply, hij, hv]
    intro y
    refine ⟨inc y, ?_⟩
    exact congrArg (fun f => f y) hr



end LPCA


