-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_DirectSumGeneratorEquations_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_DirectSumGeneratorEquations_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:04:59.865991+00:00
-- url     : https://prove2.me/theorems/ff3f5def-8fe5-4b44-892b-b681e8ee7f0a
-- title:
--   Direct Sum Generator Equations — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for direct sum generator equations used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_DirectSumGeneratorEquations.lean, selected declarations in lines 13–46; source SHA-256 6c0da9eccc0168e7fd2db191aefc0689378cbb6649b28bed8b51e68892aa5b39; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.DirectSum.Module
import Definitions.Def_LPCA_Solutions_LPCA_DirectSumRestriction_SixOne20261024_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

universe u v w

variable (R : Type u) [Ring R]

@[simp] theorem directSumRestrictionEquiv_lof
    {I : Type u} [DecidableEq I] (A : I → Type u)
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    (p : I → Prop) [DecidablePred p] (hzero : ∀ i, ¬ p i → Subsingleton (A i))
    (i : I) (hi : p i) (x : A i) :
    directSumRestrictionEquiv R A p hzero (DirectSum.lof R I A i x) =
      DirectSum.lof R {i // p i} (fun j => A j.1) ⟨i, hi⟩ x := by
  apply DFinsupp.ext
  rintro ⟨j, hj⟩
  change (DFinsupp.single (β := A) i x) j =
    (DFinsupp.single (β := fun t : {i // p i} => A t.1) ⟨i, hi⟩ x) ⟨j, hj⟩
  by_cases hij : i = j
  · subst j
    simp
  · simp [DFinsupp.single_apply, hij, Subtype.ext_iff]

@[simp] theorem directSumCongrEquiv_lof
    {I : Type v} [DecidableEq I] {A B : I → Type u}
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module R (B i)]
    (e : ∀ i, A i ≃ₗ[R] B i) (i : I) (x : A i) :
    DirectSum.congrLinearEquiv e (DirectSum.lof R I A i x) =
      DirectSum.lof R I B i (e i x) :=
  DirectSum.lmap_lof (fun i => (e i).toLinearMap) i x

@[simp] theorem directSumSigmaCurryEquiv_lof
    {I : Type v} [DecidableEq I] {B : I → Type w} [∀ i, DecidableEq (B i)]
    (A : ∀ i, B i → Type u) [∀ i j, AddCommGroup (A i j)] [∀ i j, Module R (A i j)]
    (i : I) (j : B i) (x : A i j) :
    DirectSum.sigmaLcurryEquiv R
        (DirectSum.lof R (Σ i, B i) (fun p => A p.1 p.2) ⟨i, j⟩ x) =
      DirectSum.lof R I (fun i => DirectSum (B i) (A i)) i
        (DirectSum.lof R (B i) (A i) j x) :=
  DFinsupp.sigmaCurry_single ⟨i, j⟩ x





end LPCA


