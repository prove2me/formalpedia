-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CechTerms_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_CechTerms_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:04:31.272994+00:00
-- url     : https://prove2.me/theorems/d9971c14-93af-45ef-ae6e-5d1f35037b69
-- title:
--   Čech Terms — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for čech terms used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_CechTerms.lean, selected declarations in lines 108–120; source SHA-256 daa9522baa69513cf73223b5143e2e03c7b214f3f77e05fb74b3e507916b9fa5; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false

namespace LPCA

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]





















theorem negativeDegreeActualTerm_subsingleton
    (K : Complex V) (i : V) (T : Finset V) (a : V → ℤ) (p : ℕ)
    (hT : i ∉ T) (ha : a i < 0) :
    Subsingleton (LocalizedCechTerm k K T a p) := by
  haveI : ∀ F : CechSlot T p, Subsingleton (localizedPiece k K F.1 a) := by
    intro F
    have hc : ¬ LocalizationCriterion K F.1 a := by
      intro hc
      exact (not_le_of_gt ha) (hc.1 i (fun hiF => hT (F.2.1 hiF)))
    have hzero := (localizedPiece_eq_bot_iff k K F.1 a).mpr hc
    rw [hzero]
    infer_instance
  infer_instance

end LPCA


