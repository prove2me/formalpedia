-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_CechVariableNaturality_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:06:04.951986+00:00
-- url     : https://prove2.me/theorems/bcae1bb4-cc6f-401e-a600-b2b060b3ae9b
-- title:
--   Čech Variable Naturality — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for čech variable naturality used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
--
--   Multiplication by x_j commutes with the actual localization-induced differential.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_CechVariableNaturality.lean, selected declarations in lines 38–59; source SHA-256 51ddc5d922fdf0465129a0f9a395a6f170505490ed479411727ffd8cd12657a1; exact-source certificate Sapelo2 job 49296539.

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
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VariableMultiplication_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false

namespace LPCA

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]



/-- Multiplication by x_j commutes with the actual localization-induced differential. -/
theorem actualVariable_differential_compatibility
    (coefficient : Finset V → Finset V → k)
    (K : Complex V) (T : Finset V) (a b : V → ℤ) (j : V) (p : ℕ)
    (hab : ∀ v, b v = a v + if v = j then 1 else 0)
    (y : LocalizedCechTerm k K T a p) :
    actualTermVariableMap k K T a b j (p + 1) hab
      (actualDifferential k coefficient K T a p y) =
    actualDifferential k coefficient K T b p
      (actualTermVariableMap k K T a b j p hab y) := by
  classical
  funext G
  change pieceVariableMap k K G.1 a b j hab
    (actualDifferential k coefficient K T a p y G) = _
  rw [actualDifferential_apply_full, actualDifferential_apply_full, map_sum]
  apply Finset.sum_congr rfl
  intro F _
  by_cases hFG : F.1 ⊆ G.1
  · simp only [dif_pos hFG, map_smul]
    exact congrArg (fun z => coefficient F.1 G.1 • z)
      (pieceVariableMap_localization k K F.1 G.1 hFG a b j hab (y F)).symm
  · simp only [dif_neg hFG, map_zero]







end LPCA


