-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_Defs
-- name    : LPCA_Solutions_LPCA_CechVariableNaturality_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:25:48.837391+00:00
-- url     : https://prove2.me/theorems/7156d6af-723b-48a1-baba-8711fdcc43f1
-- title:
--   Restoring omitted zero source slots in Čech differential matrices
-- statement:
--   This bundle supplies restoring omitted zero source slots in Čech differential matrices. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - Zero source pieces can be restored to the differential's index set.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_CechVariableNaturality.lean, selected declarations in lines 13–36; source SHA-256 51ddc5d922fdf0465129a0f9a395a6f170505490ed479411727ffd8cd12657a1; source certificate Sapelo2 job 49172236.

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
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false

namespace LPCA

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

/-- Zero source pieces can be restored to the differential's index set. -/
theorem actualDifferential_apply_full
    (coefficient : Finset V → Finset V → k)
    (K : Complex V) (T : Finset V) (a : V → ℤ) (p : ℕ)
    (y : LocalizedCechTerm k K T a p) (G : CechSlot T (p + 1)) :
    actualDifferential k coefficient K T a p y G =
      ∑ F : CechSlot T p, if hFG : F.1 ⊆ G.1 then
        coefficient F.1 G.1 • localizedPieceMap k K F.1 G.1 hFG a (y F) else 0 := by
  classical
  let e : CechBasis K T a p → CechSlot T p :=
    fun F => ⟨F.1, F.2.1, F.2.2.1⟩
  apply Fintype.sum_of_injective e
    (fun F H heq => Subtype.ext (congrArg (fun x : CechSlot T p => x.1) heq))
  · intro F hF
    have hc : ¬ LocalizationCriterion K F.1 a := by
      intro hc
      exact hF ⟨⟨F.1, F.2.1, F.2.2, hc⟩, rfl⟩
    have hy : y F = 0 := by
      apply Subtype.ext
      exact (Submodule.mem_bot k).mp
        (((localizedPiece_eq_bot_iff k K F.1 a).mpr hc).le (y F).2)
    split_ifs <;> simp [hy]
  · intro F
    rfl









end LPCA


