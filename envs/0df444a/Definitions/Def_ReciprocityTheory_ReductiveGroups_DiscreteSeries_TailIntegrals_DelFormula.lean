-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DelFormula
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DelFormula
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T15:37:44.38685+00:00
-- url     : https://prove2.me/theorems/517882e2-bc8b-4681-8030-9d50b96d1a8f
-- title:
--   Del Formula
-- statement:
--   Definitions and structural lemmas for Del Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/DelFormula.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergDualBaseVectorFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace FormulaFAux
def AN (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) (j : ℕ) : ℂ := if h : j < r' + 1 then aF k r' y ⟨j, h⟩ else 0
def AN' (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) (j : ℕ) : ℂ := if h : j < r' + 1 then aF' k r' y ⟨j, h⟩ else 0
def Uu (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) : ℂ :=
  ∑ i : Fin (k - 1), star (y (ix k r' (Sum.inr (Sum.inr i)))) * y (ix k r' (Sum.inr (Sum.inr i)))
end FormulaFAux
end ReciprocityTheory.ChartRestriction.DS.Xi


