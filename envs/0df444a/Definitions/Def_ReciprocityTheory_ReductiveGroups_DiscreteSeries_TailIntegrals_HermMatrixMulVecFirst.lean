-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermMatrixMulVecFirst
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermMatrixMulVecFirst
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T14:54:14.737044+00:00
-- url     : https://prove2.me/theorems/8b909a32-1d6e-432d-ba76-714f20c7092c
-- title:
--   Herm Matrix Mul Vec First
-- statement:
--   Definitions and structural lemmas for Herm Matrix Mul Vec First, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermMatrixMulVecFirst.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
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
def sg (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ i.val ∧ i.val ≤ r + k then i else ⟨2 * r + k - i.val, by omega⟩
abbrev cc : ℂ := ((Real.sqrt 2)⁻¹ : ℂ)
def aF (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (t : Fin (r + 1)) : ℂ :=
  if h : t.val < r then y (eI k r ⟨t.val, h⟩) else cc * (y (wI k r 0) - y (wI k r (Fin.last k)))
def aF' (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (t : Fin (r + 1)) : ℂ :=
  if h : t.val < r then y (esI k r ⟨t.val, h⟩) else cc * (y (wI k r 0) + y (wI k r (Fin.last k)))
end FormulaFAux
end ReciprocityTheory.ChartRestriction.DS.Xi


