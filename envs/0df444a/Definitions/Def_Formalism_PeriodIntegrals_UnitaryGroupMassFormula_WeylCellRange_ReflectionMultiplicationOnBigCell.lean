-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylCellRange_ReflectionMultiplicationOnBigCell
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylCellRange_ReflectionMultiplicationOnBigCell
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T14:27:13.979075+00:00
-- url     : https://prove2.me/theorems/daf20fe7-b23e-4898-9ab8-8e4aea56c207
-- title:
--   Reflection Multiplication On Big Cell
-- statement:
--   Definitions and structural lemmas for Reflection Multiplication On Big Cell, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylCellRange/ReflectionMultiplicationOnBigCell.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
namespace PI.QnWCellW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable def cN (r : ℕ) (c : Fin r → ℂ) (j : ℕ) : ℂ := if h : j < r then c ⟨j, h⟩ else 0
def swp (k r : ℕ) (p : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ p.val ∧ p.val ≤ r + k then p else ⟨2 * r + k - p.val, by omega⟩
noncomputable def cf (k r : ℕ) (c : Fin r → ℂ) (p : Fin (2 * r + k + 1)) : ℂ :=
  if p.val < r then (star (cN r c p.val))⁻¹
  else if p.val ≤ r + k then 1 else cN r c (2 * r + k - p.val)
noncomputable def Wm (k r : ℕ) (S : Finset ℕ) (c : Fin r → ℂ) : Mx k r := fun p q =>
  if q.val < r then
    (if q.val ∈ S then (if p.val = 2 * r + k - q.val then cN r c q.val else 0)
     else if p.val = q.val then 1 else 0)
  else if q.val ≤ r + k then (if p.val = q.val then 1 else 0)
  else if 2 * r + k - q.val ∈ S then
    (if p.val = 2 * r + k - q.val then (star (cN r c (2 * r + k - q.val)))⁻¹ else 0)
  else if p.val = q.val then 1 else 0
def μE {k : ℕ} (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : ℕ) : ℂ :=
  if h : i < k + 1 ∧ j < k + 1 then μ ⟨i, h.1⟩ ⟨j, h.2⟩ else 0
end PI.QnWCellW


