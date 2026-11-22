-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SumIndicesEqSumColumns
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SumIndicesEqSumColumns
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:37:31.162906+00:00
-- url     : https://prove2.me/theorems/1467970d-4f71-4c16-90a1-2d251a14a3dc
-- title:
--   Sum Indices Eq Sum Columns
-- statement:
--   Definitions and structural lemmas for Sum Indices Eq Sum Columns, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SumIndicesEqSumColumns.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LWedge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
def ql_E (lo : ℤ) (N : ℕ) (F : ℤ → Finset (Fin n)) : Fin N → Finset (Fin n) := fun j => F (lo + 1 + (j : ℕ))
def ql_fill (lo : ℤ) (N : ℕ) (f : Fin N → Finset (Fin n)) : ℤ → Finset (Fin n) :=
  fun c => if h : lo < c ∧ c ≤ lo + N then f ⟨(c - lo - 1).toNat, by omega⟩ else if c ≤ lo then univ else ∅
variable [NeZero n]
end Formalism.InvariantFactorPaths.ColumnFamilies


