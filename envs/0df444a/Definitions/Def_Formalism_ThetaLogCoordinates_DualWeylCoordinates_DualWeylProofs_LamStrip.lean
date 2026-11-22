-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LamStrip
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LamStrip
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:41:10.388827+00:00
-- url     : https://prove2.me/theorems/73fe6202-01cb-4c21-8e8e-0f45cec4e179
-- title:
--   Lam Strip
-- statement:
--   Definitions and structural lemmas for Lam Strip, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LamStrip.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SumIndicesEqSumColumns
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
def ql_be (b : ℕ) (L : LamIdx n b) : Fin n → ℤ := ∑ x ∈ L.1, Pi.single x (1 : ℤ)
variable [NeZero n]
def ql_ps (b : ℕ) (mu nu : Fin n → ℤ) : Matrix (TIdx mu × LamIdx n b) (TIdx nu) ℤ :=
  fun y I => ql_P ℤ (ql_E (mu (lastIdx n)) (nu 0 - mu (lastIdx n)).toNat (qs_ext mu y.1)) y.2.1
    (ql_E (mu (lastIdx n)) (nu 0 - mu (lastIdx n)).toNat (qs_ext nu I))
end Formalism.InvariantFactorPaths.ColumnFamilies


