-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridPointQuery
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridPointQuery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:53:58.434762+00:00
-- url     : https://prove2.me/theorems/d689e35b-e380-419f-97c4-e9445df1740e
-- title:
--   Grid Point Query
-- statement:
--   Definitions and structural lemmas for Grid Point Query, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridPointQuery.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
import Mathlib.Tactic
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
noncomputable def natRealQuery : ℕ → ℝ × ℕ
  | 0 => (0,1)
  | n+1 => let q := natRealQuery n
           (q.1+1,q.2+1)
noncomputable def intRealQuery : ℤ → ℝ × ℕ
  | .ofNat n => natRealQuery n
  | .negSucc n => let q := natRealQuery (n+1)
                  (-q.1,q.2+1)
noncomputable def gridPointQuery (K : ℕ) (g : Grid K) : Space × ℕ :=
  let q0 := intRealQuery (g 0).val
  let q1 := intRealQuery (g 1).val
  let q2 := intRealQuery (g 2).val
  (WithLp.toLp 2 ![q0.1,q1.1,q2.1],q0.2+q1.2+q2.2+3)
end QEC.Coding.BDL26RandomPerturbation


