-- Prove2me | Definitions.Def_MantriCVQ_DT
-- name    : MantriCVQ_DT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:08.948202+00:00
-- url     : https://prove2.me/theorems/c7e921a4-2eec-4985-b2fd-ce71dadddfb7
-- title:
--   Decision trees
-- statement:
--   A **decision tree** over $K$ variables queries one variable at each internal node and outputs a bit at each leaf. Its **depth** is the maximum number of queries on a root-to-leaf path.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3, p. 13 (PDF p. 15)

import Mathlib

namespace MantriCVQ

/-- A decision tree over `K` variables (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3,
p. 13 (PDF p. 15): "queries one variable at each internal node and outputs a bit at each leaf"). -/
inductive DT (K : ℕ) where
  | leaf (b : Bool)
  | query (i : Fin K) (t0 t1 : DT K)

/-- The depth: the maximum number of queries on a root-to-leaf path. -/
def DT.depth {K : ℕ} : DT K → ℕ
  | .leaf _ => 0
  | .query _ t0 t1 => 1 + max t0.depth t1.depth

/-- The value of a decision tree at `z`. -/
def DT.eval {K : ℕ} (z : Fin K → Bool) : DT K → Bool
  | .leaf b => b
  | .query i t0 t1 => if z i then t1.eval z else t0.eval z

end MantriCVQ


