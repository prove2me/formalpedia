-- Prove2me | Definitions.Def_MantriCVQ_PH
-- name    : MantriCVQ_PH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:49.873299+00:00
-- url     : https://prove2.me/theorems/cb0dfe66-e06e-4f49-a990-6545b9551f51
-- title:
--   The polynomial hierarchy $\mathsf{PH}^O$
-- statement:
--   $\mathsf{PH}^O=\bigcup_{k\ge0}\bigl(\Sigma_k^{p,O}\cup\Pi_k^{p,O}\bigr)$, the union of all the classes of the hierarchy relative to $O$, including $k=0$.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3.1, p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_MantriCVQ_SigmaPi

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace MantriCVQ

/-- The polynomial hierarchy relative to `O` (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33),
§3.1, p. 14 (PDF p. 16): "PH^O is the union of all these classes"), for all `k ≥ 0`. -/
def PH (O : Oracle) : Set (Set Str) :=
  ⋃ k : ℕ, SigmaPi O true k ∪ SigmaPi O false k

end MantriCVQ


