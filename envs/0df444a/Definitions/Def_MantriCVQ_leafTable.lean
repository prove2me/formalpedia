-- Prove2me | Definitions.Def_MantriCVQ_leafTable
-- name    : MantriCVQ_leafTable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:43.400198+00:00
-- url     : https://prove2.me/theorems/a316aa59-cee9-41f1-a9b4-dba868bd159d
-- title:
--   The leaf table stored in the oracle
-- statement:
--   At size $n$ the oracle stores the leaves of one instance at the addresses $1^n0w$, where $w$ ranges over the root-to-leaf paths. The leaf table of $O$ at size $n$ is $w\mapsto O(1^n0w)$.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §7.1, p. 37 (PDF p. 39)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Oracle

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace MantriCVQ

/-- The leaf table stored in the oracle at size `n` (Mantri, arXiv:2610.37635 (PDF sha256
d1fab777…1d0b33), §7.1, p. 37 (PDF p. 39): "Its leaves occupy the addresses `1^n 0 w`, where `w`
ranges over the root-to-leaf paths of the tree"). -/
def leafTable (O : Oracle) (n : ℕ) : Str → Bool :=
  fun w => O (unary n ++ false :: w)

end MantriCVQ


