-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_DetMulEqSumProdMulDetSubmatrix
-- name    : Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_DetMulEqSumProdMulDetSubmatrix
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:20:55.954743+00:00
-- url     : https://prove2.me/theorems/4607d1a1-7414-4ed8-948c-423a0c622d93
-- title:
--   Det Mul Eq Sum Prod Mul Det Submatrix
-- statement:
--   Definitions and structural lemmas for Det Mul Eq Sum Prod Mul Det Submatrix, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/DetMulEqSumProdMulDetSubmatrix.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
def consRowMatrix {R : Type*} {r : ℕ} (u : Fin (r + 1) → R) (Y : Matrix (Fin r) (Fin (r + 1)) R) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  Matrix.of fun i => Fin.cases u (fun a => Y a) i
end Formalism.HermitianLatticeCounting.P


