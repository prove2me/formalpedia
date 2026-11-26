-- Prove2me | Definitions.Def_FourierJacobi_Algebra_WeylSum
-- name    : FourierJacobi_Algebra_WeylSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:11:53.846315+00:00
-- url     : https://prove2.me/theorems/9917db09-10ec-5eee-a5da-a23af3bd2051
-- title:
--   Weyl Sum
-- statement:
--   Definitions and structural lemmas for Weyl Sum, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylSum.lean

import Definitions.Def_FourierJacobi_Algebra_WeylCoefficient10
set_option autoImplicit false
namespace FourierJacobi
namespace Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def allWeylCoefficients (t a b : K) : Fin 8 → Fin 11 → K := ![wcCoeffs0 t a b, wcCoeffs1 t a b, wcCoeffs2 t a b, wcCoeffs3 t a b, wcCoeffs4 t a b, wcCoeffs5 t a b, wcCoeffs6 t a b, wcCoeffs7 t a b]
end Algebra
end FourierJacobi


