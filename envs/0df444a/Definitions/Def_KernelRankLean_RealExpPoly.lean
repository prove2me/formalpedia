-- Prove2me | Definitions.Def_KernelRankLean_RealExpPoly
-- name    : KernelRankLean_RealExpPoly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T01:48:32.278437+00:00
-- url     : https://prove2.me/theorems/7ab7252a-f6d6-4073-b57f-4085fdb23b2e
-- title:
--   Real Exp Poly
-- statement:
--   Definitions and structural lemmas for Real Exp Poly, from Olli Niemitalo's pinned Finite separable rank of radial kernels development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RealExpPoly.lean

import Definitions.Def_KernelRankLean_ExpPoly
set_option autoImplicit true
open Complex Polynomial
namespace KernelRank
noncomputable def conjPoly (A : ℂ[X]) : ℂ[X] := A.map (starRingEnd ℂ)
end KernelRank


