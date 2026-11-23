-- Prove2me | Definitions.Def_KernelRankLean_Representation
-- name    : KernelRankLean_Representation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T01:49:13.788922+00:00
-- url     : https://prove2.me/theorems/8284717d-03b4-4b37-9e07-fa389c88890e
-- title:
--   Representation
-- statement:
--   Definitions and structural lemmas for Representation, from Olli Niemitalo's pinned Finite separable rank of radial kernels development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Representation.lean

import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_Defs
set_option autoImplicit true
open Complex Polynomial
namespace KernelRank
noncomputable def pairWeight (μ : ℂ) : ℝ := if μ.im = 0 then 1 / 2 else 1
end KernelRank


