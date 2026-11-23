-- Prove2me | Definitions.Def_KernelRankLean_ComplexRank
-- name    : KernelRankLean_ComplexRank
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T02:06:35.884125+00:00
-- url     : https://prove2.me/theorems/3497d7d9-2203-487a-b723-c48c65ba2eff
-- title:
--   Complex Rank
-- statement:
--   Definitions and structural lemmas for Complex Rank, from Olli Niemitalo's pinned Finite separable rank of radial kernels development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/ComplexRank.lean

import Definitions.Def_KernelRankLean_Differential
import Definitions.Def_KernelRankLean_RealExpPoly
set_option autoImplicit true
open Complex Polynomial NNReal
namespace KernelRank
noncomputable def expPolyAnnihilator {ι : Type*} [Fintype ι]
    (P : ι → ℂ[X]) (rate : ι → ℂ) : ℂ[X] :=
  ∏ i, (X - C (rate i)) ^ ((P i).natDegree + 1)
end KernelRank


