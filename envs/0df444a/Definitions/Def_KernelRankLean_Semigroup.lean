-- Prove2me | Definitions.Def_KernelRankLean_Semigroup
-- name    : KernelRankLean_Semigroup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T01:47:54.863866+00:00
-- url     : https://prove2.me/theorems/6d682aa6-08bd-4b5d-84c7-24117f5d9cdd
-- title:
--   Semigroup
-- statement:
--   Definitions and structural lemmas for Semigroup, from Olli Niemitalo's pinned Finite separable rank of radial kernels development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Semigroup.lean

import Mathlib
set_option autoImplicit true
open Filter NormedSpace Set
open scoped Topology
namespace KernelRank
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
end KernelRank


