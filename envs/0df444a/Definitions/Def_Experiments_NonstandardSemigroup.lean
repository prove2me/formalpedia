-- Prove2me | Definitions.Def_Experiments_NonstandardSemigroup
-- name    : Experiments_NonstandardSemigroup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T01:47:52.963458+00:00
-- url     : https://prove2.me/theorems/3ef73afd-e8b1-425f-a36f-bb051722c572
-- title:
--   Nonstandard Semigroup
-- statement:
--   Definitions and structural lemmas for Nonstandard Semigroup, from Olli Niemitalo's pinned Finite separable rank of radial kernels development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/NonstandardSemigroup.lean

import Mathlib
set_option autoImplicit true
open Filter NormedSpace Set
open scoped Topology
noncomputable section
namespace Experiments
variable {A : Type*} [NormedRing A]
variable [NormedAlgebra ℝ A]
variable [CompleteSpace A]
end Experiments


