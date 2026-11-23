-- Prove2me | Definitions.Def_Experiments_FiniteDifferenceSemigroup
-- name    : Experiments_FiniteDifferenceSemigroup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T01:48:29.958677+00:00
-- url     : https://prove2.me/theorems/54ec78c0-c89e-49f3-9340-d7aa845b3a40
-- title:
--   Finite Difference Semigroup
-- statement:
--   Definitions and structural lemmas for Finite Difference Semigroup, from Olli Niemitalo's pinned Finite separable rank of radial kernels development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/FiniteDifferenceSemigroup.lean

import Definitions.Def_Experiments_GeneratorBound
set_option autoImplicit true
open Filter NormedSpace Set
open scoped Topology
noncomputable section
namespace Experiments
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
end Experiments


