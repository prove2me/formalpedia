-- Prove2me | Definitions.Def_Experiments_UltrapowerSemigroup
-- name    : Experiments_UltrapowerSemigroup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T01:51:06.460629+00:00
-- url     : https://prove2.me/theorems/a7b1095e-23f7-491b-bd78-339b9716f0e6
-- title:
--   Ultrapower Semigroup
-- statement:
--   Definitions and structural lemmas for Ultrapower Semigroup, from Olli Niemitalo's pinned Finite separable rank of radial kernels development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/UltrapowerSemigroup.lean

import Definitions.Def_Experiments_NonstandardSemigroup
import Definitions.Def_Experiments_Ultrapower
set_option autoImplicit true
open Filter NormedSpace Set
open scoped Topology
noncomputable section
namespace Experiments.NSA
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
end Experiments.NSA


