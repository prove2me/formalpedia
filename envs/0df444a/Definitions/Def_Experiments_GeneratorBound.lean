-- Prove2me | Definitions.Def_Experiments_GeneratorBound
-- name    : Experiments_GeneratorBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T01:47:53.840805+00:00
-- url     : https://prove2.me/theorems/45bb1397-8318-4847-ac29-188e2caba8e2
-- title:
--   Generator Bound
-- statement:
--   Definitions and structural lemmas for Generator Bound, from Olli Niemitalo's pinned Finite separable rank of radial kernels development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/GeneratorBound.lean

import Mathlib
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
namespace Experiments
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
end Experiments


