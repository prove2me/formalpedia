-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNeZeroOfIsLattice
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNeZeroOfIsLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:42:08.247812+00:00
-- url     : https://prove2.me/theorems/8e37e3ea-90e7-4745-9841-b8ff8049112d
-- title:
--   Exists Ne Zero Of Is Lattice
-- statement:
--   Definitions and structural lemmas for Exists Ne Zero Of Is Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNeZeroOfIsLattice.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsClassRepsMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module nonZeroDivisors
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.RankOne
open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
variable {K : Type} [Field K] [NumberField K] [StarRing K]
def mulE (I J : Submodule (𝓞 K) K) (hJI : J * I = 1) :
    Submodule (𝓞 K) K ≃ Submodule (𝓞 K) K where
  toFun M := I * M
  invFun M := J * M
  left_inv M := by change J * (I * M) = M; rw [← mul_assoc, hJI, one_mul]
  right_inv M := by change I * (J * M) = M; rw [← mul_assoc, mul_comm I J, hJI, one_mul]
end Formalism.HermitianLattices.Ext.L3.RankOne


