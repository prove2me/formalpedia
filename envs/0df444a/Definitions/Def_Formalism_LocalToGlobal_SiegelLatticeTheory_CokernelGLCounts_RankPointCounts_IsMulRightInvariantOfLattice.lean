-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IsMulRightInvariantOfLattice
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IsMulRightInvariantOfLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:30:49.705802+00:00
-- url     : https://prove2.me/theorems/a0e2f4ea-3e04-43a5-b08b-1e4288205fd1
-- title:
--   Is Mul Right Invariant Of Lattice
-- statement:
--   Definitions and structural lemmas for Is Mul Right Invariant Of Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/IsMulRightInvariantOfLattice.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Set Filter Topology
open scoped ENNReal NNReal Pointwise
namespace Formalism.L2.SG.CovariantRepresentation
section Lattice
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
def lcount (Γ : Subgroup H) (K : Set H) (x : H) : ℝ≥0∞ := ∑' γ : Γ, K.indicator 1 ((γ : H) * x)
def lwt (Γ : Subgroup H) (K : Set H) (x : H) : ℝ≥0∞ := K.indicator 1 x * (lcount Γ K x)⁻¹
end Lattice
section Bounded
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
end Bounded
end Formalism.L2.SG.CovariantRepresentation


