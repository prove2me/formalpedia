-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_EqZeroOfMemMult
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_EqZeroOfMemMult
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T05:59:01.473898+00:00
-- url     : https://prove2.me/theorems/2988424c-c746-4420-806f-5913c7c9b3f7
-- title:
--   Eq Zero Of Mem Mult
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Mem Mult, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/EqZeroOfMemMult.lean

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.SG.Pf.Lem3Mass
open Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds Filter Topology
section Alg
variable {R : Type} [CommRing R] [StarRing R] {m : ℕ}
def Mult (c : R) (N : ℕ) : Set (Matrix (Fin m) (Fin m) R) := {X | ∃ W, X = c ^ N • W}
variable {c : R}
end Alg
section Top
variable {R : Type} [CommRing R] [StarRing R] [TopologicalSpace R] [IsTopologicalRing R] [ContinuousStar R]
  [CompactSpace R] [T2Space R] {m : ℕ}
instance compactSpace_matR : CompactSpace (Matrix (Fin m) (Fin m) R) :=
  inferInstanceAs (CompactSpace (Fin m → Fin m → R))
instance t2SpaceMatrix : T2Space (Matrix (Fin m) (Fin m) R) := inferInstanceAs (T2Space (Fin m → Fin m → R))
end Top
end Formalism.L2.SG.Pf.Lem3Mass


