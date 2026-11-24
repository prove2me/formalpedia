-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_SpanUnitaryMatrix
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_SpanUnitaryMatrix
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:07.52401+00:00
-- url     : https://prove2.me/theorems/7254e2d6-4bd0-4c21-8316-16db27337de3
-- title:
--   Span Unitary Matrix
-- statement:
--   Definitions and structural lemmas for Span Unitary Matrix, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/SpanUnitaryMatrix.lean

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
open Matrix
namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
variable {n : ℕ}
def pm (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => if σ i = j then 1 else 0
def dph (a : Fin n) : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => if i = a then Complex.I else 1
end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks


