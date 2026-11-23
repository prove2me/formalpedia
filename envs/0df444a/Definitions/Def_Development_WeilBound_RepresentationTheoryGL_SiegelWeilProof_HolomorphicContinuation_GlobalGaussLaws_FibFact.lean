-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GlobalGaussLaws_FibFact
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GlobalGaussLaws_FibFact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:22:37.399411+00:00
-- url     : https://prove2.me/theorems/f3dc2377-85dc-474c-ae11-25cf9e34f504
-- title:
--   Fib Fact
-- statement:
--   Definitions and structural lemmas for Fib Fact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GlobalGaussLaws/FibFact.lean

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
open MeasureTheory
open scoped ENNReal NNReal
namespace PositivityTheory.Rg.Sw.Glob.Fib
variable {m n : ℕ} {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [MeasurableSpace X]
  [BorelSpace X]
end PositivityTheory.Rg.Sw.Glob.Fib


