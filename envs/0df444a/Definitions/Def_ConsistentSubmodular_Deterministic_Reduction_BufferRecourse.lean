-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_BufferRecourse
-- name    : ConsistentSubmodular_Deterministic_Reduction_BufferRecourse
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:08:43.54935+00:00
-- url     : https://prove2.me/theorems/cf7fdeef-ca8b-47ad-b9f0-d4c233186bd1
-- title:
--   The rolling buffer at time zero is empty
-- statement:
--   This bundle contains no new definition. It consists of one proved lemma about the rolling buffer of the scheduling construction, where for a width $w$ and time $t$ the rolling buffer is the set $X_t\setminus X_{t-w}$ of the last $w$ arrived elements (natural-number subtraction, $X_t=\{e: e<t\}$ the arrived prefix).
--
--   The file proves that the rolling buffer at time $0$ is empty for every width $w$: $X_0\setminus X_0=\emptyset$.
--
--   This fact is the base case used when the selected set of the global schedule (core trajectory together with the rolling buffer) is shown to start from the empty set, as the consistency model requires.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/BufferRecourse.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SchedulingBasics

namespace ConsistentSubmodular

variable {n : ℕ}

@[simp] theorem rollingBuffer_zero (width : ℕ) : rollingBuffer n width 0 = ∅ := by
  simp [rollingBuffer, arrivedPrefix]

end ConsistentSubmodular


