-- Prove2me | Definitions.Def_ConsistentSubmodular_Randomized_Impossibility_HardInstance
-- name    : ConsistentSubmodular_Randomized_Impossibility_HardInstance
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:08:13.966039+00:00
-- url     : https://prove2.me/theorems/59f4b4ff-383a-4ddb-8f85-e52e3d79add6
-- title:
--   Hard instance for randomized impossibility: key times and group weights
-- statement:
--   Continuing the hard stream with budget $k$ and $3k+2$ arrivals (time $t$ is the moment after $t$ arrivals), the following are defined.
--
--   - `timeBefore k` $=3k$: all tiny sets have arrived, $U_0$ has not.
--   - `timeMiddle k` $=3k+1$: $U_0$ has arrived.
--   - `timeAfter k` $=3k+2$: $U_1$ has arrived (the end of the stream).
--   - `lpWeights x` is the vector of the weights of the three groups, $(1,\;x,\;x^2(1+x))$, the last entry being `lpThird x`; at $x=u_1$ these are the weights $1,u_1,u_2$ of Figure 2 of the paper.
--
--   The file also proves the evaluation of `lpWeights x` at indices $0$, $1$, $2$.
--
--   The three times are those at which consistency bounds the expected value of the algorithm by affine functions of the expected numbers of tiny sets held, and the weights are those of the weighted coverage objective, in the proof of Theorem 1 (impossibility for randomized algorithms, Appendix A.2).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Impossibility/HardInstance.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Impossibility_HardStream
import Definitions.Def_ConsistentSubmodular_Randomized_Impossibility_HardScalar

noncomputable section

open scoped BigOperators

open Finset

namespace ConsistentSubmodular.HardInstance

/-- Time `3k`: all tiny sets have arrived, `U₀` has not. -/
def timeBefore (k : ℕ) : Fin (3 * k + 2 + 1) := ⟨3 * k, by omega⟩

/-- Time `3k + 1`: `U₀` has arrived. -/
def timeMiddle (k : ℕ) : Fin (3 * k + 2 + 1) := ⟨3 * k + 1, by omega⟩

/-- Time `3k + 2`: `U₁` has arrived. -/
def timeAfter (k : ℕ) : Fin (3 * k + 2 + 1) := ⟨3 * k + 2, by omega⟩

/-- The weights `1, x, x² (1 + x)` of the three groups; at `x = u₁` they are the
weights `1, u₁, u₂` of Figure 2. -/
def lpWeights (x : ℝ) : Fin 3 → ℝ := ![1, x, lpThird x]

@[simp] theorem lpWeights_zero (x : ℝ) : lpWeights x 0 = 1 := rfl

@[simp] theorem lpWeights_one (x : ℝ) : lpWeights x 1 = x := rfl

@[simp] theorem lpWeights_two (x : ℝ) : lpWeights x 2 = lpThird x := rfl

end ConsistentSubmodular.HardInstance

end


