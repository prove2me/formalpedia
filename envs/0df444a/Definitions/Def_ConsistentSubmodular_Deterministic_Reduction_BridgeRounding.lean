-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_BridgeRounding
-- name    : ConsistentSubmodular_Deterministic_Reduction_BridgeRounding
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:12:30.808175+00:00
-- url     : https://prove2.me/theorems/d8f0ce7b-de3f-44db-865d-1c1fc3a17b20
-- title:
--   Forced-element reserve of a bridge with $2N+1$ grid points
-- statement:
--   - `bridgeHeavy N`: the forced-element reserve of a bridge whose grid has $2N+1$ points, namely
--   $$\mathrm{bridgeHeavy}(N)\;=\;8\,N^{2}\cdot \mathrm{logBudget}\bigl(4(2N+1)\bigr),$$
--   where $\mathrm{logBudget}(x)=\lfloor\log_2 x\rfloor+1$. It is a natural number: $N^2$ times a constant times the logarithmic budget of $4(2N+1)$ tests, matching a threshold of order $N^{-2}/\log(\text{number of tests})$.
--
--   In the reduction for deterministic algorithms, the bridge paths connect the exit of one rounded window to the entry of the next; this quantity bounds how many elements are set aside as forced (heavy) elements when rounding such a bridge by concentration, and hence the extra cardinality allowed beyond the core budget.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/BridgeRounding.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_BridgeGrid
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_PhysicalOperationPath
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SharedThreshold
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Model
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_PhysicalSampling
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Simplex
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_SamplingOperators
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SamplingScale
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_RoundingBudget

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

set_option maxHeartbeats 2000000

/-- The forced-element reserve of a bridge with `2N + 1` grid points. -/
def bridgeHeavy (N : ℕ) : ℕ := 8 * N ^ 2 * logBudget (4 * (2 * N + 1))

end ConsistentSubmodular

end


