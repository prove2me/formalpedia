-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_UniformRoundedFamilies
-- name    : ConsistentSubmodular_Deterministic_Reduction_UniformRoundedFamilies
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:13:41.593357+00:00
-- url     : https://prove2.me/theorems/bb751ab1-e5ef-4241-b381-994b7d79a9ca
-- title:
--   Cardinality reserve and operation coefficient for rounded windows and bridges
-- statement:
--   Let $N$ be the accuracy parameter and $S$ a bound on the number of segments of a compressed window.
--
--   - `familyHeavy` $N\,S$: the cardinality reserve for the forced elements of windows and bridges, defined as `windowHeavyBound` $N\,S+$ `bridgeHeavy` $N$. Here `windowHeavyBound` $N\,S=64N^2\,\lceil\log\rceil$-type budget `logBudget`$(4M)$ with $M$ the window test bound for $(N,S)$, and `bridgeHeavy` $N=8N^2\,\texttt{logBudget}(4(2N+1))$ is the corresponding reserve for a bridge on a grid with $2N+1$ points.
--   - `familyLength` $S$: the operation coefficient for windows and bridges, `windowLengthBound` $S+10$ with `windowLengthBound` $S=100S+10$.
--
--   These are natural numbers: the first bounds how many elements may be forced into a rounded window or bridge, and the second bounds the number of physical operations per unit of core budget.
--
--   They are the explicit instantiations of the parameters $H$ and $L$ of the uniform transfer statements (for `HasUniformRoundedFamilies`) once windows have at most $S$ segments, and are used to compute the final recourse constant of the deterministic reduction.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/UniformRoundedFamilies.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_ClockWindows
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_RoundedWindow
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_ProgramAssembly
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_WindowSamples
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_FractionalWindow
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SharedThreshold
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_SamplingOperators
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SamplingScale
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_PathSubdivision
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Model
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_PhysicalSampling
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Simplex
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_RoundingBudget
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_BridgeRounding
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_FamilyTransfer

noncomputable section

namespace ConsistentSubmodular

/-- Cardinality reserve for the forced elements of windows and bridges. -/
def familyHeavy (N S : ℕ) : ℕ := windowHeavyBound N S + bridgeHeavy N

/-- Operation coefficient for windows and bridges. -/
def familyLength (S : ℕ) : ℕ := windowLengthBound S + 10

end ConsistentSubmodular

end


