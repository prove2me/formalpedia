-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_BridgeGrid
-- name    : ConsistentSubmodular_Deterministic_Reduction_BridgeGrid
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:11:08.556512+00:00
-- url     : https://prove2.me/theorems/f10bf17d-2372-4e9c-be8b-7ceb7f5df7cc
-- title:
--   Bridge grid: $K+1$ equally spaced points between the two vertices of the simplex on two candidates
-- statement:
--   Points of $\mathrm{Point}(1)$ are weight vectors on the two candidates $0,1$; `vertex` $i$ is the vector $\delta_i$ putting all weight on candidate $i$, and `mix` $(p,q,x)=(1-x)p+xq$.
--
--   - `ConsistentSubmodular.BridgeGrid.point` $(K,j)$: for $K\in\mathbb{N}$ and $j\in\{0,\dots,K\}$, the grid point
--   $$\mathrm{mix}\big(\delta_0,\delta_1,\ j/K\big)=\big(1-\tfrac jK,\ \tfrac jK\big),$$
--   i.e. the $j$-th of $K+1$ equally spaced points on the segment from $\delta_0$ to $\delta_1$ (with the real-number convention $x/0=0$ when $K=0$).
--
--   The file also proves the endpoint facts: the point with $j=0$ equals $\delta_0$, and, for $K>0$, the point with $j=K$ equals $\delta_1$.
--
--   This grid is used in the construction of the bridge between two cores: a path from $\delta_0$ to $\delta_1$ is discretized into $K$ equal steps so that it can be rounded to physical sets (Appendix B).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/BridgeGrid.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_PhysicalSampling
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_CompatibleProfiles
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Paths
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SharedThreshold
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Model
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_PathSubdivision

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace BridgeGrid

variable {n : ℕ}

def point (K : ℕ) (j : Fin (K + 1)) : Point 1 :=
  mix (vertex 0) (vertex 1) ((j.val : ℝ) / K)

@[simp] theorem initial (K : ℕ) : point K 0 = vertex 0 := by simp [point]

@[simp] theorem terminal (K : ℕ) (hK : 0 < K) : point K (Fin.last K) = vertex 1 := by
  simp [point, ne_of_gt (show (0 : ℝ) < K by exact_mod_cast hK)]

end BridgeGrid

end ConsistentSubmodular

end


