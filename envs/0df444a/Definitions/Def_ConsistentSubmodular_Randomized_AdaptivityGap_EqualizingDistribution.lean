-- Prove2me | Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_EqualizingDistribution
-- name    : ConsistentSubmodular_Randomized_AdaptivityGap_EqualizingDistribution
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:07:22.058276+00:00
-- url     : https://prove2.me/theorems/00f9e907-2ab6-4771-9e59-4900a3c15c4d
-- title:
--   Length $d_j=r_j-\ell_j$ of an interval in an interval-selection instance
-- statement:
--   For an interval-selection instance $I$ with intervals $[\ell_j,r_j]$, $j\in\{0,\dots,N\}$ (probabilities $p_j$, with $0\le\ell_j\le r_j$), the file defines one quantity.
--
--   - `intervalLength` $I\,j$: the length $d_j=r_j-\ell_j\ge0$ of interval $j$.
--
--   The notation $d_j$ is used throughout the analysis of nonincreasing consecutive intervals (Definition 2.3), where $d_0\ge d_1\ge\dots\ge d_N>0$, and of the equalizing distribution, whose probabilities are determined by the lengths $d_j$.
--
--   It provides the basic notation for the chain-based computation of the adaptivity gap in Appendix A (Lemma 4).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/EqualizingDistribution.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Chains

/-- The length `d_j = r_j - ℓ_j` of interval `j`. -/
def intervalLength {N : ℕ} (I : IntervalInstance N) (j : Fin (N + 1)) : ℝ :=
  I.right j - I.left j

end ConsistentSubmodular.Chains

end


