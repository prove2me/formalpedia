-- Prove2me | Definitions.Def_AndOrSched_scaleD
-- name    : AndOrSched_scaleD
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:27:00.605007+00:00
-- url     : https://prove2.me/theorems/d0959c9a-8487-4374-b143-053fb628507b
-- title:
--   The scaling factor $D$
-- statement:
--   $D$ is the least common multiple of the denominators of the processing times $p_j\in\mathbb Q_{\ge0}$. Multiplying every processing time by $D$ makes all of them integers ("we may assume that all data is integer") and multiplies every completion time and every cost by $D$. $D=1$ when all processing times are integers.
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.6, "we may assume that all data is integer"

import Mathlib
import Definitions.Def_AndOrSched_Instance
open scoped Classical NNReal

namespace AndOrSched

/-- The scaling factor `D`: the least common multiple of the denominators of the processing times
(Happach, Schulz, arXiv:2001.07011v1, §2, p.6, "we may assume that all data is integer"). Multiplying every `pⱼ` by `D` makes
them integers, and scales every schedule and its cost by `D`.

**Formalization Note** `D = 1` for an empty job set and whenever all `pⱼ` are integers. -/
def scaleD (I : Instance) : ℕ :=
  Finset.univ.lcm fun j => (I.p j).den

end AndOrSched


