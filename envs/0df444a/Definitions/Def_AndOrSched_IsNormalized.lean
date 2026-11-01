-- Prove2me | Definitions.Def_AndOrSched_IsNormalized
-- name    : AndOrSched_IsNormalized
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:28:54.784172+00:00
-- url     : https://prove2.me/theorems/8a3c0d55-5eec-484b-95e5-8a96b297103e
-- title:
--   The w.l.o.g. assumptions of §2
-- statement:
--   An instance is **normalized** if
--   1. $w_a=0$ for every $a\in A$;
--   2. every processing time is an integer;
--   3. $p_j\ge1$ for every job without predecessors, so that no job can complete at time $0$;
--   4. there are no redundant OR-arcs.
--
--   These are the assumptions under which the paper states LP (1), LP (5) and Lemmas 1–3.
--
--   **Formalization Note** Integrality is required of the processing times only; the weights stay real.
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §1, p.4 and §2, p.6, "W.l.o.g., we may assume that wa = 0 for all a ∈ A … all data is integer and pj ≥ 1"

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_orPred
import Definitions.Def_AndOrSched_nonRedPred
import Definitions.Def_AndOrSched_HasPred
open scoped Classical NNReal

namespace AndOrSched

/-- The paper's w.l.o.g. assumptions on an instance (Happach, Schulz, arXiv:2001.07011v1, §1, p.4 and §2, p.6):
1. `w_a = 0` for every `a ∈ A`;
2. all processing times are integers;
3. `pⱼ ≥ 1` for every job without predecessors, "so no job can complete at time 0";
4. there are no redundant OR-arcs.

**Formalization Note** "All data is integer" is required of the processing times only; the weights
stay real, since the analysis never uses their integrality. -/
def IsNormalized (I : Instance) : Prop :=
  (∀ a, I.w (Sum.inl a) = 0) ∧ (∀ j, ∃ n : ℕ, I.p j = n) ∧
  (∀ j, ¬ HasPred I j → 1 ≤ I.p j) ∧ ∀ b, nonRedPred I b = orPred I b

end AndOrSched


