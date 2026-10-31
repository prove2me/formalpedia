-- Prove2me | Definitions.Def_GeomRescale_Reachable
-- name    : GeomRescale_Reachable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:19:40.40014+00:00
-- url     : https://prove2.me/theorems/0e7990e5-34d7-4991-8266-6ea6d944e6e2
-- title:
--   Reachable states of Algorithm 2
-- statement:
--   A state is reachable on input $f, \Lambda$ if a finite sequence of steps leads to it from the initial state. This is the meaning of "throughout the algorithm" and "at every stage" in Lemmas 3.9–3.13.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Algorithm 2, p.10

import Mathlib
import Definitions.Def_GeomRescale_init
import Definitions.Def_GeomRescale_Step

namespace GeomRescale

/-- `s` is reachable from the initial state of Algorithm Rescaling-SFM on input `f`, `Λ`
(Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Algorithm 2, p.10). This is the formal meaning of "throughout the algorithm" and "at every
stage" in Lemmas 3.9–3.13. -/
def Reachable {n : ℕ} (f : Finset (Fin n) → ℤ) (Λ : ℝ) (s : St n) : Prop :=
  Relation.ReflTransGen (Step f Λ) (init n) s

end GeomRescale


