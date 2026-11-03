-- Prove2me | Definitions.Def_NearestDSM_solSet
-- name    : NearestDSM_solSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:20:13.030486+00:00
-- url     : https://prove2.me/theorems/f38e0c79-8590-4833-b4d1-50e9ca562594
-- title:
--   The solution set $[y^*]=\{y\mid F(y)=0\}$
-- statement:
--   The solution set of the optimality conditions (2.5) is
--   $$
--   \{y\in\mathbb R^{2n-1}\mid F(y)=0\}.
--   $$
--   By Lemma 3.3 it is an equivalence class, and the paper writes it $[y^*]$ for any of its elements $y^*$. It is the set of optimal dual multipliers of the nearest doubly stochastic matrix problem.
--
--   **Formalization Note** The paper's $n$ is $n+1$.
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, (2.5) p.8, Lemma 3.3, p.14

import Mathlib
import Definitions.Def_NearestDSM_Fres

namespace NearestDSM

/-- The solution set `{y | F(y) = 0}` of the system (2.5), Hu, Im, Li & Wolkowicz, *A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem*, arXiv:2107.09631v1, Lemma 3.3,
p.14; the paper writes it `[y∗]` (Lemma 3.3: it is an equivalence class). -/
def solSet {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Set (Dual n) :=
  {y | Fres Xh y = 0}

end NearestDSM


