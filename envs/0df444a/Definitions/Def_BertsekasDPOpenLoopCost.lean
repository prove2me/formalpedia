-- Prove2me | Definitions.Def_BertsekasDPOpenLoopCost
-- name    : BertsekasDPOpenLoopCost
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-11T01:09:50.681452+00:00
-- url     : https://prove2.me/theorems/a39975e1-a4f6-4f9e-ab91-0d0854293fca
-- title:
--   Expected cost of an open-loop control sequence
-- statement:
--   **Expected cost of an open-loop control sequence** in the basic stochastic model of Chapter 1 (used in §6.2). An *open-loop* control sequence $(u_0, u_1, \dots)$ fixes each stage's control in advance, ignoring the state actually reached. Its expected cost over the last $m$ stages, at stage $k = N-m-1$, is given by the recursion
--
--   $$J_{u,m+1}(x) \;=\; \sum_{w \in W} p_k\bigl(w \mid x, u_k\bigr)\Bigl[g_k(x, u_k, w) + J_{u,m}\bigl(f_k(x, u_k, w)\bigr)\Bigr], \qquad J_{u,0} = g_N,$$
--
--   which is the policy-cost recursion of the basic problem with the state-dependent control $\mu_k(x)$ replaced by the constant $u_k$.
--
--   This is the benchmark against which measurement-based schemes are judged: the open-loop feedback controller of §6.2 is worth using precisely because it is never worse than the best sequence of this restricted form (Prop. 6.2.1), whereas the certainty equivalent controller carries no such guarantee.
--
--   **Formalization Note** The definition imposes no admissibility requirement on the sequence; admissibility appears as a hypothesis in the theorems that use it. Stage indices follow the same remaining-stages convention as the rest of the Chapter 1 model.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Section 6.2

import Mathlib
import Definitions.Def_BertsekasDPModel

/-- Expected cost of a fixed (open-loop) control sequence in the basic problem
of Chapter 1: `BertsekasDPOpenLoopCost M useq m x` is the expected cost of the
last `m` stages starting from state `x` at stage `M.N - m`, when the control
at each stage `i` is the predetermined `useq i`, regardless of the state. -/
def BertsekasDPOpenLoopCost {S C W : Type} [Fintype W]
    (M : BertsekasDPModel S C W) (useq : ℕ → C) : ℕ → S → ℝ
  | 0, x => M.gN x
  | m + 1, x =>
      let k := M.N - (m + 1)
      let u := useq k
      ∑ w, M.p k x u w *
        (M.g k x u w + BertsekasDPOpenLoopCost M useq m (M.f k x u w))


