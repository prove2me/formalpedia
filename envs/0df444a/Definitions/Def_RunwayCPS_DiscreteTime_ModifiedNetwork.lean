-- Prove2me | Definitions.Def_RunwayCPS_DiscreteTime_ModifiedNetwork
-- name    : RunwayCPS_DiscreteTime_ModifiedNetwork
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:04.181761+00:00
-- url     : https://prove2.me/theorems/84ecf229-a48e-4151-9a8f-2dc45434fbd6
-- title:
--   §6.2: the discrete-time triangle-inequality modified network of 3-tuples (i, t, d), with d^min, d^max, and the arc cost c_fin(i)(t)
-- statement:
--   This file defines the network of §6.2, which handles separations that violate the triangle inequality.
--
--   **Parameters.** For a node $i$ of stage $p$ of $G$ with penultimate aircraft $a$ and final aircraft $b$,
--   $$
--   d^{\min}_i=\delta_{ab},\qquad
--   d^{\max}_i=\max\Big\{\max_{j:\, i\in P(j)}\big(\delta_{a,\mathrm{fin}(j)}-\delta_{b,\mathrm{fin}(j)}\big),\; d^{\min}_i\Big\},
--   $$
--   where $j$ ranges over the stage-$(p+1)$ nodes of $G$ that follow $i$ ($P(j)$ is the set of predecessors of $j$). At stage $n$ there is no such $j$ and $d^{\max}_i=d^{\min}_i$.
--
--   **Nodes.** A node of stage $p$ is a triple $(i,t,d)$ with $i$ a stage-$p$ node of $G$, $t\in\Gamma(i)$, and $d=0$ if $p=1$, while $d^{\min}_i\le d\le d^{\max}_i$ if $p\ge 2$.
--
--   **Arcs.** There is an arc from $(i,t',d')$ at stage $p$ to $(j,t'',d'')$ at stage $p+1$ when
--
--   1. $(i,j)$ is an arc of $G$;
--   2. $t''-t'\ge d^{\min}_j$;
--   3. $d''=\min\{t''-t',\,d^{\max}_j\}$;
--   4. if $p\ge 2$, $d'+t''-t'$ is at least the separation between the penultimate aircraft of $i$ and the final aircraft of $j$.
--
--   **Paths and costs.** A source-sink path chooses a node $(i_p,t_p,d_p)$ per stage $p=1,\dots,n$ with arcs between consecutive stages. It represents the schedule that puts $\mathrm{fin}(i_p)$ in position $p$ at time $t_p$. Each arc entering $(i,t,d)$ costs $c_{\mathrm{fin}(i)}(t)$ and arcs to the sink cost $0$, so the cost of a path is
--   $$
--   \sum_{p=1}^{n} c_{\mathrm{fin}(i_p)}(t_p).
--   $$
--
--   The parameter $d$ records how far apart the last two aircraft are (capped at $d^{\max}$), which is enough to check the separation between aircraft two positions apart.
--
--   **Formalization Note** $d$, $d^{\min}$, $d^{\max}$ and time differences are integers ($\mathbb Z$), since $\delta_{a,\mathrm{fin}(j)}-\delta_{b,\mathrm{fin}(j)}$ can be negative. Condition 4 is not imposed on arcs leaving stage $1$, whose nodes have no penultimate aircraft (as in the paper's proof of Lemma 6). The paper writes the arc cost $c(i,t)$; it is the cost $c_{\mathrm{fin}(i)}(t)$ of the final aircraft of $i$, as in §6.1.2. $\Gamma(i)$ is the full time window.
-- source:
--   Balakrishnan & Chandran, Algorithms for Scheduling Runway Operations Under Constrained Position Shifting, Oper. Res. 58(6) (2010), pp. 1658–1660, §6.2 (node conditions 1–3, d^min, d^max, arc conditions 1–4, closing paragraph on arc costs)

import Mathlib
import Definitions.Def_RunwayCPS_DiscreteTime_Network

namespace RunwayCPS.DiscreteTime

variable {n : ℕ}

/-- The final aircraft of the successors of the stage-`p` node `i` in `G`: the aircraft `c`
such that some stage-`(p+1)` node `j` of `G` with `fin(j) = c` follows `i` (`i ∈ P(j)`). It is
empty when `p = n`. -/
noncomputable def succFinals [NeZero n] (I : Instance n) (p : ℕ) (i : List (Fin n)) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter
    (fun c => ∃ j : List (Fin n), IsGNode I (p + 1) j ∧ RunwayCPS.Makespan.IsArc I.k p i j ∧ RunwayCPS.Makespan.final j = c)

/-- `d^min_i = δ_ab` (§6.2), where `a` and `b` are the penultimate and final aircraft of the
node `i`. Computed in `ℤ`. -/
def dmin [NeZero n] (I : Instance n) (i : List (Fin n)) : ℤ :=
  (I.δ (penult i) (RunwayCPS.Makespan.final i) : ℤ)

/-- `d^max_i = max { max_{j : i ∈ P(j)} (δ_{a,fin(j)} − δ_{b,fin(j)}), d^min_i }` (§6.2) for a
node `i` of stage `p` of `G`, with `a`, `b` its penultimate and final aircraft and `j` ranging
over the stage-`(p+1)` nodes of `G` that follow `i`. Computed in `ℤ` (the differences can be
negative); when `i` has no successor (stage `n`) the inner maximum is omitted and
`d^max_i = d^min_i`. -/
noncomputable def dmax [NeZero n] (I : Instance n) (p : ℕ) (i : List (Fin n)) : ℤ :=
  (succFinals I p i).fold max (dmin I i)
    (fun c => (I.δ (penult i) c : ℤ) - (I.δ (RunwayCPS.Makespan.final i) c : ℤ))

/-- A node `(i, t, d)` of the discrete-time triangle-inequality modified network (§6.2):
`i` is a node of `G`, `t` a landing period of `fin(i)`, `d` a separation bound in periods. -/
structure MNode (n : ℕ) where
  node : List (Fin n)
  t : ℕ
  d : ℤ

/-- `(i, t, d)` is a node of stage `p` of the modified network (§6.2): `i` is a stage-`p` node
of `G`, `t ∈ Γ(i)`, and `d = 0` if `p = 1`, while `d^min_i ≤ d ≤ d^max_i` if `p ≥ 2`. -/
def IsMNode [NeZero n] (I : Instance n) (p : ℕ) (v : MNode n) : Prop :=
  IsGNode I p v.node ∧ v.t ∈ Gamma I v.node ∧
  (p = 1 → v.d = 0) ∧
  (2 ≤ p → dmin I v.node ≤ v.d ∧ v.d ≤ dmax I p v.node)

/-- An arc from the stage-`p` node `u = (i, t', d')` to the stage-`(p+1)` node
`v = (j, t'', d'')` of the modified network (§6.2):
1. `(i, j)` is an arc of `G`;
2. `t'' − t' ≥ d^min_j`;
3. `d'' = min (t'' − t', d^max_j)`;
4. if `p ≥ 2` (so that `i` has a penultimate aircraft), `d' + t'' − t'` is at least the
   separation between the penultimate aircraft of `i` and the final aircraft of `j`.
All differences are taken in `ℤ`. -/
def IsMArc [NeZero n] (I : Instance n) (p : ℕ) (u v : MNode n) : Prop :=
  RunwayCPS.Makespan.IsArc I.k p u.node v.node ∧
  dmin I v.node ≤ (v.t : ℤ) - (u.t : ℤ) ∧
  v.d = min ((v.t : ℤ) - (u.t : ℤ)) (dmax I (p + 1) v.node) ∧
  (2 ≤ p → (I.δ (penult u.node) (RunwayCPS.Makespan.final v.node) : ℤ) ≤ u.d + (v.t : ℤ) - (u.t : ℤ))

/-- A source-sink path in the modified network: a node `P p` of stage `p` for every
`p = 1, …, n`, with an arc between consecutive stages (values outside `1, …, n` are
irrelevant). The source and sink arcs always exist. -/
def IsMPath [NeZero n] (I : Instance n) (P : ℕ → MNode n) : Prop :=
  (∀ p, 1 ≤ p → p ≤ n → IsMNode I p (P p)) ∧
  ∀ p, 1 ≤ p → p < n → IsMArc I p (P p) (P (p + 1))

/-- The aircraft sequence of a path: the 0-based position `q` receives `fin(i)` of the node
`(i, t, d)` at stage `q + 1`. -/
def mSeq [NeZero n] (P : ℕ → MNode n) : Fin n → Fin n :=
  fun q => RunwayCPS.Makespan.final (P ((q : ℕ) + 1)).node

/-- The landing times of a path: the 0-based position `q` lands at the period `t` of the node
`(i, t, d)` at stage `q + 1`. -/
def mTimes (P : ℕ → MNode n) : Fin n → ℕ :=
  fun q => (P ((q : ℕ) + 1)).t

/-- The cost of a path (§6.2, last paragraph): each arc entering a node `(i, t, d)` costs
`c_{fin(i)}(t)` and arcs to the sink cost zero, so the cost is the sum over the stages
`1, …, n` of `c_{fin(i_p)}(t_p)`. -/
def pathCost [NeZero n] (I : Instance n) (P : ℕ → MNode n) : ℝ :=
  ∑ q : Fin n, I.c (RunwayCPS.Makespan.final (P ((q : ℕ) + 1)).node) (P ((q : ℕ) + 1)).t

/-- The set of costs of source-sink paths of the modified network. -/
def pathCosts [NeZero n] (I : Instance n) : Set ℝ :=
  {x | ∃ P, IsMPath I P ∧ x = pathCost I P}

end RunwayCPS.DiscreteTime


