-- Prove2me | Definitions.Def_LCPlanarSteiner_RootData
-- name    : LCPlanarSteiner_RootData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:05:32.458613+00:00
-- url     : https://prove2.me/theorems/322ed40e-7088-4ef0-8115-d7076585ac7c
-- title:
--   Fractional rooted witnesses
-- statement:
--   A **rooted datum** consists of a graph, a root $r$, a list of distinct terminals $t$, each with a bound $b_t$ and a finite distribution of paths $(p, f^t_p)$, and purchases $x_e$. It is **valid** with upper bound $B$ when
--   1. the graph is well-formed, the root and terminals are vertices, and the terminals are distinct;
--   2. $0 \le b_t \le B$, and every listed path of $t$ is a simple path from $r$ to $t$ with $\ell(p) \le b_t$ and weight $f^t_p \ge 0$;
--   3. each distribution has total weight $\sum_p f^t_p = 1$, and $x_e \ge 0$;
--   4. the purchases dominate every terminal separately:
--   $$
--   \sum_{p \ni e} f^t_p \le x_e \qquad (e \in E,\ t \in T).
--   $$
--   Its cost is $X = \sum_e c_e x_e$, and $D = 1 + \lceil \log_2 k \rceil$ where $k$ is the number of terminals other than the root.
--
--   These are the fractional witnesses rounded by Lemma 3.8 and display (7).
--
--   **Formalization Note** A polynomially supported distribution is a finite list in the input.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 3.8, p.8; display (1), p.2; §3, p.4

import Mathlib
import Definitions.Def_LCPlanarSteiner_IsSPath
import Definitions.Def_LCPlanarSteiner_plen
import Definitions.Def_LCPlanarSteiner_Dlog

namespace LCPlanarSteiner

/-- **Fractional rooted witnesses: purchases dominating unit path distributions.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 3.8, p.8: "Suppose purchases x of cost X dominate polynomially supported unit
distributions of original simple paths, with paths to t of length at most b_t, where 0 ≤ b_t ≤ H";
display (1), p.2: "Σ_{p∈P_h(t)} f^t_p = 1 (t ∈ T), Σ_{p∈P_h(t): e∈p} f^t_p ≤ x_e (e ∈ E, t ∈ T)";
§3, p.4: "D = 1 + ⌈log₂ k⌉ after removing the root from the terminal set."

A datum consists of a graph `net`, a root `root`, a list `terms` of terminals, each with its bound
`b_t` and its distribution (a finite list of pairs `(path, weight)`), and purchases `x` (the `e`-th
entry is `x_e`).

`Valid R B` (with an upper bound `B` on the `b_t`): the graph is well-formed, the root and the
terminals are vertices, the terminals are distinct, `0 ≤ b_t ≤ B`, every listed path is a simple
path from the root to its terminal of length `≤ b_t` with weight `≥ 0`, the weights of each terminal
sum to `1`, `x ≥ 0`, and for every arc `e` and terminal `t` the weight of the paths of `t` through
`e` is at most `x_e` (domination, separately per terminal).

`X R = Σ_e c_e x_e` is the purchase cost and `D R = 1 + ⌈log₂ k⌉` with `k` the number of terminals
other than the root.

**Formalization Note.** "Polynomially supported" means a finite list given in the input. A terminal
equal to the root has only the empty path. Arcs with index `≥ m` do not enter `X`. -/
structure RootData where
  /-- the graph -/
  net : Net
  /-- the root `r` -/
  root : ℕ
  /-- terminals `t` with bound `b_t` and distribution `(path, weight)` -/
  terms : List (ℕ × ℚ × List (List ℕ × ℚ))
  /-- purchases `x_e` -/
  x : List ℚ

/-- Validity of a rooted datum with bounds `b_t ≤ B`. -/
def RootData.Valid (R : RootData) (B : ℚ) : Prop :=
  R.net.WF ∧ R.root < R.net.n ∧ (R.terms.map Prod.fst).Nodup ∧ (∀ a ∈ R.x, 0 ≤ a) ∧
  (∀ τ ∈ R.terms, τ.1 < R.net.n ∧ 0 ≤ τ.2.1 ∧ τ.2.1 ≤ B ∧
    (∀ pw ∈ τ.2.2, IsSPath R.net R.root τ.1 pw.1 ∧ plen R.net pw.1 ≤ τ.2.1 ∧ 0 ≤ pw.2) ∧
    (τ.2.2.map Prod.snd).sum = 1) ∧
  ∀ (e : ℕ), ∀ τ ∈ R.terms,
    ((τ.2.2.filter fun pw => decide (e ∈ pw.1)).map Prod.snd).sum ≤ R.x.getD e 0

/-- The purchase cost `X = Σ_e c_e x_e`. -/
def RootData.X (R : RootData) : ℚ :=
  ∑ e ∈ Finset.range R.net.arcs.length, R.net.cst e * R.x.getD e 0

/-- `D = 1 + ⌈log₂ k⌉`, `k` the number of terminals other than the root. -/
def RootData.D (R : RootData) : ℕ :=
  Dlog ((R.terms.map Prod.fst).filter fun t => t ≠ R.root).length

end LCPlanarSteiner


