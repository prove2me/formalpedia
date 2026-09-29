-- Prove2me | Definitions.Def_EdmondsKarp_Scaling_Augmentation
-- name    : EdmondsKarp_Scaling_Augmentation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:22:54.55892+00:00
-- url     : https://prove2.me/theorems/23fa296f-4789-4b7f-a6be-4d7d8a03dfe9
-- title:
--   Augmenting paths and flow augmentation in the Hitchcock network
-- statement:
--   Let $f$ be a function on the arcs of the network of Figure 1 with capacities $a_i$, $b_j$. For an ordered pair of nodes $(u, v)$ define the quantity $\varepsilon(u,v)$ of Edmonds–Karp §1.1 as follows. If $(u,v)$ is an arc other than the return arc (Case (a)), $\varepsilon(u,v) = c(u,v) - f(u,v)$: this is $a_i - f_{0i}$ for $(s, s_i)$, $b_j - f_{j0}$ for $(t_j, t)$ and $+\infty$ for $(s_i, t_j)$. If $(v, u)$ is an arc other than the return arc (Case (b)), $\varepsilon(u,v) = f(v,u)$. For any other pair, including both orientations of the return arc, $\varepsilon(u,v) = 0$. (No two arcs of Figure 1 are antiparallel, so the third case of the paper, Case (c), never occurs.)
--
--   An **augmenting path** relative to $f$ is a sequence of distinct nodes $s = u_1, u_2, \dots, u_p = t$ with $\varepsilon_i = \varepsilon(u_i, u_{i+1}) > 0$ for every $i$. Let
--   $$\varepsilon = \min_i \varepsilon_i,$$
--   a real number attained at some pair. The **augmentation** along the path increases $f(t,s)$ by $\varepsilon$, increases $f$ by $\varepsilon$ on every arc $(u_i, u_{i+1})$ used forward and decreases $f$ by $\varepsilon$ on every arc $(u_{i+1}, u_i)$ used in reverse. A **flow augmentation step** from $f$ to $f'$ means that $f'$ is the result of augmenting $f$ along some augmenting path relative to $f$.
--
--   These notions define the steps of every algorithm in the mission; counting them is the subject of Theorem 9.
--
--   **Formalization Note** $\varepsilon(u,v)$ is `resCap`, valued in `WithTop ℝ` so that the infinite-capacity arcs give $\top$. `IsPathMin T x L ε` says that the real number `ε` is a lower bound of all $\varepsilon_i$ along `L` and is attained. Paths are lists with `Nodup`, starting at `s` and ending at `t`; they never use the return arc. `pathDir L u v` is $+1$, $-1$ or $0$ according as `L` uses the arc $(u,v)$ forward, in reverse, or not at all.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 249, §1.1 (path, augmenting path, Cases (a)–(b), ε = min ε_i, the augmentation)

import Mathlib
import Definitions.Def_EdmondsKarp_Scaling_Transport

namespace EdmondsKarp.Scaling

variable {m n : ℕ}

/-- The quantity `ε_i` of §1.1 (p. 249) for a consecutive pair `(u, v)` of a path, in the network of
Figure 1 (no two arcs of `A` are antiparallel, so only Cases (a) and (b) occur):
Case (a), `(u, v) ∈ A`: `c(u, v) - f(u, v)` — this is `+∞` on the infinite-capacity arcs `(s_i, t_j)`;
Case (b), `(v, u) ∈ A`: `f(v, u)`.
Every other pair (including the return arc `(t, s)` in either direction) gets `0`, i.e. is not
usable in an augmenting path. -/
def resCap (T : Transport m n) (x : Flow m n) : Node m n → Node m n → WithTop ℝ
  | .s, .src i => ((T.a i - x.f0 i : ℝ) : WithTop ℝ)
  | .src _, .dst _ => ⊤
  | .dst j, .t => ((T.b j - x.fz j : ℝ) : WithTop ℝ)
  | .src i, .s => ((x.f0 i : ℝ) : WithTop ℝ)
  | .dst j, .src i => ((x.fx i j : ℝ) : WithTop ℝ)
  | .t, .dst j => ((x.fz j : ℝ) : WithTop ℝ)
  | _, _ => 0

/-- An augmenting path relative to `x` (§1.1, p. 249): a list `u_1 = s, …, u_p = t` of distinct
nodes such that every consecutive pair `(u_i, u_{i+1})` has `ε_i > 0`. -/
def IsAugPath (T : Transport m n) (x : Flow m n) (L : List (Node m n)) : Prop :=
  L.Nodup ∧ L.head? = some .s ∧ L.getLast? = some .t ∧
    ∀ e ∈ L.zip L.tail, 0 < resCap T x e.1 e.2

/-- `ε = min ε_i` over the consecutive pairs of the path `L` (§1.1, p. 249); `ε` is a real number
attained at some pair (a bottleneck arc). -/
def IsPathMin (T : Transport m n) (x : Flow m n) (L : List (Node m n)) (ε : ℝ) : Prop :=
  (∀ e ∈ L.zip L.tail, (ε : WithTop ℝ) ≤ resCap T x e.1 e.2) ∧
    ∃ e ∈ L.zip L.tail, resCap T x e.1 e.2 = (ε : WithTop ℝ)

/-- `+1` if `(u, v)` is traversed forward by the path `L` (a consecutive pair `u, v`), `-1` if it
is traversed in reverse (a consecutive pair `v, u`), `0` otherwise. -/
def pathDir (L : List (Node m n)) (u v : Node m n) : ℝ :=
  (if (u, v) ∈ L.zip L.tail then 1 else 0) - (if (v, u) ∈ L.zip L.tail then 1 else 0)

/-- The augmentation of §1.1 (p. 249) along `L` by `ε`: increase the return arc by `ε`; on each arc
of `A`, increase the flow by `ε` if the path uses it as a forward arc (Case (a)) and decrease it by
`ε` if the path uses it as a reverse arc (Case (b)). -/
def augment (x : Flow m n) (L : List (Node m n)) (ε : ℝ) : Flow m n where
  f0 i := x.f0 i + ε * pathDir L .s (.src i)
  fx i j := x.fx i j + ε * pathDir L (.src i) (.dst j)
  fz j := x.fz j + ε * pathDir L (.dst j) .t
  ret := x.ret + ε

/-- One flow augmentation: `y` is obtained from `x` by augmenting along some augmenting path relative
to `x` by its minimum `ε`. -/
def AugStep (T : Transport m n) (x y : Flow m n) : Prop :=
  ∃ (L : List (Node m n)) (ε : ℝ), IsAugPath T x L ∧ IsPathMin T x L ε ∧ y = augment x L ε

end EdmondsKarp.Scaling


