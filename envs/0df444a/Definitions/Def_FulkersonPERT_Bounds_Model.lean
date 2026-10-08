-- Prove2me | Definitions.Def_FulkersonPERT_Bounds_Model
-- name    : FulkersonPERT_Bounds_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:08:30.306369+00:00
-- url     : https://prove2.me/theorems/bbd26921-7346-4a8a-803a-16402c246f38
-- title:
--   §3–§4, pp. 4–8 — bundle distributions, the product (3.5), e_i (3.7), mean lengths (3.12), g_i (3.13) and the numbers f_i (4.2)
-- statement:
--   This file fixes the stochastic PERT model of Fulkerson (1962), §3–§4.
--
--   Let $N$ be a project network with events $0,1,\dots,n$ (origin $0$, terminal $n$), every arc $(i,j)$ satisfying $i<j$, and every event lying on a path from the origin to the terminal. Fulkerson's node $i$ is event $i-1$. For an event $j$, the **bundle** $B_j$ is the set of arcs $(i,j)$ entering $j$; we write $\operatorname{pred}(j)$ for the set of their tails. The origin's bundle is empty.
--
--   1. **Bundle distributions** ((3.1)–(3.3)). For every event $j$ there is a finite set $S_j$ of *bundle vectors* $v:\{0,\dots,n\}\to\mathbb R$, where $v_i$ is the length of arc $(i,j)$ (coordinates with $i\notin\operatorname{pred}(j)$ are carried along but never used), and a weight $p_j(v)$ for each $v$. The data form a probability model, written $\mathrm{IsProb}$, when $p_j(v)\ge 0$ for $v\in S_j$ and $\sum_{v\in S_j}p_j(v)=1$ for every $j$, including the origin.
--   2. **Assignments and the product probability** ((3.4)–(3.5)). An assignment $\omega$ chooses one bundle vector $\omega_j\in S_j$ for every event; the length of arc $(i,j)$ is then $t_{ij}=\omega_j(i)$, and the probability of $\omega$ is
--   $$p(\omega)=\prod_{j=0}^{n}p_j(\omega_j),$$
--   which expresses independence between bundles.
--   3. **Expected critical path length** ((3.6)–(3.7)). With $\ell_i(t)$ the critical (longest) path length from the origin to $i$ under the arc lengths $t$, computed by the earliest-event-time recursion,
--   $$e_i=\sum_{\omega}p(\omega)\,\ell_i(t(\omega)),$$
--   the sum running over all assignments drawn from the supports.
--   4. **Mean arc lengths and $g$** ((3.12)–(3.13)). $\bar t_{ij}=\sum_{v\in S_j}p_j(v)\,v_i$, and $g_i=\ell_i(\bar t)$, the critical path length for the mean arc lengths.
--   5. **The numbers $f$** ((4.2)). $f_0=0$ and, for $j\ne0$,
--   $$f_j=\sum_{v\in S_j}p_j(v)\,\max_{i\in\operatorname{pred}(j)}\bigl(f_i+v_i\bigr).$$
--   Only the distribution of the bundle of $j$ enters at $j$.
--   6. **Paths** ((3.6)). A path to $i$ is a list of events starting at $0$, ending at $i$, with consecutive events joined by arcs; its length is the sum of its arc lengths.
--   7. **Joint distributions** (remark, p. 12). A finite set of complete length assignments $y$ with weights $p(y)$; its expected critical path lengths $\sum_y p(y)\ell_i(y)$, its mean arc lengths $\sum_y p(y)y_{ij}$, and its bundle marginals (the law of $v=(y_{ij})_i$ at each event $j$).
--
--   These are the objects compared in Fulkerson's inequalities $g_i\le f_i\le e_i$.
--
--   **Formalization Note** The maximum over the arcs entering $j$ is a `Finset.sup'` over the nonempty set $\operatorname{pred}(j)$, which is Fulkerson's convention that terms of missing arcs are ignored (lengths $-\infty$). There is one arc per ordered pair of events, Fulkerson's own convention in (3.13). Arc lengths are arbitrary reals: the footnote on p. 4 says nonnegativity is not essential in §3–§4. Distributions are data plus the predicate `IsProb`; `p` is only read on the support.
-- source:
--   Fulkerson, Expected Critical Path Lengths in PERT Networks, RAND Memorandum RM-3075-PR (1962), pp. 2–8, §2, (3.1)–(3.13), (4.2)–(4.3); remark p. 12

import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork
import Definitions.Def_CriticalPath_Events_EventTimes

namespace FulkersonPERT.Bounds

open CriticalPath.Events
open scoped Classical

variable {n : ℕ}

/-- Bundle distributions, Fulkerson (1962) §3, (3.1)–(3.3), pp. 4–5. For every event `j` the
bundle `B_j` consists of the arcs `(i, j)` with `i ∈ N.pred j`; a *bundle vector* at `j` is a
function `v : Fin (n + 1) → ℝ` where `v i` is the length of arc `(i, j)` (coordinates outside
`N.pred j` are carried but never read). `supp j` is the finite support of the bundle's
distribution and `p j v` the probability of the bundle vector `v`. -/
structure BundleDist (n : ℕ) where
  /-- The finite support of the distribution of the bundle vector at event `j`. -/
  supp : Fin (n + 1) → Finset (Fin (n + 1) → ℝ)
  /-- `p j v` is the probability `p(t_{B_j})` of the bundle vector `v` at event `j`, (3.3). -/
  p : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ

/-- Each bundle distribution is a probability distribution on its finite support. -/
def BundleDist.IsProb (D : BundleDist n) : Prop :=
  (∀ j, ∀ v ∈ D.supp j, 0 ≤ D.p j v) ∧ ∀ j, ∑ v ∈ D.supp j, D.p j v = 1

/-- The arc lengths of an assignment `ω` of bundle vectors, (3.4): `ω j` is the bundle vector of
event `j`, so the length of arc `(i, j)` is `ω j i`. -/
def arcLengths (ω : Fin (n + 1) → Fin (n + 1) → ℝ) : Fin (n + 1) → Fin (n + 1) → ℝ :=
  fun i j => ω j i

/-- The probability of an assignment under independence between bundles, (3.5):
`p(t) = p(t_{B_1}) ⋯ p(t_{B_n})`. -/
noncomputable def prob (D : BundleDist n) (ω : Fin (n + 1) → Fin (n + 1) → ℝ) : ℝ :=
  ∏ j, D.p j (ω j)

/-- The expected critical path length `e_i = Σ_t p(t) ℓ_i(t)`, (3.7): the sum over every
assignment of bundle vectors from the supports, weighted by the product probability (3.5), of the
critical path length `ℓ_i(t)` (Kelley's earliest event time). -/
noncomputable def expectedLength (N : ProjectNetwork n) (D : BundleDist n) (i : Fin (n + 1)) :
    ℝ :=
  ∑ ω ∈ Fintype.piFinset D.supp, prob D ω * earliest N (arcLengths ω) i

/-- The expected arc lengths `t̄_α = Σ_{t_B} p(t_B) t_α`, (3.12): `meanLength D i j` is the
expected length of arc `(i, j)`. -/
noncomputable def meanLength (D : BundleDist n) (i j : Fin (n + 1)) : ℝ :=
  ∑ v ∈ D.supp j, D.p j v * v i

/-- The numbers `g_i` of (3.13): the critical path length to `i` for the expected arc lengths. -/
noncomputable def meanCPL (N : ProjectNetwork n) (D : BundleDist n) (i : Fin (n + 1)) : ℝ :=
  earliest N (meanLength D) i

/-- The numbers `f_j` of (4.2), p. 8: `f_origin = 0` and, for `j ≠ 0`,
`f_j = Σ_{v} p_j(v) · max_{i ∈ pred j} (f_i + v_i)`, the maximum over the arcs `(i, j)` that
exist (missing arcs ignored). Only the bundle distribution of event `j` enters at `j`. -/
noncomputable def fNum (N : ProjectNetwork n) (D : BundleDist n) (j : Fin (n + 1)) : ℝ :=
  if h : j = 0 then 0
  else ∑ v ∈ D.supp j, D.p j v *
    (N.pred j).attach.sup' (Finset.attach_nonempty_iff.2 (N.pred_nonempty h))
      (fun i => fNum N D i.1 + v i.1)
termination_by j.val
decreasing_by exact N.lt_of_mem_pred i.2

/-- The length of a path given as its list of nodes `v_0, …, v_k`: the sum of `y v_{r-1} v_r`. -/
def pathLength (y : Fin (n + 1) → Fin (n + 1) → ℝ) (p : List (Fin (n + 1))) : ℝ :=
  ((p.zip p.tail).map (fun e => y e.1 e.2)).sum

/-- `p` is a path (directed chain) of the network from the origin to the event `i`, listed by its
nodes. -/
def IsPathTo (N : ProjectNetwork n) (p : List (Fin (n + 1))) (i : Fin (n + 1)) : Prop :=
  p.head? = some 0 ∧ p.getLast? = some i ∧ p.IsChain (fun a b => (a, b) ∈ N.P)

/-- A joint finite distribution on all arc lengths (remark, p. 12): `supp` is a finite set of
length assignments `y` (`y i j` the length of arc `(i, j)`), and `p y` the probability of `y`. -/
structure JointDist (n : ℕ) where
  /-- The finite support of the joint distribution. -/
  supp : Finset (Fin (n + 1) → Fin (n + 1) → ℝ)
  /-- `p y` is the probability of the assignment `y`. -/
  p : (Fin (n + 1) → Fin (n + 1) → ℝ) → ℝ

/-- A joint distribution is a probability distribution on its finite support. -/
def JointDist.IsProb (J : JointDist n) : Prop :=
  (∀ y ∈ J.supp, 0 ≤ J.p y) ∧ ∑ y ∈ J.supp, J.p y = 1

/-- The expected critical path length to `i` under a joint distribution. -/
noncomputable def jointExpected (N : ProjectNetwork n) (J : JointDist n) (i : Fin (n + 1)) : ℝ :=
  ∑ y ∈ J.supp, J.p y * earliest N y i

/-- The expected length of arc `(i, j)` under a joint distribution. -/
noncomputable def jointMean (J : JointDist n) (i j : Fin (n + 1)) : ℝ :=
  ∑ y ∈ J.supp, J.p y * y i j

/-- The bundle marginals of a joint distribution: at event `j`, the law of the bundle vector
`fun i => y i j`. -/
noncomputable def JointDist.marginals (J : JointDist n) : BundleDist n where
  supp j := J.supp.image (fun y i => y i j)
  p j v := ∑ y ∈ J.supp with (fun i => y i j) = v, J.p y

end FulkersonPERT.Bounds


