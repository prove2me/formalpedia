-- Prove2me | Definitions.Def_SchrijverSFM_Alg_Setting
-- name    : SchrijverSFM_Alg_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:59.148686+00:00
-- url     : https://prove2.me/theorems/a3464dfb-607a-4010-924d-222f21dc13ec
-- title:
--   §2–§4, pp. 348–352 — base polytope B_f, greedy vectors h^≺, moved orders ≺^{s,u}, the digraph D, distances, and one iteration of Schrijver's algorithm
-- statement:
--   This file fixes the objects of §2–§4 of Schrijver's paper. Throughout, $V = \{0, 1, \dots, n-1\}$ (the paper's $V = \{1, \dots, n\}$, §4), $f$ is a real-valued function on all subsets of $V$, and vectors $x \in \mathbb{R}^V$ are functions $V \to \mathbb{R}$.
--
--   **Vectors and the base polytope.** For $U \subseteq V$ write $x(U) := \sum_{v \in U} x(v)$ (display (4)). The base polytope is (display (3))
--   $$B_f := \{x \in \mathbb{R}^V \mid x(U) \le f(U) \text{ for all } U \subseteq V,\ x(V) = f(V)\}.$$
--   For $u \in V$, $\chi^u$ is the incidence vector of $u$: $\chi^u(v) = 1$ if $v = u$ and $0$ otherwise.
--
--   **Total orders and greedy vectors.** A total order $\prec$ on $V$ is given by a permutation $\sigma$ of $V$ read as a position map: $u \prec v$ iff $\sigma(u) < \sigma(v)$ (every total order on a finite set arises this way). For $v \in V$, $v_\prec := \{u \in V \mid u \prec v\}$ (display (5)), and the greedy vector is (display (6))
--   $$h^\prec(v) := f(v_\prec \cup \{v\}) - f(v_\prec).$$
--   A lower ideal of $\prec$ is a set $U$ with $u \in U,\ w \prec u \Rightarrow w \in U$. The interval is $(s,t]_\prec := \{v \mid s \prec v \preceq t\}$ (display (7)). For $s \prec u$, the order $\prec^{s,u}$ is obtained from $\prec$ by resetting $v \prec u$ to $u \prec v$ for each $v$ with $s \preceq v \prec u$, every other pair keeping its order; that is, $u$ is moved to the position just before $s$. It is characterized by: $v \prec^{s,u} w$ iff either $v = u$ and $s \preceq w \prec u$, or $v \prec w$ and $(v, w)$ is not a pair $(v, u)$ with $s \preceq v \prec u$.
--
--   **States.** A state of the algorithm is a finite list $(\prec_1, \lambda_1), \dots, (\prec_k, \lambda_k)$ of total orders with real weights; it represents the point (display (13))
--   $$x = \lambda_1 h^{\prec_1} + \dots + \lambda_k h^{\prec_k}.$$
--   A state is valid if $k \ge 1$, every $\lambda_i > 0$ and $\sum_i \lambda_i = 1$. The initial state for an order $\prec$ is the one-term list $(\prec, 1)$, i.e. $x = h^\prec$.
--
--   **The digraph and distances.** $D = (V, A)$ with $A := \{(u, v) \mid u \prec_i v \text{ for some } i\}$ (display (14)); $P := \{v \mid x(v) > 0\}$ and $N := \{v \mid x(v) < 0\}$ (display (15)). A vertex is reachable if a directed path (possibly of length $0$) leads to it from a vertex of $P$. The distance $d(v) \in \{0, 1, 2, \dots\} \cup \{\infty\}$ is the minimum number of arcs of a directed walk from $P$ to $v$, and $d(v) = \infty$ if there is none. Case 1 holds when no vertex of $N$ is reachable; then $U$ is the set of vertices that can reach $N$ by a directed path (of length $\ge 0$, so $N \subseteq U$).
--
--   **The choice rule of Case 2** (p. 351). $t$ is a reachable element of $N$ maximizing $(d(t), t)$ lexicographically (largest $d(t)$, then largest $t$ in the numbering of $V$); $s$ is the largest element with $(s, t) \in A$ and $d(s) + 1 = d(t)$. $\alpha$ is the maximum of $|(s,t]_{\prec_i}|$ over $i$, and $\beta$ (display (19)) is the number of indices $i$ with $|(s,t]_{\prec_i}| = \alpha$. The tuple $(d(t), t, s, \alpha, \beta)$ is compared lexicographically.
--
--   **One iteration** (pp. 351–352). From a valid state $S$ in Case 2, with $t, s$ chosen as above and an index $i$ (written $\prec_1 := \prec_i$, $\lambda_1 := \lambda_i$) with $|(s,t]_{\prec_1}| = \alpha$, an iteration produces a state $S'$ such that:
--   1. (subroutine, (12)/(17)) there are $\delta \ge 0$ and a convex combination of vectors $h^{\prec_1^{s,u}}$, $u \in (s,t]_{\prec_1}$, equal to $h^{\prec_1} + \delta(\chi^t - \chi^s)$;
--   2. (the point $x'$) with $y := x + \lambda_1\delta(\chi^t - \chi^s)$ (display (18)), the point $x'$ of $S'$ equals $x + \theta\lambda_1\delta(\chi^t - \chi^s)$ for some $\theta \in [0,1]$, with $x'(t) \le 0$ and either $\theta = 1$ (so $x' = y$) or $x'(t) = 0$: the point of the segment $\overline{xy}$ closest to $y$ with $x'(t) \le 0$;
--   3. (the new decomposition) $S'$ is valid, has at most $|V|$ terms, and its orders are, up to rearrangement, a sub-multiset of $\{\prec_j : j \ne i\}$ together with $\prec_1$ (allowed only if $x'(t) = 0$), followed by distinct orders of the form $\prec_1^{s,u}$ with $u \in (s,t]_{\prec_1}$ (each at most once).
--
--   A run of $m$ iterations is a sequence of states $S_0, S_1, \dots$ with $S_0$ an initial state and $S_{j+1}$ obtained from $S_j$ by one iteration for every $j < m$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The ground set is `Fin n`, "largest" refers to the order of `Fin n`, a total order is an `Equiv.Perm (Fin n)` used as a position map, a state is a `List (Equiv.Perm (Fin n) × ℝ)`, and distances are `ℕ∞`-valued (an empty infimum is $\infty$). The relation `IsMoved σ s u τ` characterizes $\prec^{s,u}$ by its comparisons, which determine it uniquely. An iteration is a relation, not a function: any $\delta$ and convex combination returned by the subroutine, any maximizing index $i$, and any output of the Carathéodory reduction are admitted, as the paper leaves these choices open. The paper's numbers lie in any ordered field; here they are real. The value oracle and running time are not modelled. Submodularity is the referenced platform definition `NonmonotoneSubmod.Shared.Submodular`.
-- source:
--   Schrijver, A combinatorial algorithm minimizing submodular functions in strongly polynomial time, J. Combin. Theory Ser. B 80 (2000), pp. 348–352, displays (3)–(7), (13)–(15), (17)–(19), §3 (definition of ≺^{s,u}, p. 349), §4 (Cases 1 and 2, pp. 351–352)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

namespace SchrijverSFM.Alg

open Classical

/-! Schrijver (2000), §2–§4, pp. 348–352. The ground set is `V = Fin n = {0, …, n-1}`
(the paper's `{1, …, n}`); subsets are `Finset (Fin n)`, vectors `x ∈ ℝ^V` are `Fin n → ℝ`.
A total order `≺` on `V` is a permutation `σ : Equiv.Perm (Fin n)` read as a position map:
`u ≺_σ v :↔ σ u < σ v`. -/

/-- Display (4): `x(U) = ∑_{v ∈ U} x(v)`. -/
noncomputable def xsum {n : ℕ} (x : Fin n → ℝ) (U : Finset (Fin n)) : ℝ :=
  ∑ v ∈ U, x v

/-- Display (3): the base polytope `B_f = {x ∈ ℝ^V | x(U) ≤ f(U) for all U ⊆ V, x(V) = f(V)}`. -/
def baseB {n : ℕ} (f : Finset (Fin n) → ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ U : Finset (Fin n), xsum x U ≤ f U) ∧ xsum x Finset.univ = f Finset.univ}

/-- Display (5): `v_≺ = {u ∈ V | u ≺ v}` for the total order `u ≺ v :↔ σ u < σ v`. -/
def before {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => σ u < σ v)

/-- Display (6): the greedy vector `h^≺(v) = f(v_≺ ∪ {v}) − f(v_≺)`. -/
def greedy {n : ℕ} (f : Finset (Fin n) → ℝ) (σ : Equiv.Perm (Fin n)) : Fin n → ℝ :=
  fun v => f (insert v (before σ v)) - f (before σ v)

/-- §2, p. 348: `U` is a lower ideal of `≺`: `u ∈ U` and `w ≺ u` imply `w ∈ U`. -/
def IsLowerIdeal {n : ℕ} (σ : Equiv.Perm (Fin n)) (U : Finset (Fin n)) : Prop :=
  ∀ u ∈ U, ∀ w : Fin n, σ w < σ u → w ∈ U

/-- Display (7): `(s, t]_≺ = {v | s ≺ v ≼ t}`. -/
def interval {n : ℕ} (σ : Equiv.Perm (Fin n)) (s t : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => σ s < σ v ∧ σ v ≤ σ t)

/-- §3, p. 349: `τ` is the order `≺^{s,u}` obtained from `≺ = σ` by resetting `v ≺ u` to
`u ≺ v` for each `v` with `s ≼ v ≺ u` (every other pair keeps its `σ`-order); i.e. `u` is
moved to the position just before `s`. Stated relationally: for all `v, w`,
`v ≺^{s,u} w` iff either `v = u` and `s ≼ w ≺ u`, or `v ≺ w` and the pair is not one of the
reset pairs `(v, u)` with `s ≼ v ≺ u`. -/
def IsMoved {n : ℕ} (σ : Equiv.Perm (Fin n)) (s u : Fin n) (τ : Equiv.Perm (Fin n)) : Prop :=
  ∀ v w : Fin n, τ v < τ w ↔
    ((v = u ∧ σ s ≤ σ w ∧ σ w < σ u) ∨
      (σ v < σ w ∧ ¬ (w = u ∧ σ s ≤ σ v ∧ σ v < σ u)))

/-- p. 350: the incidence vector `χ^u` of `u`. -/
def chi {n : ℕ} (u : Fin n) : Fin n → ℝ :=
  fun v => if v = u then 1 else 0

/-- A state of the algorithm (§4, display (13)): the list of pairs `(≺_i, λ_i)`, `i = 1, …, k`. -/
abbrev State (n : ℕ) := List (Equiv.Perm (Fin n) × ℝ)

/-- Display (13): `x = λ_1 h^{≺_1} + ⋯ + λ_k h^{≺_k}`. -/
noncomputable def point {n : ℕ} (f : Finset (Fin n) → ℝ) (S : State n) : Fin n → ℝ :=
  fun v => (S.map (fun p => p.2 * greedy f p.1 v)).sum

/-- §4, p. 351: the `λ_i` are positive and sum to 1 (and `k ≥ 1`). -/
def Valid {n : ℕ} (S : State n) : Prop :=
  S ≠ [] ∧ (∀ p ∈ S, 0 < p.2) ∧ (S.map Prod.snd).sum = 1

/-- §4, p. 351: "Initially, we choose an arbitrary total order `≺` and set `x = h^≺`." -/
def initial {n : ℕ} (σ₀ : Equiv.Perm (Fin n)) : State n := [(σ₀, 1)]

/-- Display (14): the arc set `A = {(u, v) | ∃ i, u ≺_i v}` of the digraph `D = (V, A)`. -/
def arc {n : ℕ} (S : State n) (u v : Fin n) : Prop :=
  ∃ p ∈ S, p.1 u < p.1 v

/-- Display (15): `P = {v ∈ V | x(v) > 0}`. -/
noncomputable def posSet {n : ℕ} (f : Finset (Fin n) → ℝ) (S : State n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => 0 < point f S v)

/-- Display (15): `N = {v ∈ V | x(v) < 0}`. -/
noncomputable def negSet {n : ℕ} (f : Finset (Fin n) → ℝ) (S : State n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => point f S v < 0)

/-- `v` can be reached in `D` by a directed path (possibly of length 0) from a vertex of `P`. -/
def reachable {n : ℕ} (f : Finset (Fin n) → ℝ) (S : State n) (v : Fin n) : Prop :=
  ∃ p ∈ posSet f S, Relation.ReflTransGen (arc S) p v

/-- There is a directed walk in `D` with exactly `m` arcs from a vertex of `P` to `v`. -/
def walkLen {n : ℕ} (f : Finset (Fin n) → ℝ) (S : State n) : ℕ → Fin n → Prop
  | 0, v => v ∈ posSet f S
  | m + 1, v => ∃ w, walkLen f S m w ∧ arc S w v

/-- §4, Case 2, p. 351: `d(v)`, the distance in `D` from `P` to `v` (minimum number of arcs of
a directed path from `P` to `v`), with `d(v) = ⊤` (`∞`) when `v` is not reachable from `P`. -/
noncomputable def dist {n : ℕ} (f : Finset (Fin n) → ℝ) (S : State n) (v : Fin n) : ℕ∞ :=
  ⨅ (m : ℕ) (_ : walkLen f S m v), (m : ℕ∞)

/-- §4, Case 1, p. 351: "D has no path from P to N". -/
def caseOne {n : ℕ} (f : Finset (Fin n) → ℝ) (S : State n) : Prop :=
  ¬ ∃ v ∈ negSet f S, reachable f S v

/-- §4, Case 1, p. 351: `U`, the set of vertices of `D` that can reach `N` by a directed path
(possibly of length 0, so `N ⊆ U`). -/
noncomputable def caseOneSet {n : ℕ} (f : Finset (Fin n) → ℝ) (S : State n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => ∃ w ∈ negSet f S, Relation.ReflTransGen (arc S) v w)

/-- §4, Case 2, p. 351: `t` is the element of `N` reachable from `P` with `d(t)` maximum and,
among those, largest in `V = Fin n` (lexicographic maximum of `(d(t), t)`). -/
def IsChosenT {n : ℕ} (f : Finset (Fin n) → ℝ) (S : State n) (t : Fin n) : Prop :=
  t ∈ negSet f S ∧ reachable f S t ∧
    ∀ t' ∈ negSet f S, reachable f S t' →
      toLex (dist f S t', t') ≤ toLex (dist f S t, t)

/-- §4, Case 2, p. 351: `s` is the largest element (in `V = Fin n`) with `(s, t) ∈ A` and
`d(s) = d(t) − 1`. -/
def IsChosenS {n : ℕ} (f : Finset (Fin n) → ℝ) (S : State n) (t s : Fin n) : Prop :=
  arc S s t ∧ dist f S s + 1 = dist f S t ∧
    ∀ s' : Fin n, arc S s' t → dist f S s' + 1 = dist f S t → s' ≤ s

/-- §4, Case 2, p. 351: `α`, the maximum of `|(s, t]_{≺_i}|` over `i = 1, …, k`. -/
def alpha {n : ℕ} (S : State n) (s t : Fin n) : ℕ :=
  (S.map (fun p => (interval p.1 s t).card)).foldr max 0

/-- Display (19): `β`, the number of `i ∈ {1, …, k}` with `|(s, t]_{≺_i}| = α`. -/
def beta {n : ℕ} (S : State n) (s t : Fin n) : ℕ :=
  (S.map (fun p => (interval p.1 s t).card)).count (alpha S s t)

/-- The tuple `(d(t), t, s, α, β)` of display (21), in the lexicographic order. -/
def lexKey {n : ℕ} (d : ℕ∞) (t s : Fin n) (a b : ℕ) : ℕ∞ ×ₗ (Fin n ×ₗ (Fin n ×ₗ (ℕ ×ₗ ℕ))) :=
  toLex (d, toLex (t, toLex (s, toLex (a, b))))

/-- Display (12)/(17): an output of the subroutine for `≺ = σ₁` and `s, t`: `δ ≥ 0` and a convex
combination `Mv` (nonnegative weights summing to 1) of vectors `h^{≺^{s,u}}` with
`u ∈ (s, t]_≺`, equal to `h^≺ + δ(χ^t − χ^s)`. -/
def SubroutineOutput {n : ℕ} (f : Finset (Fin n) → ℝ) (σ₁ : Equiv.Perm (Fin n)) (s t : Fin n)
    (δ : ℝ) (Mv : State n) : Prop :=
  0 ≤ δ ∧ (∀ q ∈ Mv, 0 ≤ q.2) ∧ (Mv.map Prod.snd).sum = 1 ∧
    (∀ q ∈ Mv, ∃ u ∈ interval σ₁ s t, IsMoved σ₁ s u q.1) ∧
    ∀ v : Fin n, greedy f σ₁ v + δ * (chi t v - chi s v) =
      (Mv.map (fun q => q.2 * greedy f q.1 v)).sum

/-- §4, p. 352: `x' = point f S'` is the point of the segment `[x, y]`,
`y = x + λ₁ δ (χ^t − χ^s)` (display (18)), closest to `y` with `x'(t) ≤ 0`:
`x' = x + θ λ₁ δ (χ^t − χ^s)` with `0 ≤ θ ≤ 1`, `x'(t) ≤ 0`, and `θ = 1` (`x' = y`) or `x'(t) = 0`. -/
def SegmentPoint {n : ℕ} (f : Finset (Fin n) → ℝ) (S S' : State n) (t s : Fin n)
    (lam₁ δ : ℝ) : Prop :=
  ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
    (∀ v : Fin n, point f S' v = point f S v + θ * (lam₁ * δ) * (chi t v - chi s v)) ∧
    point f S' t ≤ 0 ∧ (θ = 1 ∨ point f S' t = 0)

/-- §4, p. 352: the orders of the new decomposition `S'` of `x'` (after the Carathéodory
reduction) form a sub-multiset of `{≺_i : i ≠ 1} ∪ {≺₁^{s,u} : u ∈ (s, t]_{≺₁}}`, together with
`≺₁` itself only if `x'(t) = 0` ("if `x'(t) < 0` then we can do without `h^{≺₁}`"); each
moved order `≺₁^{s,u}` occurs at most once (`L₂.Nodup`). -/
def NewOrders {n : ℕ} (f : Finset (Fin n) → ℝ) (S S' : State n) (i : ℕ)
    (σ₁ : Equiv.Perm (Fin n)) (s t : Fin n) : Prop :=
  ∃ L₁ L₂ : List (Equiv.Perm (Fin n)),
    (S'.map Prod.fst).Perm (L₁ ++ L₂) ∧
    L₁.Subperm ((S.eraseIdx i).map Prod.fst ++ (if point f S' t = 0 then [σ₁] else [])) ∧
    L₂.Nodup ∧ ∀ τ ∈ L₂, ∃ u ∈ interval σ₁ s t, IsMoved σ₁ s u τ

/-- One iteration of the algorithm in Case 2 (§4, pp. 351–352), from state `S` to state `S'`,
with chosen `t`, `s` and index `i` of the order `≺₁` (`|(s, t]_{≺₁}| = α`). -/
def StepVia {n : ℕ} (f : Finset (Fin n) → ℝ) (S S' : State n) (t s : Fin n) (i : ℕ) : Prop :=
  Valid S ∧ ¬ caseOne f S ∧ IsChosenT f S t ∧ IsChosenS f S t s ∧
    ∃ σ₁ : Equiv.Perm (Fin n), ∃ lam₁ : ℝ, S[i]? = some (σ₁, lam₁) ∧
      (interval σ₁ s t).card = alpha S s t ∧
      ∃ δ : ℝ, (∃ Mv : State n, SubroutineOutput f σ₁ s t δ Mv) ∧
        SegmentPoint f S S' t s lam₁ δ ∧
        Valid S' ∧ S'.length ≤ n ∧
        NewOrders f S S' i σ₁ s t

/-- One iteration of the algorithm (some admissible choice of `t`, `s`, `i`). -/
def Step {n : ℕ} (f : Finset (Fin n) → ℝ) (S S' : State n) : Prop :=
  ∃ (t s : Fin n) (i : ℕ), StepVia f S S' t s i

/-- A run of `m` iterations: `S 0` is an initial state `[(≺, 1)]` and each `S (j+1)` is obtained
from `S j` by one iteration, for `j < m`. -/
def IsRun {n : ℕ} (f : Finset (Fin n) → ℝ) (S : ℕ → State n) (m : ℕ) : Prop :=
  (∃ σ₀ : Equiv.Perm (Fin n), S 0 = initial σ₀) ∧ ∀ j < m, Step f (S j) (S (j + 1))

end SchrijverSFM.Alg


