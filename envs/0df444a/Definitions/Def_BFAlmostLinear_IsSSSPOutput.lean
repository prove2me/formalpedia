-- Prove2me | Definitions.Def_BFAlmostLinear_IsSSSPOutput
-- name    : BFAlmostLinear_IsSSSPOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:38:33.937061+00:00
-- url     : https://prove2.me/theorems/d350b28e-4918-482f-9576-528c5632f085
-- title:
--   Input layout and correct output for single-source shortest paths with real weights
-- statement:
--   Let $G=(V,E)$ be a directed multigraph with $V=\{0,\dots,n-1\}$ and arcs $E=\{0,\dots,m-1\}$, arc $e$ going from $\mathrm{tail}(e)$ to $\mathrm{head}(e)$, with real weights $w:E\to\mathbb R$ of any sign and a source $s$. The distance
--   $$d(s,v)=\inf\Big\{\textstyle\sum_{e\in P}w(e) : P\text{ a walk from }s\text{ to }v\Big\}\in\mathbb R\cup\{\pm\infty\}$$
--   is $+\infty$ when $v$ is unreachable and $-\infty$ below a reachable closed walk of negative weight.
--
--   **Input.** Integer cells $0,1,2$ hold $n,m,s$; cells $3+e$ and $3+m+e$ hold $\mathrm{tail}(e)$ and $\mathrm{head}(e)$; real cell $e$ holds $w(e)$; every other cell is $0$.
--
--   **Correct output.** Integer cell $-1$ holds a tag $L$, and exactly one of the following holds.
--
--   1. $L\ge1$ and integer cells $-2,\dots,-1-L$ list the arcs of a closed walk of negative total weight whose start is reachable from $s$.
--   2. $L=0$, no closed walk whose start is reachable from $s$ has negative weight, and for every vertex $v$: integer cell $-2-2v$ is $0$ if $v$ is unreachable and $1$ otherwise; for reachable $v$, real cell $-1-v$ holds $d(s,v)$, and for $v\ne s$ integer cell $-3-2v$ holds a parent arc $e$ with $\mathrm{head}(e)=v$ and $d(s,v)=d(s,\mathrm{tail}(e))+w(e)$, such that following parent arcs from $v$ reaches $s$.
--
--   This is the specification met by the program of Theorem 1.1.
--
--   **Formalization Note** The graph is the published `AtomicDynRouting.ResidenceTime.Network (Fin n) (Fin m)`. Distances are infima over walks in `EReal`. The theorem names no output format; Lemma 4.2 "reports a negative cycle" and the proof of Theorem 1.1 "recover[s] the shortest paths", so the output is either a certified negative closed walk or exact distances with a shortest-path tree. Unreachable vertices need no write because memory starts at $0$.
-- source:
--   Hair, Li, Li, Zhang, Bellman-Ford in Almost-Linear Time, STOC 2027 submission (manuscript sha256 873b9acb…), Theorem 1.1, p.1; §1.1, p.2; Lemma 4.2, p.13; proof of Theorem 1.1, p.12

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Network
import Definitions.Def_BFAlmostLinear_Machine

namespace BFAlmostLinear

open AtomicDynRouting.ResidenceTime

/-!
# The input and output of single-source shortest paths

Hair, Li, Li, Zhang, *Bellman-Ford in Almost-Linear Time*, STOC 2027 submission (manuscript sha256
873b9acb…), Theorem 1.1, p.1, and §1.1, p.2: "All graphs G = (V, E) in this paper are directed and have
(possibly negative) real edge weights."

**Formalization Note.**
* The graph is the published `AtomicDynRouting.ResidenceTime.Network (Fin n) (Fin m)`: arc `e` goes from
  `G.tail e` to `G.head e`, so parallel arcs and self-loops are allowed. Its "paths" are walks.
* Distances are infima over walks, in `EReal`: `⊤` when `v` is unreachable, `⊥` below a reachable
  negative closed walk. The theorem names no output. Lemma 4.2, p.13 "reports a negative cycle", and the
  proof of Theorem 1.1, p.12 "recover[s] the shortest paths", so the output is either a certified
  negative closed walk, or the exact distances with a tree of shortest paths.
* **Input layout.** Integer memory: cell `0` is `n`, cell `1` is `m`, cell `2` is `s`, cells `3 + e` are
  the tails, cells `3 + m + e` the heads, all other cells `0`. Real memory: cell `e` holds `w e`, all other
  cells `0`.
* **Output layout**, read at the first halt. Integer cell `−1` is the tag `L`.
  - `L ≥ 1`: integer cells `−2 − j` for `j < L` list the arcs of a closed walk of negative total weight
    whose start is reachable from `s`.
  - `L = 0`: there is no such walk. Integer cell `−2 − 2v` is `0` if `v` is unreachable from `s` and `1`
    otherwise. For reachable `v`, real cell `−1 − v` is `d(s, v)`, and for `v ≠ s`, integer cell
    `−3 − 2v` is the parent arc of `v`. Parent arcs are tight, and following them from any reachable
    vertex reaches `s`.
  The two branches share cells; `L` says which one applies. Unreachable vertices need no write, because
  memory starts at `0`.
-/

/-- The total weight `∑_{e ∈ P} w e` of an arc list. -/
def pathWeight {E : Type} (w : E → ℝ) (P : List E) : ℝ := (P.map w).sum

/-- The distance `d(s, v)`: the infimum over walks from `s` to `v` of the total weight, in `EReal`. -/
noncomputable def dist {V E : Type} (G : Network V E) (w : E → ℝ) (s v : V) : EReal :=
  ⨅ (P : List E) (_ : G.IsPathFrom s v P), ((pathWeight w P : ℝ) : EReal)

/-- There is a walk from `s` to `v`. -/
def Reachable {V E : Type} (G : Network V E) (s v : V) : Prop := ∃ P : List E, G.IsPathFrom s v P

/-- The cell list `n, m, c, tail₀, …, tail_{m−1}, head₀, …, head_{m−1}`. -/
def graphCells {n m : ℕ} (G : Network (Fin n) (Fin m)) (c : ℕ) : List ℤ :=
  [(n : ℤ), (m : ℤ), (c : ℤ)] ++ List.ofFn (fun e : Fin m => (((G.tail e : ℕ)) : ℤ)) ++
    List.ofFn (fun e : Fin m => (((G.head e : ℕ)) : ℤ))

/-- A memory holding the list `l` from cell `0` on, and `0` elsewhere. -/
def memOfList {α : Type} (a : α) (l : List α) : ℤ → α :=
  fun z => if 0 ≤ z then l.getD z.toNat a else a

/-- The initial state on the input `(G, w)` with `c` in cell `2`. For Theorem 1.1, `c` is the source. -/
noncomputable def ssspInit {n m : ℕ} (G : Network (Fin n) (Fin m)) (w : Fin m → ℝ) (c : ℕ) :
    Machine.State :=
  Machine.initState (memOfList 0 (graphCells G c)) (memOfList 0 (List.ofFn w))

/-- The arc list `P` is stored from integer cell `−2` downward and `L = P.length` is in cell `−1`. -/
def ListsArcs {m : ℕ} (σ : Machine.State) (P : List (Fin m)) : Prop :=
  σ.imem (-1) = (P.length : ℤ) ∧
    ∀ (j : ℕ) (hj : j < P.length), σ.imem (-2 - (j : ℤ)) = (((P[j] : Fin m) : ℕ) : ℤ)

/-- Integer cell `−3 − 2v` holds the arc `e`. -/
def ParentCell {n m : ℕ} (σ : Machine.State) (v : Fin n) (e : Fin m) : Prop :=
  σ.imem (-3 - 2 * ((v : ℕ) : ℤ)) = ((e : ℕ) : ℤ)

/-- The state `σ` holds a correct answer to single-source shortest paths on `(G, w, s)`. -/
def IsSSSPOutput {n m : ℕ} (G : Network (Fin n) (Fin m)) (w : Fin m → ℝ) (s : Fin n)
    (σ : Machine.State) : Prop :=
  (∃ (v : Fin n) (P : List (Fin m)), ListsArcs σ P ∧ Reachable G s v ∧ G.IsPathFrom v v P ∧
      pathWeight w P < 0) ∨
  (σ.imem (-1) = 0 ∧
    (∀ (v : Fin n) (P : List (Fin m)), Reachable G s v → G.IsPathFrom v v P → 0 ≤ pathWeight w P) ∧
    ∀ v : Fin n,
      (¬ Reachable G s v → σ.imem (-2 - 2 * ((v : ℕ) : ℤ)) = 0) ∧
      (Reachable G s v →
        σ.imem (-2 - 2 * ((v : ℕ) : ℤ)) = 1 ∧
        ((σ.rmem (-1 - ((v : ℕ) : ℤ)) : ℝ) : EReal) = dist G w s v ∧
        ∃ (k : ℕ) (chain : ℕ → Fin n), chain 0 = v ∧ chain k = s ∧
          ∀ i < k, chain i ≠ s ∧ ∃ e : Fin m, ParentCell σ (chain i) e ∧ G.head e = chain i ∧
            G.tail e = chain (i + 1) ∧
            dist G w s (chain i) = dist G w s (chain (i + 1)) + ((w e : ℝ) : EReal)))

end BFAlmostLinear


