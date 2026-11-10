-- Prove2me | Definitions.Def_PebbleMotion_Trees_Moves
-- name    : PebbleMotion_Trees_Moves
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:38:11.870776+00:00
-- url     : https://prove2.me/theorems/aa30695d-0fb1-437c-904e-1744c798bf6e
-- title:
--   Configurations, moves, solution sequences, transitivity, feasible puzzles, PMT instances
-- statement:
--   Pebbles are $P=\{1,\dots,n\}$. A **configuration** of $P$ on the vertex set $V$ is a map $f:V\to\{0,1,\dots,n\}$ with exactly one vertex carrying each label $i\in\{1,\dots,n\}$; vertices with $f(v)=0$ are **blanks**.
--
--   A **move** $(u,v)$ shifts the pebble on $u$ to the adjacent blank $v$: it is valid in $f$ when $u\sim v$ in $G$, $f(u)\ne0$ and $f(v)=0$, and it produces the configuration with $f(u)$ on $v$ and $u$ blank. A **solution sequence from $f$ to $g$** is a list of moves, each valid in the configuration reached so far, ending at $g$; its length is the number of moves.
--
--   The **unlabeled** version tracks only the occupied set $S$: a move $(u,v)$ needs $u\sim v$, $u\in S$, $v\notin S$, and replaces $S$ by $(S\setminus\{u\})\cup\{v\}$.
--
--   $(G,P)$ is **transitive** if for every configuration $f$, every pebble $i$ and every vertex $v$ some solution sequence from $f$ reaches a configuration with $i$ on $v$. The puzzle $(G,P)$ is **feasible** if for all configurations $f,g$ there is a solution sequence from $f$ to $g$.
--
--   An **instance of the Pebble Motion Problem on Trees** on the vertices $\{0,\dots,N-1\}$ is a tree $G$, $n$ with $n\le N-2$ (written $n+2\le N$), configurations $f,g$, and $n+k(G)<N$.
-- source:
--   Nakamigawa and Sakuma, Structural Origins of Cubic Complexity in Pebble Motion, arXiv:2503.20550 (held revision dated 2026-11-03), §1.1, §2.1, §2.2 (Problem PMT) and Lemma 7, p.2, 7–9, 13, PDF SHA256 efd330453039630e97e2ef1029ef0b2b3ac5a16bd700a2c5fad226582870f412

import Mathlib
import Definitions.Def_PebbleMotion_Trees_Isthmus

set_option autoImplicit false

namespace PebbleMotion.Trees

variable {V : Type*} [DecidableEq V]

/-- A **configuration** of the pebbles `P = {1, …, n}` on the vertex set `V` (Nakamigawa–Sakuma,
§1.1, p.2): a map `f : V → {0, 1, …, n}` with `|f⁻¹(i)| = 1` for each `1 ≤ i ≤ n`; `f⁻¹(i)` is the
vertex of pebble `i` and `f⁻¹(0)` the set of blanks. -/
def IsConfiguration {n : ℕ} (f : V → Fin (n + 1)) : Prop :=
  ∀ i : Fin (n + 1), i ≠ 0 → ∃! v : V, f v = i

/-- A **move** `m = (u, v)` (p.2) shifts the pebble on `u` to the adjacent blank vertex `v`: it is
valid in the configuration `f` when `u` and `v` are adjacent in `G`, `u` carries a pebble and `v`
is a blank. -/
def IsValidMove (G : SimpleGraph V) {n : ℕ} (f : V → Fin (n + 1)) (m : V × V) : Prop :=
  G.Adj m.1 m.2 ∧ f m.1 ≠ 0 ∧ f m.2 = 0

/-- The configuration after the move `m = (u, v)`: the pebble `f u` is now on `v`, and `u` is a
blank. -/
def applyMove {n : ℕ} (f : V → Fin (n + 1)) (m : V × V) : V → Fin (n + 1) :=
  Function.update (Function.update f m.2 (f m.1)) m.1 0

/-- `ms` is a **solution sequence from `f` to `g`** on the board graph `G` (p.2): a finite sequence
of moves, each valid in the configuration reached so far, transforming `f` into `g`. Its length is
`ms.length`, the number of moves. -/
def IsSolutionSeq (G : SimpleGraph V) {n : ℕ} :
    (V → Fin (n + 1)) → (V → Fin (n + 1)) → List (V × V) → Prop
  | f, g, [] => f = g
  | f, g, m :: ms => IsValidMove G f m ∧ IsSolutionSeq G (applyMove f m) g ms

/-- A sequence of **unlabeled** moves transferring the pebbles occupying exactly `S` to occupy
exactly `S'` (Lemma 7, p.13): each move `(u, v)` goes along an edge of `G` from an occupied vertex
`u` to an unoccupied vertex `v`. -/
def IsTransferSeq (G : SimpleGraph V) : Finset V → Finset V → List (V × V) → Prop
  | S, S', [] => S = S'
  | S, S', m :: ms =>
      (G.Adj m.1 m.2 ∧ m.1 ∈ S ∧ m.2 ∉ S) ∧ IsTransferSeq G (insert m.2 (S.erase m.1)) S' ms

/-- The pair `(G, P)`, `P = {1, …, n}`, is **transitive** (p.7): for every configuration `f`,
every pebble `i` can be moved from its current vertex to any prescribed vertex `v` of `G` by a
finite sequence of moves. -/
def IsTransitive (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ f : V → Fin (n + 1), IsConfiguration f →
    ∀ i : Fin (n + 1), i ≠ 0 → ∀ v : V,
      ∃ (ms : List (V × V)) (h : V → Fin (n + 1)), IsSolutionSeq G f h ms ∧ h v = i

/-- The puzzle `(G, P)`, `P = {1, …, n}`, is **feasible** (p.8): every pair of configurations of
`P` on `G` is mutually reachable, i.e. for all configurations `f, g` there is a solution sequence
from `f` to `g`. -/
def IsFeasiblePuzzle (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ f g : V → Fin (n + 1), IsConfiguration f → IsConfiguration g →
    ∃ ms : List (V × V), IsSolutionSeq G f g ms

/-- An **instance of the Pebble Motion Problem on Trees** (Problem, pp.8–9) on the vertex set
`Fin N`: `G` is a tree with `N` vertices, `P = {1, …, n}` with `n ≤ N − 2`, `f` and `g` are
configurations of `P` on `G`, and `n + k(G) < N`. -/
def IsPMTInstance {N : ℕ} (G : SimpleGraph (Fin N)) (n : ℕ) (f g : Fin N → Fin (n + 1)) : Prop :=
  G.IsTree ∧ n + 2 ≤ N ∧ IsConfiguration f ∧ IsConfiguration g ∧ n + maxIsthmusSize G < N

end PebbleMotion.Trees


