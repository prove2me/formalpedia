-- Prove2me | Definitions.Def_SteinerNav_GreedyRun
-- name    : SteinerNav_GreedyRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:46:48.784001+00:00
-- url     : https://prove2.me/theorems/1be817df-49ed-4a22-be05-d24b04c9cbca
-- title:
--   Strict greedy descent on a directed graph, its runs, local minima and the return rule of Lemma 6.5
-- statement:
--   Let $E$ be a finite directed graph on points of $\mathbb R^d$ and $q\in\mathbb R^d$ a query.
--
--   1. **Greedy step.** From the current vertex $x$, the search may move to $y$ if $(x,y)\in E$, $y$ is an out-neighbor of $x$ closest to $q$, and $\|y-q\|<\|x-q\|$.
--   2. **Local minimum.** $x$ is a greedy local minimum for $q$ if no out-neighbor of $x$ is strictly closer to $q$ than $x$.
--   3. **Run.** A run of $k$ moves from $x_0$ is a sequence $x_0,x_1,\dots,x_k$ in which each $x_{i+1}$ is a greedy step from $x_i$. When several out-neighbors tie for closest, each choice gives a run.
--   4. **Return rule (Lemma 6.5).** At a final vertex $x$, return $x$ if $x\in P$; otherwise return an out-neighbor of $x$ closest to $q$.
--
--   This is the search procedure ("as long as an out-neighbor of the current vertex is closer to $q$ than the current vertex is, the search proceeds to the out-neighbor closest to $q$") whose guarantees the mission formalizes.
--
--   **Formalization Note** Runs are an inductive relation `GreedyRun E q x₀ k x` ("the search can be at $x$ after exactly $k$ moves"). The paper leaves ties unspecified, so statements quantify over every run, that is, over every tie-breaking. The return rule allows every closest out-neighbor.
-- source:
--   Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, Sparse α-Navigable Graphs in Euclidean Space via Steiner Points, STOC 2027 submission (manuscript sha256 e396eee6…), §1, p.2 (greedy search); §6.3, p.22 (strict greedy descent, local minimum, Lemma 6.5's return rule)

import Mathlib
import Definitions.Def_SteinerNav_Covers

namespace SteinerNav

/-- One move of strict greedy descent toward the query `q`: `y` is an out-neighbor of `x` closest to
`q`, and it is strictly closer to `q` than `x` is (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), §1, p.2, and §6.3, p.22).

**Formalization Note** The paper leaves ties unspecified, so a tie gives several possible moves. -/
def GreedyStep {d : ℕ} (E : Finset (Pt d × Pt d)) (q x y : Pt d) : Prop :=
  (x, y) ∈ E ∧ dist y q < dist x q ∧ ∀ z, (x, z) ∈ E → dist y q ≤ dist z q

/-- `x` is a greedy local minimum for `q`: no out-neighbor of `x` is strictly closer to `q`
(Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), §6.3, p.22). -/
def GreedyLocalMin {d : ℕ} (E : Finset (Pt d × Pt d)) (q x : Pt d) : Prop :=
  ∀ z, (x, z) ∈ E → dist x q ≤ dist z q

/-- `GreedyRun E q x₀ k x`: strict greedy descent toward `q`, started at `x₀`, can be at `x` after
exactly `k` moves, under some resolution of the ties (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), §1, p.2, and §6.3, p.22). -/
inductive GreedyRun {d : ℕ} (E : Finset (Pt d × Pt d)) (q x₀ : Pt d) : ℕ → Pt d → Prop
  | start : GreedyRun E q x₀ 0 x₀
  | step {k : ℕ} {x y : Pt d} :
      GreedyRun E q x₀ k x → GreedyStep E q x y → GreedyRun E q x₀ (k + 1) y

/-- The return rule of Lemma 6.5 at a final vertex `x`: return `x` if `x ∈ P`; otherwise return an
out-neighbor of `x` closest to `q` (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), Lemma 6.5, p.22).

**Formalization Note** Every closest out-neighbor is an allowed return value. -/
def GreedyReturns {d : ℕ} (E : Finset (Pt d × Pt d)) (P : Finset (Pt d)) (q x y : Pt d) : Prop :=
  (x ∈ P ∧ y = x) ∨ (x ∉ P ∧ (x, y) ∈ E ∧ ∀ z, (x, z) ∈ E → dist y q ≤ dist z q)

end SteinerNav


