-- Prove2me | Definitions.Def_ChinesePostman_Polyhedron_Setting
-- name    : ChinesePostman_Polyhedron_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:24:23.537419+00:00
-- url     : https://prove2.me/theorems/cc0be2cd-0f9e-4fcb-b4d8-584fd39e54ce
-- title:
--   §2–§3, pp. 89–94 — multigraphs, odd nodes, odd sets, 'e meets S', parity points (3.1), (3.2), (3.6), the postman polyhedron (3.2), (3.5) and its dual (3.7)–(3.9)
-- statement:
--   This file fixes the objects of §2–§3 of Edmonds and Johnson (1973).
--
--   1. A **graph** $G$ consists of a finite set $N$ of nodes and a finite set $E$ of edges; each edge meets two *different* nodes, and several edges may meet the same pair of nodes (parallel edges are allowed, loops are not).
--   2. The **degree** of a node $n$ is the number of edges meeting $n$, that is $\sum_{e\in E} a_{ne}$ where $a_{ne}=1$ if $e$ meets $n$ and $0$ otherwise. Put $b_n = 1$ if the degree of $n$ is odd (then $n$ is an **odd node**) and $b_n = 0$ otherwise (an **even node**).
--   3. An edge $e$ **meets** a set $S\subseteq N$ when it meets exactly one node in $S$ and one node not in $S$. A set $S\subseteq N$ is an **odd set** when it contains an odd number of odd nodes (and any number of even nodes).
--   4. The **parity points** are the vectors $x\in\mathbb R^E$ satisfying
--   $$x_e\in\mathbb Z,\quad x_e\ge 0\ (e\in E),\qquad \sum_{e\in E} a_{ne}x_e \equiv b_n \pmod 2\ (n\in N),$$
--   that is (3.1), (3.2) and (3.6).
--   5. The **postman polyhedron** is the set of $x\in\mathbb R^E$ with
--   $$x_e\ge 0\ (e\in E),\qquad \sum\{x_e : e \text{ meets } S\}\ge 1\ \text{ for every odd set } S,$$
--   that is (3.2) and (3.5).
--   6. For a length vector $c\in\mathbb R^E$, the objective is $z=\sum_e c_e x_e$ (3.4). The **dual problem** has a variable $y_S$ for each odd set $S$, with constraints $y_S\ge 0$ (3.7) and $\sum\{y_S : e \text{ meets } S\}\le c_e$ for every edge $e$ (3.8), and objective $v=\sum\{y_S : S \text{ odd}\}$ (3.9).
--   7. For the version with the variables $w_n$ of p. 91: the integer points $(x,w)\in\mathbb Z^E\times\mathbb Z^N$ with $x\ge 0$, $w\ge 0$ and $\sum_e a_{ne}x_e-2w_n=b_n$ for all $n$ ((3.1), (3.1′), (3.2), (3.2′), (3.3)), and the polyhedron of real $(x,w)$ satisfying (3.2), (3.2′), (3.3) and (3.5).
--
--   These are the objects of the polyhedral description of the Chinese postman problem: the parity points are the extra traversals $x_e$ of a postman tour, and the postman polyhedron is their claimed convex hull.
--
--   **Formalization Note** The graph is a local `Graph` with a map `ends : E → Sym2 V` and a proof that no edge is a loop, over finite types of nodes and edges; parallel edges are allowed. Integrality is built into the parity points: each is the real image of an integer vector, so the congruence (3.6) is taken in $\mathbb Z$. The dual variable is a function `y : Finset V → ℝ`; every sum over `y` and the sign condition (3.7) are restricted to the odd sets, so its values on other sets play no role. The degree, odd sets and $b_n$ are all computed from $G$; the set of odd nodes is never a free parameter.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), pp. 89–94, §2 (graph), §3 (3.1), (3.1′), (3.2), (3.2′), (3.3), (3.4), (3.5), (3.6), (3.7), (3.8), (3.9)

import Mathlib

namespace ChinesePostman.Polyhedron

open Classical

/-! The graph has finite node and edge types, with parallel edges allowed and loops excluded
(§2, p. 89; §3, p. 91). -/

/-- A graph with a separate identity for every edge, including parallel edges. -/
structure Graph (V E : Type) where
  ends : E → Sym2 V
  loopless : ∀ e, ¬ (ends e).IsDiag

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- p. 90: the degree of node `n`, the number of edges meeting `n` (`Σ_e a_ne`). -/
noncomputable def degree (G : Graph V E) (n : V) : ℕ :=
  (Finset.univ.filter (fun e => n ∈ G.ends e)).card

/-- p. 90: `b_n`, equal to `1` when node `n` has odd degree (an *odd node*) and `0` otherwise. -/
noncomputable def bParity (G : Graph V E) (n : V) : ℤ :=
  if Odd (degree G n) then 1 else 0

/-- p. 91: edge `e` *meets* the node set `S` when it meets exactly one node in `S` and one node
not in `S`. -/
def Meets (G : Graph V E) (e : E) (S : Finset V) : Prop :=
  ∃ u v, G.ends e = s(u, v) ∧ u ∈ S ∧ v ∉ S

/-- p. 91: `S` is an *odd set* when it contains an odd number of odd nodes (and any number of
even nodes). -/
def IsOddSet (G : Graph V E) (S : Finset V) : Prop :=
  Odd (S.filter (fun n => Odd (degree G n))).card

/-- p. 90: `Σ_{e ∈ E} a_ne x_e`, the sum of `x_e` over the edges meeting node `n`. -/
noncomputable def incidentSum {α : Type} [AddCommMonoid α] (G : Graph V E) (x : E → α) (n : V) :
    α :=
  ∑ e ∈ Finset.univ.filter (fun e => n ∈ G.ends e), x e

/-- p. 91, (3.5): `Σ{x_e : e meets S}`. -/
noncomputable def cutSum {α : Type} [AddCommMonoid α] (G : Graph V E) (x : E → α)
    (S : Finset V) : α :=
  ∑ e ∈ Finset.univ.filter (fun e => Meets G e S), x e

/-- p. 93: the real points `x` with integer coordinates satisfying (3.1) `x_e` integer,
(3.2) `x_e ≥ 0` and (3.6) `Σ_e a_ne x_e ≡ b_n (mod 2)` for every node `n`. -/
def parityPoints (G : Graph V E) : Set (E → ℝ) :=
  {x | ∃ z : E → ℤ, (∀ e, 0 ≤ z e) ∧ (∀ n, incidentSum G z n ≡ bParity G n [ZMOD 2]) ∧
    x = fun e => (z e : ℝ)}

/-- p. 94: the polyhedron of solutions to (3.2) `x_e ≥ 0` and (3.5)
`Σ{x_e : e meets S} ≥ 1` for every odd set `S`. -/
def postmanPolyhedron (G : Graph V E) : Set (E → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ ∀ S : Finset V, IsOddSet G S → 1 ≤ cutSum G x S}

/-- p. 94: the odd sets of `G`, which index the dual variables `y_S`. -/
noncomputable def oddSets (G : Graph V E) : Finset (Finset V) :=
  Finset.univ.filter (IsOddSet G)

/-- p. 94, (3.8): `Σ{y_S : S odd, e meets S}`. Only odd sets enter. -/
noncomputable def dualLoad (G : Graph V E) (y : Finset V → ℝ) (e : E) : ℝ :=
  ∑ S ∈ (oddSets G).filter (fun S => Meets G e S), y S

/-- p. 94, (3.9): the dual objective `v = Σ{y_S : S odd}`. -/
noncomputable def dualValue (G : Graph V E) (y : Finset V → ℝ) : ℝ :=
  ∑ S ∈ oddSets G, y S

/-- p. 94: `y` is feasible for the dual problem, (3.7) `y_S ≥ 0` for every odd set `S` and
(3.8) `Σ{y_S : e meets S} ≤ c_e` for every edge `e`. Values of `y` on non-odd sets are ignored. -/
def IsDualFeasible (G : Graph V E) (c : E → ℝ) (y : Finset V → ℝ) : Prop :=
  (∀ S ∈ oddSets G, 0 ≤ y S) ∧ ∀ e, dualLoad G y e ≤ c e

/-- (3.4): the objective `z = Σ_e c_e x_e`. -/
def objective (c x : E → ℝ) : ℝ :=
  ∑ e, c e * x e

/-- p. 91: the integer points `(x, w)` satisfying (3.1), (3.1′), (3.2), (3.2′) and (3.3)
`Σ_e a_ne x_e − 2 w_n = b_n`, read in `ℝ^E × ℝ^N`. -/
def wParityPoints (G : Graph V E) : Set ((E → ℝ) × (V → ℝ)) :=
  {p | ∃ z : E → ℤ, ∃ u : V → ℤ, (∀ e, 0 ≤ z e) ∧ (∀ n, 0 ≤ u n) ∧
    (∀ n, incidentSum G z n - 2 * u n = bParity G n) ∧
    p = (fun e => (z e : ℝ), fun n => (u n : ℝ))}

/-- p. 91: the Chinese postman polyhedron in `(x, w)`, the solutions to (3.2), (3.2′), (3.3) and
(3.5). -/
def wPostmanPolyhedron (G : Graph V E) : Set ((E → ℝ) × (V → ℝ)) :=
  {p | (∀ e, 0 ≤ p.1 e) ∧ (∀ n, 0 ≤ p.2 n) ∧
    (∀ n, incidentSum G p.1 n - 2 * p.2 n = (bParity G n : ℝ)) ∧
    ∀ S : Finset V, IsOddSet G S → 1 ≤ cutSum G p.1 S}

end ChinesePostman.Polyhedron


