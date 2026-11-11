-- Prove2me | Definitions.Def_TurnstileCutSparsify_Main_Graph
-- name    : TurnstileCutSparsify_Main_Graph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:38:24.802423+00:00
-- url     : https://prove2.me/theorems/7af90dcc-c26d-4f3f-b571-2bdd76baf00a
-- title:
--   Weighted graphs on [n], cut weights, connectivities λ_e, (1 ± ε)-cut sparsifiers and positive reweightings (§2, Definition 2.1, (1))
-- statement:
--   The vertex set is $V=[n]$ and the $N=\binom n2$ coordinates are the unordered vertex pairs $e=\{u,v\}$, $u<v$. A graph is a nonnegative weight vector $x$ on the pairs; its edges are the pairs with $x_e>0$. For $S\subseteq V$ the **cut weight** is
--   $$x(S,V\setminus S)=\sum_{e:\ |e\cap S|=1}x_e ,$$
--   summed over all pairs crossing $S$, and $E(S,V\setminus S)$ is the set of edges crossing $S$. The **connectivity** of a pair $e=uv$ is $\lambda_e(x)=\min_{S:\,u\in S,\,v\notin S}x(S,V\setminus S)$ (1); it is defined for every pair, including pairs of weight zero.
--
--   **Definition 2.1.** For $0<\varepsilon<1$, $H$ is a $(1\pm\varepsilon)$-cut sparsifier of $G$ if $(1-\varepsilon)w(S,V\setminus S)\le w_H(S,V\setminus S)\le(1+\varepsilon)w(S,V\setminus S)$ for **every** $S\subseteq V$. More generally $H$ approximates every cut of $x$ within $[\mathrm{lo},\mathrm{hi}]$ when $\mathrm{lo}\cdot x(S,V\setminus S)\le w_H(S,V\setminus S)\le \mathrm{hi}\cdot x(S,V\setminus S)$ for every $S$. A **positive reweighting of edges of $G$** is a graph $H$ on $V$ with $E(H)\subseteq E$ and positive weights. A graph is connected when the simple graph of its edges is. Probabilities over a finite set of random choices are taken under the uniform distribution.
--
--   **Formalization Note** Vertices are `Fin n` (0-based); `Pair n` is the subtype of `(u, v)` with `u < v`; `cut x S` sums `x e` over the pairs with exactly one endpoint in `S`; `connV x u v` is the minimum (`Finset.inf'` over the nonempty set of separating `S`); `conn x e = connV x e.lo e.hi`; `ApproxCuts lo hi x y` and `IsCutSparsifier ε x y` quantify over all `S : Finset (Fin n)`; `IsPosReweighting x y`: every pair with `y e ≠ 0` has `y e > 0` and `x e > 0`; `supportGraph x` is the simple graph of the edges; `prob E` and `expect f` are the uniform probability and expectation on a finite type.
-- source:
--   Lin, Mirrokni, Woodruff (2026), Near-Optimal Space and Time Cut Sparsification in Turnstile Streams, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), §2 p. 9, Definition 2.1 and (1) p. 10

import Mathlib

open scoped BigOperators Classical

noncomputable section

namespace TurnstileCutSparsify.Main

/-!
# Weighted graphs on `[n]`, cuts, connectivities and cut sparsifiers (§2, Definition 2.1, (1))

Lin, Mirrokni, Woodruff, *Near-Optimal Space and Time Cut Sparsification in Turnstile Streams*,
arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), §2 p. 9, Definition 2.1 and
(1) p. 10.

* The vertex set is `V = Fin n` (the paper's `[n]`, shifted to start at `0`).
* `Pair n` is the set of the `N = C(n, 2)` unordered vertex pairs, each written once as `(u, v)`
  with `u < v`. A weight vector (a graph) is a function `x : Pair n → ℝ`; the pair `e` is an edge
  of `x` when `x e > 0`.
* `crosses S e`: exactly one endpoint of `e` lies in `S`, i.e. `|e ∩ S| = 1`.
* `cut x S = x(S, V \ S)`: the total weight of the pairs crossing `S`, summed over all pairs
  (pairs of weight zero contribute nothing).
* `connV x u v = λ_x(u, v) = min {x(S, V \ S) : u ∈ S, v ∉ S}` for `u ≠ v`, and `conn x e` is the
  connectivity `λ_e(x)` of a pair (1), defined for every pair, including pairs of weight zero.
* `ApproxCuts lo hi x y`: `lo · x(S, V \ S) ≤ y(S, V \ S) ≤ hi · x(S, V \ S)` for **every**
  `S ⊆ V`, including `∅` and `V`. `IsCutSparsifier ε x y` is Definition 2.1 with `lo = 1 − ε`,
  `hi = 1 + ε`.
* `IsPosReweighting x y`: every pair carrying nonzero weight in `y` carries positive weight in `y`
  and is an edge of `x` (the paper's "positive reweighting of edges of `G`": `E(H) ⊆ E` with positive
  weights).
* `supportGraph x` is the simple graph of the edges of `x`; `x` is connected when it is.
* `prob E` is the probability of the event `E` under the uniform distribution on a finite,
  nonempty type, and `expect f` the expectation of `f`.
-/

/-- The unordered pairs of distinct vertices of `[n]`, written `(u, v)` with `u < v`. -/
abbrev Pair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

variable {n : ℕ}

/-- The smaller endpoint `min e`. -/
def Pair.lo (e : Pair n) : Fin n := e.1.1

/-- The larger endpoint `max e`. -/
def Pair.hi (e : Pair n) : Fin n := e.1.2

/-- The pair `{u, v}` of two distinct vertices. -/
def Pair.of (u v : Fin n) (h : u ≠ v) : Pair n :=
  if h' : u < v then ⟨(u, v), h'⟩ else ⟨(v, u), lt_of_le_of_ne (not_lt.1 h') (Ne.symm h)⟩

/-- `|e ∩ S| = 1`: exactly one endpoint of `e` lies in `S`. -/
def crosses (S : Finset (Fin n)) (e : Pair n) : Prop :=
  (e.lo ∈ S ∧ e.hi ∉ S) ∨ (e.lo ∉ S ∧ e.hi ∈ S)

/-- The cut weight `x(S, V \ S)`, summed over all pairs crossing `S`. -/
def cut (x : Pair n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ e, if crosses S e then x e else 0

/-- The edges of `x` crossing `S`: `E(S, V \ S)` for the graph `x`. -/
def cutEdges (x : Pair n → ℝ) (S : Finset (Fin n)) : Finset (Pair n) :=
  Finset.univ.filter fun e => crosses S e ∧ 0 < x e

/-- The connectivity `λ_x(u, v) = min_{S : u ∈ S, v ∉ S} x(S, V \ S)` of two distinct vertices
(value `0` when `u = v`, a case never used). -/
def connV (x : Pair n → ℝ) (u v : Fin n) : ℝ :=
  if h : u = v then 0 else
    ((Finset.univ : Finset (Finset (Fin n))).filter fun S => u ∈ S ∧ v ∉ S).inf'
      ⟨{u}, by simp [Finset.mem_filter, Finset.mem_singleton, Ne.symm h]⟩ (cut x)

/-- The connectivity `λ_e(x)` of a pair `e` (1). -/
def conn (x : Pair n → ℝ) (e : Pair n) : ℝ := connV x e.lo e.hi

/-- `lo · x(S, V \ S) ≤ y(S, V \ S) ≤ hi · x(S, V \ S)` for every `S ⊆ V`. -/
def ApproxCuts (lo hi : ℝ) (x y : Pair n → ℝ) : Prop :=
  ∀ S : Finset (Fin n), lo * cut x S ≤ cut y S ∧ cut y S ≤ hi * cut x S

/-- Definition 2.1: `y` is a `(1 ± ε)`-cut sparsifier of `x`. -/
def IsCutSparsifier (ε : ℝ) (x y : Pair n → ℝ) : Prop := ApproxCuts (1 - ε) (1 + ε) x y

/-- `y` is a positive reweighting of edges of `x`: `E(y) ⊆ E(x)` and every weight of `y` is
positive. -/
def IsPosReweighting (x y : Pair n → ℝ) : Prop := ∀ e, y e ≠ 0 → 0 < y e ∧ 0 < x e

/-- The number of edges of `y`. -/
def edgeCount (y : Pair n → ℝ) : ℕ := (Finset.univ.filter fun e => y e ≠ 0).card

/-- The simple graph on `[n]` whose edges are the pairs of positive weight: `u ~ v` iff `u ≠ v`
and the pair `{u, v}` has positive weight. -/
def supportGraph (x : Pair n → ℝ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => ∃ e : Pair n, 0 < x e ∧ e.lo = u ∧ e.hi = v

/-- A nonnegative integer weight vector, as a real one. -/
def toR (x : Pair n → ℕ) : Pair n → ℝ := fun e => (x e : ℝ)

/-- The probability of an event under the uniform distribution on a finite type. -/
def prob {Ω : Type*} [Fintype Ω] (E : Ω → Prop) : ℝ :=
  ((Finset.univ.filter E).card : ℝ) / (Fintype.card Ω : ℝ)

/-- The expectation of `f` under the uniform distribution on a finite type. -/
def expect {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / (Fintype.card Ω : ℝ)

end TurnstileCutSparsify.Main


