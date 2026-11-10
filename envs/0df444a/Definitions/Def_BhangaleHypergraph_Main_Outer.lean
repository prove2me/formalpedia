-- Prove2me | Definitions.Def_BhangaleHypergraph_Main_Outer
-- name    : BhangaleHypergraph_Main_Outer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:05:57.175466+00:00
-- url     : https://prove2.me/theorems/040d4fba-2b92-4025-ad76-8c951fac4ddb
-- title:
--   Multilayer occurrences, chain laws and inverse-image closed domains
-- statement:
--   A layered instance assigns each vertex a layer and a positive, vertex-dependent alphabet. Every indexed constraint occurrence points to a later layer and carries a total projection. A chain chooses one vertex per layer and an existing occurrence for every pair of layers. An outer instance carries nonnegative real masses on these chains summing to one. Its pairwise value is the acceptance probability under the corresponding marginal, and pairwise soundness bounds this value for every labeling and every forward pair.
--
--   For every variable $x$, the closed domain is exactly
--   $$W_x=\bigcup_{P:x\leadsto y}\{\pi_P^{-1}(A):A\in U_{C,s}([R_y])\},$$
--   including the empty path. Maximum alphabet size and maximum outdegree count the raw vertices and occurrences. The maximum of an empty finite family is set to zero; assertions indexed by its vertices then have no instances.
--
--   This interface separates finite raw data from the chosen probability law. Neither satisfiability nor soundness is bundled as a property of an input instance.
-- source:
--   Amey Bhangale, STOC 2027 submission #1052 (October 2026), §3.1 and Definition 3.1, pp. 14–15 (printed pages = PDF pages); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1052.pdf

import Mathlib
import Definitions.Def_BhangaleHypergraph_Main_Restricted

namespace BhangaleHypergraph.Main

/-- Raw finite multilayer constraint occurrences; no soundness or satisfiability is bundled. -/
structure Layered where
  n : ℕ
  layers : ℕ
  layer : Fin n → Fin layers
  R : Fin n → ℕ
  positive : ∀ x, 0 < R x
  edges : ℕ
  src : Fin edges → Fin n
  dst : Fin edges → Fin n
  forward : ∀ e, layer (src e) < layer (dst e)
  proj : (e : Fin edges) → Fin (R (src e)) → Fin (R (dst e))

abbrev Labeling (G : Layered) := (x : Fin G.n) → Fin (G.R x)

def Satisfiable (G : Layered) : Prop :=
  ∃ σ : Labeling G, ∀ e, G.proj e (σ (G.src e)) = σ (G.dst e)

/-- A chain contains an existing occurrence for every ordered pair of layers. -/
structure Chain (G : Layered) where
  vertex : Fin G.layers → Fin G.n
  at_layer : ∀ i, G.layer (vertex i) = i
  edge : (i j : Fin G.layers) → i < j → Fin G.edges
  source : ∀ i j h, G.src (edge i j h) = vertex i
  target : ∀ i j h, G.dst (edge i j h) = vertex j

instance (G : Layered) : Finite (Chain G) := by
  let f (c : Chain G) := (c.vertex, c.edge)
  exact Finite.of_injective f (by
    intro a b h
    cases a; cases b
    simp_all [f])

noncomputable instance (G : Layered) : Fintype (Chain G) := Fintype.ofFinite _

/-- An arbitrary actual law on finite chains, not a law on distinct endpoint pairs. -/
structure Outer extends Layered where
  mass : Chain toLayered → ℝ
  nonneg : ∀ c, 0 ≤ mass c
  total : ∑ c, mass c = 1

noncomputable def PairValue (G : Outer) (σ : Labeling G.toLayered)
    (i j : Fin G.layers) (h : i < j) : ℝ := by
  classical
  exact ∑ c : Chain G.toLayered, G.mass c *
    if G.proj (c.edge i j h) (σ (G.src (c.edge i j h))) =
      σ (G.dst (c.edge i j h)) then 1 else 0

def PairwiseSound (G : Outer) (ε : ℝ) : Prop :=
  ∀ (σ : Labeling G.toLayered) (i j : Fin G.layers) (h : i < j), PairValue G σ i j h ≤ ε

inductive DirectedPath (G : Layered) : Fin G.n → Fin G.n → Type
  | nil (x) : DirectedPath G x x
  | cons (e : Fin G.edges) {z} (p : DirectedPath G (G.dst e) z) :
      DirectedPath G (G.src e) z

def DirectedPath.projection {G : Layered} {x y : Fin G.n} :
    DirectedPath G x y → Fin (G.R x) → Fin (G.R y)
  | .nil _, a => a
  | .cons e p, a => p.projection (G.proj e a)

/-- Exactly the union over all paths, including the length-zero path. -/
noncomputable def Closed (G : Layered) (C s : ℕ) (x : Fin G.n) :
    Finset (Finset (Fin (G.R x))) := by
  classical
  exact Finset.univ.filter fun X => ∃ (y : Fin G.n) (p : DirectedPath G x y)
    (A : Finset (Fin (G.R y))), A ∈ Core C s (G.R y) ∧ X = Preimage p.projection A

noncomputable def MaxAlphabet (G : Layered) : ℕ := Finset.univ.sup G.R

noncomputable def MaxOutdegree (G : Layered) : ℕ := by
  classical
  exact Finset.univ.sup fun x => (Finset.univ.filter fun e => G.src e = x).card

end BhangaleHypergraph.Main


