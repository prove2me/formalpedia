-- Prove2me | Definitions.Def_SidB_graph
-- name    : SidB_graph
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-21T18:07:21.480175+00:00
-- url     : https://prove2.me/theorems/370ab450-5be0-4454-97c4-0850a54dc8de
-- title:
--   The graph layer: bigraphs, graphons, and the Sidorenko property
-- statement:
--   The graph layer of Conlon and Lee's "Sidorenko's Conjecture for Blow-ups" (Discrete Anal. 2021:2): the bipartite-graph and graphon interface of the paper. Bigraph A B is a Boolean adjacency structure; Bigraph.nbr H b is the neighbourhood of a right vertex, Bigraph.edgeCount H the number of edges (each counted through its right vertex), Bigraph.maxDeg H the maximum degree of a right vertex, and Bigraph.degCount H k the number of right vertices of degree exactly k, the degree profile d_k of the paper's Theorem 1.1. Graphon is the paper's graphon language turned into a finitary interface: a symmetric [0,1]-valued kernel W on an abstract domain, and an expectation operation exp on functionals (S -> dom) -> R for finite S, satisfying the normalization (exp_one), monotonicity (exp_mono), linearity (exp_linear), Fubini (exp_fubini), transport (exp_transport), and Hoelder AM-GM (exp_holder) axioms that Lebesgue integration against the uniform measure enjoys. Graphon.EX is the packaging of exp with the Fintype instance; Graphon.rho g F x is the paper's rho(x_F) = E_y prod_{i in F} W(x_i, y); Graphon.dens g H is the homomorphism density t_H(W) = E_{x_A} prod_{b in B} rho(x_{N(b)}); Graphon.edgeDens g is t_{K_2}(W). SatisfiesSidorenko H is the Sidorenko property itself: for every graphon, t_H(W) >= t_{K_2}(W) ^ e(H). Bigraph.blowUp H p is the blow-up (the p-th power) of H relative to A, each right vertex replaced by an independent set of order p. The three running examples close the layer: mobiusLadder, the Moebius ladder M = K_{5,5} minus its ten-cycle, on Z_5 and Z_5 with each right vertex adjacent to i-1, i, and i+1; mobiusSquare, its blow-up with p = 2; and incGraph53, the (5,3)-incidence graph between Fin 5 and its 3-subsets.
--
--   **Formalization Note** The expectation functional is the finitary idealization of Lebesgue integration: instead of measurable functions on [0,1]^S, the interface is an operation on functionals over finite S, with the axioms the paper's integrals enjoy. Constructing this interface for the Lebesgue graphons of the paper - and verifying the Hoelder axiom, the AM-GM inequality for the expectation - is part of the proposed work of the mission.
-- source:
--   D. Conlon, J. Lee, Sidorenko's conjecture for blow-ups, Discrete Anal. 2021:2 (2021), Section 1 (the graphon language of pages 3-4) and Section 2 (the Moebius ladder and the (5,3)-incidence graph).

import Mathlib

/-!
# The graph layer: bigraphs, graphons, and the Sidorenko property

The graph layer of the SidB mission, carrying the bipartite-graph and graphon
interface of David Conlon and Joonkyung Lee, "Sidorenko's Conjecture for
Blow-ups" (Discrete Anal. 2021:2): bigraphs as Boolean adjacency structures
with their neighbourhoods, edge counts, maximum degrees, and degree
profiles; the graphon interface as an abstract expectation functional, a
finitary idealization of Lebesgue integration against the uniform measure,
with the normalization, monotonicity, linearity, Fubini, transport, and
Hoelder axioms that the paper's integrals enjoy; the rho, density, and
edge-density functionals; the Sidorenko property itself; the blow-up
construction; and the three running examples: the Moebius ladder
M = K_{5,5} minus its ten-cycle, its square (the blow-up with p = 2), and
the (5,3)-incidence graph.
-/

namespace SidB

/-- A bipartite graph as a Boolean adjacency structure: a left part A, a
right part B, and the adjacency predicate from A to B. -/
structure Bigraph (A B : Type) where
  adj : A → B → Bool

/-- The neighbourhood of a right vertex b: the left vertices adjacent to b. -/
def Bigraph.nbr {A B : Type} [Fintype A] (H : Bigraph A B) (b : B) : Finset A :=
  Finset.univ.filter (fun a => H.adj a b)

/-- The number of edges of H, each counted through its right vertex. -/
def Bigraph.edgeCount {A B : Type} [Fintype A] [Fintype B] (H : Bigraph A B) : ℕ :=
  ∑ b : B, (H.nbr b).card

/-- The maximum degree of a right vertex of H. -/
def Bigraph.maxDeg {A B : Type} [Fintype A] [Fintype B] (H : Bigraph A B) : ℕ :=
  Finset.univ.sup (fun b => (H.nbr b).card)

/-- The number of right vertices of degree exactly k. -/
def Bigraph.degCount {A B : Type} [Fintype A] [Fintype B] (H : Bigraph A B) (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun b => (H.nbr b).card = k)).card

/-- A graphon as an abstract expectation functional: a symmetric [0,1]-valued
kernel W on an abstract domain, together with an expectation operation on
finitary functionals. The expectation is idealized finitarily: instead of
Lebesgue integration over [0,1]^S, it is an operation on functions
(S -> dom) -> R for finite S, satisfying the normalization, monotonicity,
linearity, Fubini, transport, and Hoelder (AM-GM) axioms that the paper's
integrals enjoy. Constructing this interface for the Lebesgue graphons of
the paper is part of the proposed work of the mission. -/
structure Graphon : Type 1 where
  dom : Type
  W : dom → dom → ℝ
  w_nonneg : ∀ x y : dom, 0 ≤ W x y
  w_symm : ∀ x y : dom, W x y = W y x
  w_le_one : ∀ x y : dom, W x y ≤ 1
  exp : (S : Type) → Fintype S → ((S → dom) → ℝ) → ℝ
  exp_one : ∀ (S : Type) (hS : Fintype S), exp S hS (fun _ => 1) = 1
  exp_mono : ∀ (S : Type) (hS : Fintype S) (f g : (S → dom) → ℝ),
      (∀ x, f x ≤ g x) → exp S hS f ≤ exp S hS g
  exp_linear : ∀ (S : Type) (hS : Fintype S) (a b : ℝ) (f g : (S → dom) → ℝ),
      exp S hS (fun x => a * f x + b * g x) = a * exp S hS f + b * exp S hS g
  exp_fubini : ∀ (S T : Type) (hS : Fintype S) (hT : Fintype T) (hST : Fintype (S ⊕ T))
      (F : ((S ⊕ T) → dom) → ℝ),
      exp (S ⊕ T) hST F = exp S hS (fun x => exp T hT (fun y => F (Sum.elim x y)))
  exp_transport : ∀ (S T : Type) (hS : Fintype S) (hT : Fintype T) (e : S ≃ T)
      (f : (T → dom) → ℝ),
      exp S hS (fun x => f (fun t => x (e.symm t))) = exp T hT f
  exp_holder : ∀ (S : Type) (hS : Fintype S) (J : Type) (_hJ : Fintype J)
      (f : J → ((S → dom) → ℝ)),
      (∀ j x, 0 ≤ f j x) → 0 < Fintype.card J →
      exp S hS (fun x => ∏ j : J, f j x) ≤
        ∏ j : J, (exp S hS (fun x => f j x ^ (Fintype.card J : ℝ)))
          ^ (1 / (Fintype.card J : ℝ))

/-- The expectation of a finitary functional over S, packaged with the
Fintype instance so that it can be applied uniformly. -/
def Graphon.EX (g : Graphon) (S : Type) [hS : Fintype S] : ((S → g.dom) → ℝ) → ℝ :=
  g.exp S hS

/-- The rho functional of the paper: the expected common-neighbourhood
weight of the finite set F of left vertices,
rho(x_F) = E_y prod_{i in F} W(x_i, y). -/
def Graphon.rho (g : Graphon) {A : Type} (F : Finset A) (x : A → g.dom) : ℝ :=
  g.EX Unit (fun u => ∏ i ∈ F, g.W (x i) (u ()))

/-- The homomorphism density of the bigraph H in the graphon g, in the
paper's form t_H(W) = E_{x_A} prod_{b in B} rho(x_{N(b)}). -/
def Graphon.dens (g : Graphon) {A B : Type} [Fintype A] [Fintype B] (H : Bigraph A B) : ℝ :=
  g.EX A (fun x => ∏ b : B, g.rho (H.nbr b) x)

/-- The edge density t_{K_2}(g) = E W(x, y). -/
def Graphon.edgeDens (g : Graphon) : ℝ :=
  g.EX Bool (fun b => g.W (b true) (b false))

/-- The Sidorenko property for H: for every graphon, the homomorphism
density of H is at least the edge density to the power of the edge count. -/
def SatisfiesSidorenko {A B : Type} [Fintype A] [Fintype B] (H : Bigraph A B) : Prop :=
  ∀ g : Graphon, g.edgeDens ^ (H.edgeCount : ℝ) ≤ g.dens H

/-- The blow-up (the p-th power) of H relative to A: each right vertex is
replaced by an independent set of order p, and every left vertex adjacent
to b becomes adjacent to all p copies. -/
def Bigraph.blowUp {A B : Type} (H : Bigraph A B) (p : ℕ) : Bigraph A (B × Fin p) where
  adj a bp := H.adj a bp.1

/-- The Moebius ladder M = K_{5,5} minus its ten-cycle, on two copies of
Z_5: the right vertex i is adjacent to i - 1, i, and i + 1 on the left. -/
def mobiusLadder : Bigraph (Fin 5) (Fin 5) where
  adj a b := decide ((a.val + 1) % 5 = b.val ∨ a.val = b.val ∨ (a.val + 4) % 5 = b.val)

/-- The square of the Moebius ladder: its blow-up with p = 2. -/
def mobiusSquare : Bigraph (Fin 5) (Fin 5 × Fin 2) :=
  mobiusLadder.blowUp 2

/-- The (5,3)-incidence graph: the membership bigraph between Fin 5 and
the 3-subsets of Fin 5. -/
def incGraph53 : Bigraph (Fin 5) {s : Finset (Fin 5) // s.card = 3} where
  adj a s := decide (a ∈ s.1)

end SidB


