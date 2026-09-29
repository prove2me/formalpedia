-- Prove2me | Definitions.Def_FourToOneGames_Hypergraph
-- name    : FourToOneGames_Hypergraph
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-14T23:01:25.010145+00:00
-- url     : https://prove2.me/theorems/9db7a403-0266-4ebc-8200-e48c460f80f6
-- title:
--   3-uniform hypergraphs, colourings, and monochromatic fraction
-- statement:
--   A **3-uniform hypergraph** $H$ on the vertex set $[n]$ is a finite collection of edges, each of which is a set of exactly three vertices.
--
--   An edge is **monochromatic** under a colouring $\chi : [n] \to [c]$ if all its vertices receive the same colour; $\chi$ is a **proper $c$-colouring** if no edge is monochromatic, and $H$ is **$c$-colourable** if a proper $c$-colouring exists. The **monochromatic fraction** of $\chi$ is the fraction of edges of $H$ that are monochromatic under $\chi$, and $H$ has the property $\mathrm{AllColoringsMono}(c,\varepsilon)$ when every $c$-colouring of $H$ leaves at least an $\varepsilon$ fraction of the edges monochromatic.
--
--   A hypergraph is encoded in binary by the number of vertices in unary followed by one bit per ordered triple of vertices saying whether that triple is an edge.
-- source:
--   Yumou Fei, Dor Minzer, Shuo Wang, "On the Hardness of 4-to-1 Games with Perfect Completeness", ECCC Report No. TR26-179 (2026), https://eccc.weizmann.ac.il/report/2026/179/, p. 15, Theorem 3.1 (statement of the promise problem)

import Mathlib

/-!
# 3-uniform hypergraphs and their colourings

Objects used in the approximate hypergraph colouring hardness result (Theorem 3.1 of
Fei–Minzer–Wang, *On the Hardness of 4-to-1 Games with Perfect Completeness*, ECCC TR26-179)
and in the outer PCP of that paper.
-/

namespace FourToOneGames

/-- A finite 3-uniform hypergraph on the vertex set `Fin n`: a finite collection of edges,
each of which is a set of exactly three vertices. -/
structure Hypergraph3 where
  /-- Number of vertices. -/
  n : ℕ
  /-- The edges, each of cardinality three. -/
  edges : Finset (Finset (Fin n))
  /-- Every edge has exactly three vertices. -/
  card_edge : ∀ e ∈ edges, e.card = 3

namespace Hypergraph3

/-- An edge `e` is monochromatic under the colouring `χ` if all its vertices get the same
colour. -/
def Monochromatic {c : ℕ} (H : Hypergraph3) (χ : Fin H.n → Fin c) (e : Finset (Fin H.n)) :
    Prop := ∀ u ∈ e, ∀ v ∈ e, χ u = χ v

/-- `χ` is a proper `c`-colouring of `H`: no edge is monochromatic. -/
def IsProperColoring {c : ℕ} (H : Hypergraph3) (χ : Fin H.n → Fin c) : Prop :=
  ∀ e ∈ H.edges, ¬ H.Monochromatic χ e

/-- `H` is `c`-colourable. -/
def Colorable (H : Hypergraph3) (c : ℕ) : Prop := ∃ χ : Fin H.n → Fin c, H.IsProperColoring χ

/-- The fraction of edges of `H` that are monochromatic under the colouring `χ`. -/
noncomputable def monoFraction {c : ℕ} (H : Hypergraph3) (χ : Fin H.n → Fin c) : ℝ :=
  letI := Classical.decPred fun e : Finset (Fin H.n) => H.Monochromatic χ e
  ((H.edges.filter fun e => H.Monochromatic χ e).card : ℝ) / (H.edges.card : ℝ)

/-- Every `c`-colouring of `H` leaves at least an `ε` fraction of the edges monochromatic. -/
def AllColoringsMono (H : Hypergraph3) (c : ℕ) (ε : ℝ) : Prop :=
  ∀ χ : Fin H.n → Fin c, ε ≤ H.monoFraction χ

end Hypergraph3

/-- A binary encoding of a 3-uniform hypergraph: the number of vertices in unary, followed by
one bit for each triple of vertices (in lexicographic order) telling whether it is an edge. -/
def encodeHypergraph3 (H : Hypergraph3) : List Bool :=
  List.replicate H.n true ++ [false] ++
    ((List.finRange H.n).flatMap fun u =>
      (List.finRange H.n).flatMap fun v =>
        (List.finRange H.n).map fun w => decide (({u, v, w} : Finset (Fin H.n)) ∈ H.edges))

end FourToOneGames


