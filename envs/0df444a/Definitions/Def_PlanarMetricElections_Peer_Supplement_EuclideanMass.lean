-- Prove2me | Definitions.Def_PlanarMetricElections_Peer_Supplement_EuclideanMass
-- name    : PlanarMetricElections_Peer_Supplement_EuclideanMass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:42:20.632558+00:00
-- url     : https://prove2.me/theorems/81ec189c-358a-4142-9d23-b20ba13219c4
-- title:
--   Euclidean space $\mathbb R^r$ and uniform mass of a finite point set
-- statement:
--   For a natural number $r$, $\mathbb R^r$ is Euclidean space with its $\ell_2$ distance. For a finite set $P\subseteq\mathbb R^r$ and any set $K\subseteq\mathbb R^r$, the uniform mass of $K$ with respect to $P$ is the fraction of points of $P$ lying in $K$:
--
--   $$\mu_P(K)=\frac{|K\cap P|}{|P|}.$$
--
--   This is the normalisation used both in the weak-net factor of equation (1) and in the vote shares of equation (2).
--
--   **Formalization Note** $\mathbb R^r$ is Mathlib's `EuclideanSpace ℝ (Fin r)`, whose `dist` is the Euclidean distance. Every use of $\mu_P$ in this mission has $P$ nonempty; for $P=\emptyset$ the Lean value is $0$.
-- source:
--   Gabriel Morete de Azevedo, Ulysse Hennebelle, STOC 2027 submission #1404 (October 2026), Section 2, equation (1), p. 4 (PDF p. 5)

import Mathlib

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace PlanarMetricElections.Peer.Supplement

/-- Euclidean space `ℝ^r`; its `dist` is the genuine ℓ₂ distance. -/
abbrev Euc (r : ℕ) := EuclideanSpace ℝ (Fin r)

/-- Uniform mass `|{p ∈ P : p ∈ K}| / |P|` of a set `K` with respect to a finite set `P ⊆ ℝ^r`.
Intended uses have `P` nonempty; the empty set gives mass `0`. -/
def euclidMass {r : ℕ} (P : Finset (Euc r)) (K : Set (Euc r)) : ℝ :=
  ((P.filter (fun p => p ∈ K)).card : ℝ) / (P.card : ℝ)

end PlanarMetricElections.Peer.Supplement


