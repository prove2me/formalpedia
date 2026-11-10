-- Prove2me | Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Graphs
-- name    : QuantumBipartiteTesting_Bipartiteness_Graphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T06:06:09.502995+00:00
-- url     : https://prove2.me/theorems/473bfe3b-2ee7-41aa-aefa-cf07a3051ce0
-- title:
--   Simple bounded-degree graphs, edit distance, and adjacency representations
-- statement:
--   A graph on $N$ labeled vertices is a finite set of unordered distinct vertex pairs. Bipartiteness means that some two-coloring assigns different colors to every edge. The degree bound is computed from the actual neighbor sets. A packed adjacency representation enumerates each neighbor once in any order and returns null precisely beyond the degree.
--
--   The edit distance is the minimum number of edge additions and deletions over actual bipartite graphs on the same vertex set. Farness means
--   $$\operatorname{dist}(G,\mathrm{BIP})\ge\varepsilon Nd.$$
--   Deletion distance is defined separately. Both minimizations have the empty target as a witness. The lower-bound scale uses the natural logarithm; it is used only eventually for $N\ge2$.
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), §2.1.1 and Definitions 2.1–2.3, PDF = printed page 8–9. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf

import Mathlib

namespace QuantumBipartiteTesting.Bipartiteness
open Finset
noncomputable section

/-- Simple graphs encoded by unordered pairs, oriented by the order on Fin N. -/
abbrev Edge (N : ℕ) := Fin N × Fin N

def IsGraph {N : ℕ} (G : Finset (Edge N)) : Prop :=
  ∀ e ∈ G, e.1 < e.2

def Bipartite {N : ℕ} (G : Finset (Edge N)) : Prop :=
  ∃ x : Fin N → Bool, ∀ e ∈ G, x e.1 ≠ x e.2

def Neighbors {N : ℕ} (G : Finset (Edge N)) (u : Fin N) : Finset (Fin N) :=
  univ.filter fun v => (u, v) ∈ G ∨ (v, u) ∈ G

def DegreeBound {N : ℕ} (d : ℕ) (G : Finset (Edge N)) : Prop :=
  ∀ u, (Neighbors G u).card ≤ d

/-- Minimum over actual same-vertex-set bipartite target graphs. -/
def EditDistance {N : ℕ} (G : Finset (Edge N)) : ℕ :=
  sInf {k | ∃ T : Finset (Edge N), IsGraph T ∧ Bipartite T ∧
    k = (G \ T).card + (T \ G).card}

def DeletionDistance {N : ℕ} (G : Finset (Edge N)) : ℕ :=
  sInf {k | ∃ T ⊆ G, Bipartite T ∧ k = (G \ T).card}

def Far {N : ℕ} (d : ℕ) (ε : ℝ) (G : Finset (Edge N)) : Prop :=
  ε * N * d ≤ (EditDistance G : ℝ)

/-- Packed adjacency lists; order is arbitrary and is part of the representation. -/
def Represents {N d : ℕ} (G : Finset (Edge N))
    (O : Fin N × Fin d → Option (Fin N)) : Prop :=
  (∀ u v, (∃ i, O (u,i) = some v) ↔ v ∈ Neighbors G u) ∧
  (∀ u i j v, O (u,i) = some v → O (u,j) = some v → i = j) ∧
  (∀ u i, O (u,i) = none ↔ (Neighbors G u).card ≤ i.val)

/-- Empty targets witness nonemptiness of both distance minimizations, even at N=0. -/
def LowerBoundScale (N : ℕ) : ℝ := (N : ℝ) ^ (1 / 3 : ℝ) / Real.log N

def DegreeScale (q : ℕ) : ℝ := 1 + q * Real.log (q + 2)

end
end QuantumBipartiteTesting.Bipartiteness


