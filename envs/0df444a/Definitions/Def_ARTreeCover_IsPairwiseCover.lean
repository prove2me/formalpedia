-- Prove2me | Definitions.Def_ARTreeCover_IsPairwiseCover
-- name    : ARTreeCover_IsPairwiseCover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:54:33.307193+00:00
-- url     : https://prove2.me/theorems/64166085-ca52-4ed9-a6b3-ad2d18f892a2
-- title:
--   Layered clusterings, $(\Delta,\alpha)$-pairwise covers and neighborhood covers
-- statement:
--   An **$s$-layered clustering** of $V$ is a list of $s$ partitions $\Pi_1,\dots,\Pi_s$ of $V$; its clusters are the parts of the $\Pi_i$. For $\Delta,\alpha>0$:
--
--   1. it is a strong (weak) **$(\Delta,\alpha)$-pairwise cover** if every cluster has strong (weak) radius at most $\alpha\Delta$, and every $u,v$ with $d_G(u,v)\le\Delta$ lie in a common cluster;
--   2. it is a strong (weak) **$(\Delta,\alpha)$-neighborhood cover** if every cluster has strong (weak) radius at most $\alpha\Delta$, and every ball $B_G(u,\Delta)=\{v: d_G(u,v)\le\Delta\}$ lies in one cluster.
--
--   A neighborhood cover is a pairwise cover, since $u,v\in B_G(u,\Delta)$ when $d_G(u,v)\le\Delta$.
--
--   **Formalization Note** A clustering with fewer distinct layers is also $s$-layered, by repeating a layer. Parts of a `Finpartition` are nonempty.
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 1, p.9 (PDF p.12); Definition 11, p.15 (PDF p.18)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_RadiusLE

open scoped ENNReal

namespace ARTreeCover

/-!
# Layered clusterings, neighborhood covers and pairwise covers

Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 1, p.9 (PDF p.12): "The clustering C
is called s-layered if C = Π1 ∪ Π2 ∪ · · · ∪ Πs, where {Πi} are partitions"; Definition 11, p.15
(PDF p.18): neighborhood and pairwise covers.

**Formalization Note.** An `s`-layered clustering is a family `Pi : Fin s → Finpartition univ` of
partitions of `V`; its clusters are the parts of the `Pi i`. Repetitions are allowed, so a clustering
with fewer than `s` distinct layers is also `s`-layered (pad by repeating a layer; for `s ≥ 1`).
Parts of a `Finpartition` are nonempty, as clusters of a partition are. The strong/weak radius is
`RadiusLE` with the flag `strong`.
-/

variable {V : Type} [DecidableEq V] [Fintype V] {s : ℕ}

/-- Every cluster of the layered clustering has strong (`strong = true`) or weak radius at most
`R`. -/
def LayeredRadiusLE (G : WGraph V) (strong : Bool)
    (Pi : Fin s → Finpartition (Finset.univ : Finset V)) (R : ℝ) : Prop :=
  ∀ i, ∀ C ∈ (Pi i).parts, RadiusLE G strong C R

/-- A strong (`strong = true`) or weak `(∆, α)`-pairwise cover (Definition 11): radius at most
`α∆`, and every `u, v` with `d_G(u, v) ≤ ∆` lie in a common cluster. -/
def IsPairwiseCover (G : WGraph V) (strong : Bool) (Δ α : ℝ)
    (Pi : Fin s → Finpartition (Finset.univ : Finset V)) : Prop :=
  LayeredRadiusLE G strong Pi (α * Δ) ∧
    ∀ u v, G.dist u v ≤ ENNReal.ofReal Δ → ∃ i, ∃ C ∈ (Pi i).parts, u ∈ C ∧ v ∈ C

/-- A strong (`strong = true`) or weak `(∆, α)`-neighborhood cover (Definition 11): radius at most
`α∆`, and every ball `B_G(u, ∆) = {v | d_G(u, v) ≤ ∆}` lies inside one cluster. -/
def IsNeighborhoodCover (G : WGraph V) (strong : Bool) (Δ α : ℝ)
    (Pi : Fin s → Finpartition (Finset.univ : Finset V)) : Prop :=
  LayeredRadiusLE G strong Pi (α * Δ) ∧
    ∀ u, ∃ i, ∃ C ∈ (Pi i).parts, ∀ v, G.dist u v ≤ ENNReal.ofReal Δ → v ∈ C

end ARTreeCover


