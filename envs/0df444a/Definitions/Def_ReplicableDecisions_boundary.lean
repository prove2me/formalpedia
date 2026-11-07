-- Prove2me | Definitions.Def_ReplicableDecisions_boundary
-- name    : ReplicableDecisions_boundary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:01:20.782592+00:00
-- url     : https://prove2.me/theorems/bc46fd7f-14c7-4d64-af37-ce3d442165d5
-- title:
--   Selectors: boundary, bad set, everywhere and neighborhood correctness
-- statement:
--   For a graph $G$ on the models, $N_G[P]$ is the closed neighborhood of $P$. A **selector** is a map $f:\mathcal P\to\mathcal Y$. Its boundary and bad set are
--
--   $$
--   \partial_Gf=\{P:\text{there is }Q\in N_G[P]\text{ with }f(Q)\ne f(P)\},\qquad B_G(f)=\partial_Gf\cup\{P:f(P)\notin\Gamma(P)\}.
--   $$
--
--   The selector is **everywhere correct** if $f(P)\in\Gamma(P)$ for every $P$, and **neighborhood correct** if
--
--   $$
--   f(Q)\in\Gamma(P)\qquad(P\in\mathcal P,\ Q\in N_G[P]).
--   $$
--
--   A model is good for $f$ exactly when its entire neighborhood has one label acceptable at it. Selectors are the combinatorial form to which replicable algorithms reduce.
-- source:
--   Chen, Replicable Decisions in Finite Experiments, STOC 2027 submission (sha256 52d181db…), §2 "Selectors", (2.1), p.9 (PDF p.11)

import Mathlib

namespace ReplicableDecisions

/-- **The closed neighborhood** `N_G[P]`. Chen, *Replicable Decisions in Finite Experiments*, STOC
2027 submission (sha256 52d181db…), §2 "Selectors", p.9 (PDF p.11). -/
def closedNbhd {ι : Type*} (G : SimpleGraph ι) (i : ι) : Set ι :=
  {j | j = i ∨ G.Adj i j}

/-- **The boundary of a selector,** `∂_G f = {P : there is Q ∈ N_G[P] with f(Q) ≠ f(P)}`, for a
selector `f : P → Y`. Chen, STOC 2027 submission (sha256 52d181db…), §2, p.9 (PDF p.11). -/
def boundary {ι : Type*} {Y : Type*} (G : SimpleGraph ι) (f : ι → Y) : Set ι :=
  {i | ∃ j ∈ closedNbhd G i, f j ≠ f i}

/-- **The bad set,** `B_G(f) = ∂_G f ∪ {P : f(P) ∉ Γ(P)}`. Chen, STOC 2027 submission
(sha256 52d181db…), §2, p.9 (PDF p.11). -/
def badSet {ι : Type*} {Y : Type*} (G : SimpleGraph ι) (Γ : ι → Set Y) (f : ι → Y) : Set ι :=
  boundary G f ∪ {i | f i ∉ Γ i}

/-- **Everywhere-correct selectors:** `f(P) ∈ Γ(P)` for every `P`. Chen, STOC 2027 submission
(sha256 52d181db…), §2, p.9 (PDF p.11). -/
def EverywhereCorrect {ι : Type*} {Y : Type*} (Γ : ι → Set Y) (f : ι → Y) : Prop :=
  ∀ i, f i ∈ Γ i

/-- **Neighborhood-correct selectors,** (2.1): `f(Q) ∈ Γ(P)` for `P ∈ P`, `Q ∈ N_G[P]`. Chen, STOC
2027 submission (sha256 52d181db…), §2, (2.1), p.9 (PDF p.11). -/
def NeighborhoodCorrect {ι : Type*} {Y : Type*} (G : SimpleGraph ι) (Γ : ι → Set Y) (f : ι → Y) :
    Prop :=
  ∀ i, ∀ j ∈ closedNbhd G i, f j ∈ Γ i

end ReplicableDecisions


