-- Prove2me | Definitions.Def_ARTreeCover_IsForestCover
-- name    : ARTreeCover_IsForestCover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:55:05.10187+00:00
-- url     : https://prove2.me/theorems/2a315742-eb7d-4978-9d0c-d5e528d4e62b
-- title:
--   Forest covers, stretch, scale-$\Delta$ and (almost-)Ramsey forest covers
-- statement:
--   Let $F_1,\dots,F_m$ be weighted forests on the vertex set of $G$.
--
--   1. They form a **forest cover** of $G$ if $d_G(u,v)\le d_{F_i}(u,v)$ for all $i,u,v$.
--   2. They have **stretch** at most $\alpha$ if for all $u,v$ there is $i$ with $d_{F_i}(u,v)\le\alpha\,d_G(u,v)$.
--   3. They have **scale-$\Delta$ stretch** $\alpha$ if $d_G(u,v)\le\Delta$ implies $d_{F_i}(u,v)\le\alpha\Delta$ for some $i$.
--   4. They are **Ramsey scale-$\Delta$** with stretch $\alpha$ if every $u$ has a home index $i$ with $d_{F_i}(u,v)\le\alpha\Delta$ for every $v$ with $d_G(u,v)\le\Delta$.
--   5. They are **almost-Ramsey** with stretch $\alpha$ if for every $u$ and every $\Delta>0$ there is a home index $i$ with $d_{F_i}(u,v)\le\alpha\Delta$ for every $v$ with $d_G(u,v)\le\Delta$.
--
--   The size of the cover is $m$. An almost-Ramsey cover gives each vertex one forest per scale that handles its whole ball at that scale, which is what the distance oracles and routing schemes of the paper consume.
--
--   **Formalization Note** A cover is a family indexed by `Fin m`, so repetitions are allowed and a cover of size at most $m$ is a family with some $m'\le m$. The bound $\alpha\,d_G(u,v)$ is $\infty$ when $d_G(u,v)=\infty$ and $\alpha>0$.
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Definitions 14, 16, 17, pp.28–30 (PDF pp.31–33)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_WForest

open scoped ENNReal

namespace ARTreeCover

/-!
# Forest covers, stretch, scale-∆ and (almost-)Ramsey forest covers

Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 14, pp.28–29 (PDF pp.31–32);
Definition 16, pp.29–30 (PDF pp.32–33); Definition 17, p.30 (PDF p.33).

**Formalization Note.** A cover of size `m` is a family `F : Fin m → WForest V` (repetitions allowed,
so "size at most m" is "some family indexed by `Fin m'` with `m' ≤ m`"). Distances are in `[0, ∞]`;
the stretch bound `α · d_G(u, v)` is `ENNReal.ofReal α * d_G(u, v)`, which is `∞` when
`d_G(u, v) = ∞` and `α > 0`. Scale bounds `α∆` are `ENNReal.ofReal (α * ∆)`. None of these predicates
asks `α ≥ 1`; the theorems state the paper's ranges.
-/

variable {V : Type} {m : ℕ}

/-- `F` is a forest cover of `G` (Definition 14): `d_G(u, v) ≤ min_F d_F(u, v)` for all `u, v`,
i.e. every forest dominates `G`. -/
def IsForestCover (G : WGraph V) (F : Fin m → WForest V) : Prop :=
  ∀ i u v, G.dist u v ≤ (F i).dist u v

/-- Stretch at most `α` (Definition 14): `min_F d_F(u, v) ≤ α · d_G(u, v)` for all `u, v`. -/
def ForestStretchLE (G : WGraph V) (F : Fin m → WForest V) (α : ℝ) : Prop :=
  ∀ u v, ∃ i, (F i).dist u v ≤ ENNReal.ofReal α * G.dist u v

/-- Scale-`∆` stretch `α` (Definition 16): if `d_G(u, v) ≤ ∆` then `min_F d_F(u, v) ≤ α∆`. -/
def ForestScaleLE (G : WGraph V) (F : Fin m → WForest V) (Δ α : ℝ) : Prop :=
  ∀ u v, G.dist u v ≤ ENNReal.ofReal Δ → ∃ i, (F i).dist u v ≤ ENNReal.ofReal (α * Δ)

/-- Ramsey scale-`∆` with stretch `α` (Definition 16): every `u` has a home forest `home(u)` with
`d_home(u)(u, v) ≤ α∆` for every `v` with `d_G(u, v) ≤ ∆`. -/
def ForestRamseyScale (G : WGraph V) (F : Fin m → WForest V) (Δ α : ℝ) : Prop :=
  ∀ u, ∃ i, ∀ v, G.dist u v ≤ ENNReal.ofReal Δ → (F i).dist u v ≤ ENNReal.ofReal (α * Δ)

/-- Almost-Ramsey with stretch `α` (Definition 17): for every `u ∈ V` and every `∆ > 0` there is a
home forest `home(u, ∆)` with `d_home(u,∆)(u, v) ≤ α∆` for every `v` with `d_G(u, v) ≤ ∆`. -/
def ForestAlmostRamsey (G : WGraph V) (F : Fin m → WForest V) (α : ℝ) : Prop :=
  ∀ u, ∀ Δ : ℝ, 0 < Δ → ∃ i, ∀ v, G.dist u v ≤ ENNReal.ofReal Δ →
    (F i).dist u v ≤ ENNReal.ofReal (α * Δ)

end ARTreeCover


