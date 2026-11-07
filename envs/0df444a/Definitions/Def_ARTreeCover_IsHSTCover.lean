-- Prove2me | Definitions.Def_ARTreeCover_IsHSTCover
-- name    : ARTreeCover_IsHSTCover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:53:35.596484+00:00
-- url     : https://prove2.me/theorems/3d87b607-0c3a-469e-b544-363eab08bb0b
-- title:
--   HST covers, stretch, scale-$\Delta$ and (almost-)Ramsey HST covers
-- statement:
--   Let $T_1,\dots,T_m$ be HSTs on the vertex set of $G$.
--
--   1. They form an **HST cover** of $G$ if $d_G(u,v)\le\rho_{T_i}(u,v)$ for all $i,u,v$.
--   2. They have **stretch** at most $\alpha$ if for all $u,v$ there is $i$ with $\rho_{T_i}(u,v)\le\alpha\,d_G(u,v)$.
--   3. They have **scale-$\Delta$ stretch** $\alpha$ if $d_G(u,v)\le\Delta$ implies $\rho_{T_i}(u,v)\le\alpha\Delta$ for some $i$.
--   4. They are **Ramsey scale-$\Delta$** with stretch $\alpha$ if every $u$ has a home index $i$ with $\rho_{T_i}(u,v)\le\alpha\Delta$ for every $v$ with $d_G(u,v)\le\Delta$.
--   5. They are **almost-Ramsey** with stretch $\alpha$ if for every $u$ and every $\Delta>0$ there is a home index $i$ with $\rho_{T_i}(u,v)\le\alpha\Delta$ for every $v$ with $d_G(u,v)\le\Delta$.
--
--   These are the exact analogues of the forest-cover notions, with the ultrametric $\rho_T$ in place of the forest distance.
--
--   **Formalization Note** Since $\rho_T=\infty$ off the leaves, domination is stated for all pairs of $V$, and a vertex with a home HST is a leaf of it.
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Definitions 15–17, pp.29–30 (PDF pp.32–33)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_HST

open scoped ENNReal

namespace ARTreeCover

/-!
# HST covers, stretch, scale-∆ and (almost-)Ramsey HST covers

Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 15, p.29 (PDF p.32);
Definition 16, pp.29–30 (PDF pp.32–33); Definition 17, p.30 (PDF p.33).

**Formalization Note.** A cover of size `m` is a family `H : Fin m → HST V`. `ρ_T` is `∞` off the
leaves of `T` (see `HST`), so domination "`d_G ≤ min_T ρ_T`" is stated for every pair of `V`.
Stretch and scale bounds are as for forest covers (`IsForestCover`).
-/

variable {V : Type} {m : ℕ}

/-- `H` is an HST cover of `G` (Definition 15): `d_G(u, v) ≤ min_T ρ_T(u, v)` for all `u, v`. -/
def IsHSTCover (G : WGraph V) (H : Fin m → HST V) : Prop :=
  ∀ i u v, G.dist u v ≤ (H i).ρ u v

/-- Stretch at most `α` (Definition 15): `min_T ρ_T(u, v) ≤ α · d_G(u, v)` for all `u, v`. -/
def HSTStretchLE (G : WGraph V) (H : Fin m → HST V) (α : ℝ) : Prop :=
  ∀ u v, ∃ i, (H i).ρ u v ≤ ENNReal.ofReal α * G.dist u v

/-- Scale-`∆` stretch `α` (Definition 16): if `d_G(u, v) ≤ ∆` then `min_T ρ_T(u, v) ≤ α∆`. -/
def HSTScaleLE (G : WGraph V) (H : Fin m → HST V) (Δ α : ℝ) : Prop :=
  ∀ u v, G.dist u v ≤ ENNReal.ofReal Δ → ∃ i, (H i).ρ u v ≤ ENNReal.ofReal (α * Δ)

/-- Ramsey scale-`∆` with stretch `α` (Definition 16): every `u` has a home HST `home(u)` with
`ρ_home(u)(u, v) ≤ α∆` for every `v` with `d_G(u, v) ≤ ∆`. -/
def HSTRamseyScale (G : WGraph V) (H : Fin m → HST V) (Δ α : ℝ) : Prop :=
  ∀ u, ∃ i, ∀ v, G.dist u v ≤ ENNReal.ofReal Δ → (H i).ρ u v ≤ ENNReal.ofReal (α * Δ)

/-- Almost-Ramsey with stretch `α` (Definition 17): for every `u ∈ V` and every `∆ > 0` there is a
home HST `home(u, ∆)` with `ρ_home(u,∆)(u, v) ≤ α∆` for every `v` with `d_G(u, v) ≤ ∆`. -/
def HSTAlmostRamsey (G : WGraph V) (H : Fin m → HST V) (α : ℝ) : Prop :=
  ∀ u, ∀ Δ : ℝ, 0 < Δ → ∃ i, ∀ v, G.dist u v ≤ ENNReal.ofReal Δ →
    (H i).ρ u v ≤ ENNReal.ofReal (α * Δ)

end ARTreeCover


