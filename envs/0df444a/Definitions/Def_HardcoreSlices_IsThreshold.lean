-- Prove2me | Definitions.Def_HardcoreSlices_IsThreshold
-- name    : HardcoreSlices_IsThreshold
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:35:58.458577+00:00
-- url     : https://prove2.me/theorems/0b8fef93-8591-4a91-83fd-465154232248
-- title:
--   The density $\alpha^*(\Delta)$ and the globally fixed $\gamma=o_\Delta(1)$
-- statement:
--   The critical density is $\alpha^*(\Delta)=\log\Delta/(2\Delta)$, with the natural logarithm. For a vertex set $\tau$ in one side, let $Y\setminus N(\tau)$ be the vertices of the other side with no neighbour in $\tau$.
--
--   A sequence $\gamma:\mathbb N\to\mathbb R$ is a **threshold at $\ell$** if $\gamma(\Delta)\to0$, $0<\gamma(\Delta)<1$ for large $\Delta$, and for all large $\Delta$, with high probability over a uniformly random $\Delta$-regular bipartite graph, every $\tau$ in either side satisfies:
--
--   1. if $|\tau|\ge(1-\gamma)\alpha^*(\Delta)|X|$ then $|Y\setminus N(\tau)|\le\frac{(\ell+1)\log\Delta}{\sqrt\Delta}|Y|$;
--   2. if $|\tau|\le(1-\gamma)\alpha^*(\Delta)|X|$ then $|Y\setminus N(\tau)|\ge\frac{\ell\log\Delta}{\sqrt\Delta}|Y|$.
--
--   This is the conclusion of Lemma 3.1. The paper fixes one such $\gamma$ for its whole length, so that the regimes of its two chains overlap at $(1-\gamma)\alpha^*(\Delta)$.
--
--   **Formalization Note** Later statements hold for every $\gamma$ with `IsThreshold 6 γ`, since the proof of Theorem 1.8 sets $\ell\ge6$.
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), p.3 (α∗, γ), p.19 ("We fix the value of γ globally"), Lemma 3.1, pp.12–13

import Mathlib
import Definitions.Def_ExpanderBIS_RandomHardCore_Setting

open Classical Filter

namespace HardcoreSlices

open ExpanderBIS.RandomHardCore

/-- **The density `α∗`.** Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), §1.1, p.3: "we fix `α∗(∆) = log ∆/(2∆)`". The logarithm is natural. -/
noncomputable def alphaStar (Δ : ℕ) : ℝ := Real.log Δ / (2 * Δ)

/-- `Y \ N(τ)` for `τ` in one side: the vertices of the other side with no neighbour in `τ`, where
`N` is the published `vertexBoundary` (p.9). -/
noncomputable def nonNbrs {m : ℕ} (G : SimpleGraph (Vertex m)) (side τ : Finset (Vertex m)) :
    Finset (Vertex m) :=
  (Finset.univ \ side) \ vertexBoundary G τ

/-- The conclusion of Lemma 3.1 (pp.12–13) at `ℓ`, `γ`, for one graph: for each side, every `τ` in that
side satisfies (1) if `|τ| ≥ (1 − γ)α∗(∆)|X|` then `|Y \ N(τ)| ≤ ((ℓ + 1) log ∆ / √∆)|Y|`, and (2) if
`|τ| ≤ (1 − γ)α∗(∆)|X|` then `|Y \ N(τ)| ≥ (ℓ log ∆ / √∆)|Y|`. -/
def ExpansionEvent (ℓ γ : ℝ) (Δ m : ℕ) (G : SimpleGraph (Vertex m)) : Prop :=
  ∀ side ∈ ({oddSide m, evenSide m} : Finset (Finset (Vertex m))), ∀ τ ⊆ side,
    ((1 - γ) * alphaStar Δ * m ≤ τ.card →
      ((nonNbrs G side τ).card : ℝ) ≤ (ℓ + 1) * Real.log Δ / Real.sqrt Δ * m) ∧
    ((τ.card : ℝ) ≤ (1 - γ) * alphaStar Δ * m →
      ℓ * Real.log Δ / Real.sqrt Δ * m ≤ ((nonNbrs G side τ).card : ℝ))

/-- **The globally fixed `γ = o∆(1)`.** Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), p.3 ("some small constant `γ = o∆(1)` to be specified
later") and p.19 ("We fix the value of `γ` globally here for the remainder of the paper").

`IsThreshold ℓ γ` says that the sequence `γ` tends to `0`, lies in `(0, 1)` for large `∆`, and for large `∆`
gives the conclusion of Lemma 3.1 at `ℓ` with high probability.

**Formalization Note.** The later statements share one `γ`, because the paper's regimes must overlap at
`(1 − γ)α∗(∆)` (p.4). They are stated for every `γ` with `IsThreshold 6 γ` (p.20: "setting `ℓ ≥ 6`"). -/
def IsThreshold (ℓ : ℝ) (γ : ℕ → ℝ) : Prop :=
  Tendsto γ atTop (nhds 0) ∧ (∀ᶠ Δ in atTop, 0 < γ Δ ∧ γ Δ < 1) ∧
    ∀ᶠ Δ in atTop, AlmostEvery Δ (fun m G => ExpansionEvent ℓ (γ Δ) Δ m G)

end HardcoreSlices


