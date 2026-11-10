-- Prove2me | Definitions.Def_MomentSearch_sketchCollection
-- name    : MomentSearch_sketchCollection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:07:38.505295+00:00
-- url     : https://prove2.me/theorems/dca04c96-3111-4031-aef0-f324bdf19dd5
-- title:
--   Uncertainty collection $\mathcal U_\sigma$ induced by a sketch
-- statement:
--   Let $\Delta_n=\{p\in\mathbb R^n_{\ge0}:\sum_{i=0}^{n-1}p_i=1\}$. Any map $\sigma:\Delta_n\to X$, for a set $X$ of possible messages, is called a **sketch**. Its **uncertainty collection** $\mathcal U_\sigma$ consists of the nonempty sets
--
--   $$
--   \{p\in\Delta_n : \sigma(p)=x\},\qquad x\in X.
--   $$
--
--   The searcher sees only the message $\sigma(p)$ and must choose a strategy that is good for every distribution with that message.
--
--   **Formalization Note** $\Delta_n$ is Mathlib's standard simplex. The sketch is given as a map on all of $\mathbb R^n$; only its values on $\Delta_n$ matter, because every fibre is intersected with $\Delta_n$. Empty fibres are excluded, as in the paper.
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §2.2, p.6 (PDF p.8)

import Mathlib

namespace MomentSearch

/-- The uncertainty collection `𝒰_σ` of a sketch `σ : Δ_n → X` (Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §2.2, p.6 (PDF p.8)):
"Its uncertainty collection Uσ consists of the nonempty sets {p ∈ ∆n : σ(p) = x} for x ∈ X."

Here `Δ_n = {p ∈ ℝ^n_{≥0} : ∑ p_i = 1}` is Mathlib's `stdSimplex ℝ (Fin n)`.

**Formalization Note.** The sketch is given as a map on all of `ℝ^n`; only its values on the
simplex matter, because every fibre is intersected with `stdSimplex ℝ (Fin n)`. Empty fibres are
excluded, as in the paper. -/
def sketchCollection {n : ℕ} {X : Type*} (σ : (Fin n → ℝ) → X) : Set (Set (Fin n → ℝ)) :=
  {U | U.Nonempty ∧ ∃ x : X, U = {p | p ∈ stdSimplex ℝ (Fin n) ∧ σ p = x}}

end MomentSearch


