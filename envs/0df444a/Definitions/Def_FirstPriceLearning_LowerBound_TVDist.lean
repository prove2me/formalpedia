-- Prove2me | Definitions.Def_FirstPriceLearning_LowerBound_TVDist
-- name    : FirstPriceLearning_LowerBound_TVDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T10:13:37.990466+00:00
-- url     : https://prove2.me/theorems/4c2e8afc-85c3-4dc4-b468-c7f864e97959
-- title:
--   Total variation distance $\|P-Q\|_{\mathrm{TV}}=\tfrac12\int|dP-dQ|$
-- statement:
--   Let $P$ and $Q$ be measures on a common measurable space $(\Omega,\mathcal F)$. Take the dominating measure $\nu=P+Q$ and write $p=dP/d\nu$ and $q=dQ/d\nu$ for the Radon–Nikodym densities. The **total variation distance** between $P$ and $Q$ is
--
--   $$
--   \|P-Q\|_{\mathrm{TV}}=\frac12\int_\Omega |p-q|\,d\nu .
--   $$
--
--   For probability measures it lies in $[0,1]$, does not depend on the dominating measure chosen, and equals $\sup_{A\in\mathcal F}|P(A)-Q(A)|$. It is the distance in which the paper's two-point lower bound (Appendix B) measures how hard it is to tell two HOB distributions apart from the observed bids.
--
--   **Formalization Note** The densities are Mathlib's `rnDeriv` with respect to $P+Q$, converted to real numbers; for the probability measures to which the distance is applied they are finite almost everywhere and bounded by $1$, so the integral is a genuine Bochner integral. Mathlib has no total variation distance at this revision. The platform's `TotalVariationDist` (the $\sup_A$ form) lives in a different Mathlib environment and is therefore not referenced.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 8, §2.1 (Notation)

import Mathlib

open MeasureTheory

namespace FirstPriceLearning.LowerBound

/-- Total variation distance `‖P − Q‖_TV = (1/2) ∫ |dP − dQ|` (Han, Zhou, Weissman,
arXiv:2003.09795v7, §2.1, p. 8). The common dominating measure is `ν = P + Q`, and `dP`, `dQ` are the
Radon–Nikodym densities of `P` and `Q` with respect to `ν`. For probability measures the value lies
in `[0, 1]` and does not depend on the dominating measure chosen. -/
noncomputable def tvDist {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) : ℝ :=
  (1 / 2 : ℝ) * ∫ ω, |(P.rnDeriv (P + Q) ω).toReal - (Q.rnDeriv (P + Q) ω).toReal| ∂(P + Q)

end FirstPriceLearning.LowerBound


