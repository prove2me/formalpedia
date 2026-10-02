-- Prove2me | Definitions.Def_TeschlQM_OneParticle_IsBoundedVanishingAtInfinity
-- name    : TeschlQM_OneParticle_IsBoundedVanishingAtInfinity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T07:48:17.315233+00:00
-- url     : https://prove2.me/theorems/3b646a12-05fa-4bd4-bcc5-f58b1a1997bd
-- title:
--   L^∞_∞(ℝⁿ): bounded Borel functions vanishing at infinity
-- statement:
--   $L^\infty_\infty(\mathbb R^n)$ denotes the bounded Borel functions which vanish at infinity. A real function $V$ on $\mathbb R^n$ belongs to it if $V$ is Borel measurable, $\sup_x |V(x)| < \infty$, and
--   $$V(x) \to 0 \qquad \text{as } |x| \to \infty.$$
--
--   Potentials in $L^\infty_\infty(\mathbb R^n)$, or in $L^\infty_\infty(\mathbb R^n) + L^2(\mathbb R^n)$ when $n \le 3$, are relatively compact perturbations of $H_0$.
--
--   **Formalization Note.** `IsBoundedVanishingAtInfinity V` is `Measurable V`, a uniform bound $|V(x)| \le C$, and `Tendsto V (cocompact _) (𝓝 0)`; on $\mathbb R^n$ the cocompact filter is $|x| \to \infty$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 170, Section 7.3, Lemma 7.11

import Mathlib

namespace TeschlQM.OneParticle

open Filter Topology

/-- Teschl, Lemma 7.11, p. 170: `V ∈ L^∞_∞(ℝⁿ)`, "the bounded Borel functions which vanish at
infinity": `V` is Borel measurable, bounded, and `V(x) → 0` as `|x| → ∞` (the filter
`cocompact` on `ℝⁿ`). -/
def IsBoundedVanishingAtInfinity {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  Measurable V ∧ (∃ C : ℝ, ∀ x, |V x| ≤ C) ∧ Tendsto V (cocompact _) (𝓝 0)

end TeschlQM.OneParticle


