-- Prove2me | Definitions.Def_RobustPrefLearn_MTP_Supplement_SubsetAccuracy
-- name    : RobustPrefLearn_MTP_Supplement_SubsetAccuracy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:11:38.093536+00:00
-- url     : https://prove2.me/theorems/cfd05b54-a54d-428c-90c6-8f31379f08e6
-- title:
--   Definition 2(i)–(iii), pp. 12–13 — accuracy on a specified subset
-- statement:
--   Let $K$ be the number of versions, $M$ a specified subset of preference models, and $\delta\in[0,1]$. An admissible policy $\pi$ is **$\delta(M)$-accurate** when, for every $f\in M$,
--   $$\mathbb P_f^\pi(\tau<\infty)=1,\qquad \mathbb P_f^\pi(d_\tau\ne\sigma_f^{-1}(1))\le\delta.$$
--   A family $\Pi=(\pi_\delta)$ is accurate on $M$ if this holds for every $\delta\in(0,1)$. Taking $M=\mathcal M_p$ recovers the published full-class accuracy predicates.
--
--   These predicates allow Theorem 2 to specify accuracy only on its given finite class, without imposing accuracy on all of $\mathcal M_p$.
--
--   **Formalization Note** The probability law, stopping time, error event, and admissibility are the published definitions. Theorems supply $M\subseteq\mathcal M_p$ and the confidence domain. The family uses $(0,1)$, as in the base mission; no assertion at $\delta=1$ is needed.
-- source:
--   Feng, Caldentey & Ryan, SSRN 3215614, Definition 2(i)–(iii), pp. 12–13

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Policy

namespace RobustPrefLearn.MTP.Supplement

/-- Definition 2(i), p.12: accuracy on a specified subset of preferences.
Theorems supply `M ⊆ Mp p` and `δ ∈ (0,1)` separately. -/
def DeltaAccurateOn {K : ℕ} (M : Set (Pref K)) (δ : ℝ) (π : Policy K) : Prop :=
  Admissible π ∧ ∀ f ∈ M, probStop π f = 1 ∧ probWrong π f ≤ ENNReal.ofReal δ

/-- Definition 2(iii), p.13, with the specified class in place of all `Mp p`. -/
def AccurateOn {K : ℕ} (M : Set (Pref K)) (fam : ℝ → Policy K) : Prop :=
  ∀ δ ∈ Set.Ioo (0 : ℝ) 1, DeltaAccurateOn M δ (fam δ)

end RobustPrefLearn.MTP.Supplement


