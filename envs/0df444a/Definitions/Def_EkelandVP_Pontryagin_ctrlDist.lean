-- Prove2me | Definitions.Def_EkelandVP_Pontryagin_ctrlDist
-- name    : EkelandVP_Pontryagin_ctrlDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:08:45.922988+00:00
-- url     : https://prove2.me/theorems/225ef110-5b41-4416-a202-3b1552e5b0a9
-- title:
--   (7.7) — the distance δ(u₁, u₂) = meas{t ∈ [0, T] | u₁(t) ≠ u₂(t)} between controls
-- statement:
--   For a real number $T$ and two controls $u_1, u_2 : \mathbb R \to K$, the **distance** between them is the Lebesgue measure of the set of times in $[0, T]$ where they disagree:
--
--   $$
--   \delta(u_1, u_2) = \operatorname{meas}\{t \in [0, T] \mid u_1(t) \neq u_2(t)\}. \qquad (7.7)
--   $$
--
--   Ekeland equips the set $\mathcal U$ of measurable controls $[0, T] \to K$ with $\delta$ and proves (Lemma 7.2) that it is a complete metric space; this is the space on which his variational principle is applied in §7.
--
--   **Formalization Note** The value is the real number obtained from the Lebesgue (outer) measure of the set; it is finite because the set lies in $[0, T]$. $\delta$ vanishes exactly on pairs of controls that agree almost everywhere on $[0, T]$, so $\mathcal U$ is a metric space on almost-everywhere classes.
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), p. 349, §7, (7.7)

import Mathlib

namespace EkelandVP.Pontryagin

/-- Ekeland (1974), §7, p. 349, (7.7): the distance between two controls,
`δ(u₁, u₂) = meas {t ∈ [0, T] | u₁(t) ≠ u₂(t)}` (Lebesgue measure). -/
noncomputable def ctrlDist {K : Type*} (T : ℝ) (u₁ u₂ : ℝ → K) : ℝ :=
  (MeasureTheory.volume (Set.Icc 0 T ∩ {t | u₁ t ≠ u₂ t})).toReal

end EkelandVP.Pontryagin


