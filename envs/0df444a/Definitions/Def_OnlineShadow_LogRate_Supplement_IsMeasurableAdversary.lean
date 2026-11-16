-- Prove2me | Definitions.Def_OnlineShadow_LogRate_Supplement_IsMeasurableAdversary
-- name    : OnlineShadow_LogRate_Supplement_IsMeasurableAdversary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:54:24.513556+00:00
-- url     : https://prove2.me/theorems/31ff5ab1-4a49-4cb4-bc9a-b62903c68d06
-- title:
--   Measurable adaptive adversary: the round-$t$ observable is Borel in the earlier answers
-- statement:
--   Let $\mathrm{adv}$ be an adaptive adversary for online shadow tomography: a function choosing the next observable $0\preceq A\preceq1$ from the transcript of earlier (observable, answer) pairs. Given answers $a=(a_0,\dots,a_{t-1})\in\mathbb R^t$, run the interaction: $\mathcal T_0=\emptyset$ and $\mathcal T_{j+1}=\mathcal T_j\cup\{(\mathrm{adv}(\mathcal T_j),a_j)\}$. The adversary is **measurable** if for every $t$ the map
--   $$\mathbb R^t\ni a\longmapsto \mathrm{adv}(\mathcal T_t)\in\mathbb C^{d\times d}$$
--   is Borel measurable.
--
--   When the learner's outcomes are continuous, the probability of an event is an integral over transcripts with Lebesgue measure (p. 19 of the paper), and this integral is defined only when the adversary's choices depend measurably on the earlier answers.
--
--   **Formalization Note** A matrix is read as its array of entries (product σ-algebra, which is the Borel σ-algebra of $\mathbb C^{d\times d}$). The adversary itself is the published deterministic `OnlineShadow.LogRate.Adversary`; no other restriction is imposed.
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition 1.1, p. 3; integral over transcripts, p. 19

import Mathlib
import Definitions.Def_OnlineShadow_LogRate_Adversary

namespace OnlineShadow.LogRate.Supplement

/-- An adaptive adversary (the published `OnlineShadow.LogRate.Adversary`) is **measurable** when, for every
round `t`, the observable it chooses at round `t` depends Borel-measurably on the earlier answers
`(μ̂⁽⁰⁾, …, μ̂⁽ᵗ⁻¹⁾) ∈ ℝ^t` (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition 1.1, p.3; the integral over
adaptive transcripts, p.19). Given the answers `a`, the transcript is built by running the
interaction: `T₀ = []` and `T_{j+1} = T_j ++ [(adv.obs T_j, a_j)]`; the round-`t` observable is
`adv.obs T_t`.

**Formalization Note** The paper integrates over transcripts with Lebesgue measure ("de denotes the sum
over transcript lengths ℓ of the Lebesgue measure over length-ℓ transcripts", p.19), which presupposes
that the adversary's choice is a measurable function of the earlier answers; without it the success
probability of a continuous-outcome protocol is not defined. A matrix is read as its array of entries
(product σ-algebra = Borel σ-algebra). No other restriction is imposed. -/
def IsMeasurableAdversary {d : ℕ} (adv : OnlineShadow.LogRate.Adversary d) : Prop :=
  ∀ t : ℕ, Measurable (fun a : Fin t → ℝ =>
    Matrix.of.symm (adv.obs ((List.ofFn a).foldl (fun T x => T ++ [(adv.obs T, x)]) [])))

end OnlineShadow.LogRate.Supplement


