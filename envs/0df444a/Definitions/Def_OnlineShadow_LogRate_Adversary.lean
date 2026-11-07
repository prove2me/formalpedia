-- Prove2me | Definitions.Def_OnlineShadow_LogRate_Adversary
-- name    : OnlineShadow_LogRate_Adversary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:04:15.010312+00:00
-- url     : https://prove2.me/theorems/52372573-f065-4156-b3a2-d96ddd84ef87
-- title:
--   Adaptive adversary for online shadow tomography
-- statement:
--   An **adaptive adversary** for online shadow tomography of $d$-dimensional states chooses the observables one at a time. Given the transcript
--   $$\mathcal T_{t-1}=\big((A^{(1)},\widehat\mu^{(1)}),\dots,(A^{(t-1)},\widehat\mu^{(t-1)})\big)$$
--   of the earlier observables and the learner's answers, it selects the next observable $A^{(t)}$, which is an **effect**: a $d\times d$ complex matrix with $0\preceq A^{(t)}\preceq 1$ in the Loewner order.
--
--   This is the opponent in Definition 1.1: the adversary sees every answer before choosing the next observable, which is what separates online from offline shadow tomography.
--
--
--   **Formalization Note** The adversary is a deterministic function of the transcript, written as a list whose length is the round index; it is defined on transcripts of every length, and only the first $m$ rounds are used. A randomized adversary is a mixture of deterministic ones.
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition 1.1, p. 3

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_IsEffect

namespace OnlineShadow.LogRate

/-- An **adaptive adversary** for online shadow tomography of `d`-dimensional states
(Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition 1.1, p.3): given the transcript `T` of the interaction so far, the list of earlier
observables and the learner's answers `[(A⁽¹⁾, μ̂⁽¹⁾), …, (A⁽ᵗ⁾, μ̂⁽ᵗ⁾)]`, it selects the next observable
`obs T`, which is an effect `0 ⪯ A ⪯ 1`.

**Formalization Note** The adversary is a deterministic function of the transcript (a randomized adversary
is a mixture of deterministic ones). The round index is the length of the transcript, and the function is
defined on transcripts of every length; only the first `m` rounds are ever used. -/
structure Adversary (d : ℕ) where
  /-- The next observable, as a function of the transcript of earlier (observable, answer) pairs. -/
  obs : List (Matrix (Fin d) (Fin d) ℂ × ℝ) → Matrix (Fin d) (Fin d) ℂ
  /-- Every observable chosen is an effect, `0 ⪯ A ⪯ 1`. -/
  isEffect : ∀ T, ShadowTomography.UpperBound.IsEffect (obs T)

end OnlineShadow.LogRate


