-- Prove2me | Definitions.Def_IntroDelayAMDP_coordEpisode
-- name    : IntroDelayAMDP_coordEpisode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:44:52.847718+00:00
-- url     : https://prove2.me/theorems/aecc0a07-939a-4174-9db9-979b391a5419
-- title:
--   The episode of a tape coordinate
-- statement:
--   The episode a tape coordinate belongs to: the action and next-state draws $(\kappa,h)$ and the coins $(k,s,a,\kappa)$ of an attempt made in episode $\kappa$ all belong to episode $\kappa$. It defines the filtration.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Section 2.1, p.12

import Mathlib
import Definitions.Def_IntroDelayAMDP_Coord

namespace IntroDelayAMDP

/-- **The episode a tape coordinate belongs to** (Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Section 2.1, printed p.12, the
filtration `F_k`). The action and next-state draws `(κ, h)` and the coins `(k, s, a, κ)` of an
attempt made in episode `κ` all belong to episode `κ` (0-based). -/
def coordEpisode {St A : Type} {K H : ℕ} : Coord St A K H → ℕ
  | Sum.inl (κ, _) => κ
  | Sum.inr (Sum.inl (κ, _)) => κ
  | Sum.inr (Sum.inr (Sum.inl (_, _, _, κ))) => κ
  | Sum.inr (Sum.inr (Sum.inr (_, _, _, κ))) => κ

end IntroDelayAMDP


