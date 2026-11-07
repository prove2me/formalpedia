-- Prove2me | Definitions.Def_IntroDelayAMDP_initState
-- name    : IntroDelayAMDP_initState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:18.584298+00:00
-- url     : https://prove2.me/theorems/f88ad10f-d9ff-456f-82b5-10e2f94fdd5d
-- title:
--   Initial state of Algorithm 1
-- statement:
--   Line 1 of Algorithm 1: no observations (so the confidence set is the set of all transitions), no visits, zero cumulative loss (so $\pi_1$ is uniform) and no estimates. The entries of episodes not yet played are placeholders that the run never reads.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 1, line 1, p.16

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_AlgState

namespace IntroDelayAMDP

/-- **Initial state of Algorithm 1** (line 1, printed p.16, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530): "Initialize `P_1` as the set
of all transitions, with no unfinished estimates"): no observations (so the confidence set
`confSet L β (fun _ _ => [])` is the set of all transitions), no visits, zero cumulative loss (so
`π_1` is uniform), and no estimates. The entries `pol`, `traj` of episodes not yet played are
placeholders that the run never reads. -/
noncomputable def initState {St A : Type} {H : ℕ} (L : LayeredSpace St H) (a0 : A) : AlgState St A where
  cumG _ _ := 0
  obs _ _ := []
  visits _ _ := 0
  pol _ _ _ := 0
  traj _ _ := (L.s0, a0)
  started _ _ _ := False
  active _ _ _ := False
  w _ _ _ := 0
  piece _ _ _ := 0
  ind _ _ _ _ := False

end IntroDelayAMDP


