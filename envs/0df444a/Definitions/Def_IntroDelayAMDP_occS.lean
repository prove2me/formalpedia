-- Prove2me | Definitions.Def_IntroDelayAMDP_occS
-- name    : IntroDelayAMDP_occS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:44:07.691193+00:00
-- url     : https://prove2.me/theorems/43d29aca-5c8a-4347-9d19-c82c99d5c78b
-- title:
--   State occupancy measure, Eq. (13)
-- statement:
--   $q^{P',\pi}(s)$ is the probability that a trajectory of $\pi$ under $P'$ visits $s$, that is, is at $s$ at step $h(s)$. The paper's $q^\pi$ is this quantity under the true $P$, and $q^\star=q^{\pi^\star}$.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Eq. (13), p.13

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_occIter

namespace IntroDelayAMDP

/-- **State occupancy measure** `q^{P′,π}(s)` (Eq. (13), p.13). Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), printed p.13: "for
layer-`h` state `s ∈ S_h` and action `a ∈ A`, `q^{P′,π}(s, a) ≜ Pr_{a_{h′}∼π(·|s_{h′}),
s_{h′+1}∼P′(·|s_{h′},a_{h′})}{s_h = s, a_h = a}`, `q^{P′,π}(s) ≜ ∑_{a∈A} q^{P′,π}(s, a)`".

`occS L P' π s` is the probability that a trajectory of `π` under `P'` from `s₀` visits `s`, i.e.
is at `s` at step `layer(s)`. The paper's `q^π` is `occS L P π` under the true `P`, and
`q⋆ = q^{π⋆}`. -/
noncomputable def occS {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] {H : ℕ}
    (L : LayeredSpace St H) (P' : St → A → St → ℝ) (π : St → A → ℝ) (s : St) : ℝ :=
  occIter P' π L.s0 (L.layer s) s

end IntroDelayAMDP


