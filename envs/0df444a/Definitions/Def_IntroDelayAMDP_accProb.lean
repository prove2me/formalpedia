-- Prove2me | Definitions.Def_IntroDelayAMDP_accProb
-- name    : IntroDelayAMDP_accProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:43:23.057266+00:00
-- url     : https://prove2.me/theorems/c163e3c1-195d-482e-bec4-41512c579e7a
-- title:
--   GRR acceptance ratio, Eq. (4)
-- statement:
--   For two policies and the first $h+1$ pairs of a trajectory,
--   $$\alpha_{k,\kappa}=\frac12\prod_{h'=0}^{h}\frac{\pi_k(a_{h'}\mid s_{h'})}{\pi_\kappa(a_{h'}\mid s_{h'})}.$$
--
--   **Formalization Note** Algorithm 1 accepts with probability $\min\{1,\alpha_{k,\kappa}\}$. The `min` is applied by the run, not here. The policies of Algorithm 1 are positive, so no division by zero occurs there.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Eq. (4), p.6

import Mathlib

namespace IntroDelayAMDP

/-- **GRR acceptance ratio** `α_{k,κ}` (Eq. (4), p.6). Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), printed p.6: "Let episode `κ` be
accepted with probability `α_{k,κ} ≜ ½ ∏_{h′=0}^{h} π_k(a_{κ,h′} | s_{κ,h′}) / π_κ(a_{κ,h′} | s_{κ,h′})`, (4)".

For two policies `πk, πκ` and the first `h + 1` pairs `t 0, …, t h` of a trajectory,
`accProb πk πκ t = ½ ∏_{i ≤ h} πk(t i) / πκ(t i)`.

**Formalization Note.** Algorithm 1 (line 10) accepts with probability `min{1, α_{k,κ}}`; the
`min` is applied by the run, not here. The policies of Algorithm 1 are positive, so no division by
`0` occurs there. -/
noncomputable def accProb {St A : Type} {h : ℕ} (πk πκ : St → A → ℝ) (t : Fin (h + 1) → St × A) : ℝ :=
  (1 / 2) * ∏ i, πk (t i).1 (t i).2 / πκ (t i).1 (t i).2

end IntroDelayAMDP


