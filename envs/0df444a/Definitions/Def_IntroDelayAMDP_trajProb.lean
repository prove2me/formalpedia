-- Prove2me | Definitions.Def_IntroDelayAMDP_trajProb
-- name    : IntroDelayAMDP_trajProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:43:42.632089+00:00
-- url     : https://prove2.me/theorems/d0435609-0902-44cc-a205-c1d677f032f8
-- title:
--   Probability of a partial trajectory
-- statement:
--   The probability that the first $h+1$ pairs of a trajectory of $\pi$ under $P$ started at $s_0$ are the given ones:
--   $$\mathbf 1[s_{0}\text{ is initial}]\prod_{h'<h}P(s_{h'+1}\mid s_{h'},a_{h'})\prod_{h'=0}^{h}\pi(a_{h'}\mid s_{h'}).$$
--   It expresses the expectation $\mathbb E^{\pi_k}[f(\tau^h)]$ in Lemma A.4 as a finite sum.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), App. A.2, p.32

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace

namespace IntroDelayAMDP

/-- **Probability of a partial trajectory** `Pr_π(τ^h = τ)` (App. A.2, p.32). Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), printed p.32:
"`Pr(τ^h_κ = τ, A_κ = 1 | G) = ∏_{h′<h} P(s_{h′+1} | s_{h′}, a_{h′}) ∏_{h′=0}^{h} π_κ(a_{h′} | s_{h′}) · …`",
for "the first `h + 1` steps of a trajectory of `π_k` under `P`".

For a policy `π` and a transition `P`, the probability that the first `h + 1` pairs of a
trajectory started at `s₀` are `t 0, …, t h` is
`trajProb L P π t = 1[t 0 starts at s₀] · ∏_{i<h} P(s_{i+1} | s_i, a_i) · ∏_{i≤h} π(a_i | s_i)`. -/
noncomputable def trajProb {St A : Type} [DecidableEq St] {H : ℕ} (L : LayeredSpace St H)
    (P : St → A → St → ℝ) (π : St → A → ℝ) {h : ℕ} (t : Fin (h + 1) → St × A) : ℝ :=
  (if (t 0).1 = L.s0 then 1 else 0) *
    (∏ i : Fin h, P (t i.castSucc).1 (t i.castSucc).2 (t i.succ).1) * ∏ i, π (t i).1 (t i).2

end IntroDelayAMDP


