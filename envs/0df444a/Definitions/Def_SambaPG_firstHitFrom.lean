-- Prove2me | Definitions.Def_SambaPG_firstHitFrom
-- name    : SambaPG_firstHitFrom
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:05.235073+00:00
-- url     : https://prove2.me/theorems/ffe7af2c-47c1-4f43-a70b-43975dc26bf0
-- title:
--   First time at or after $s$ at which a property holds
-- statement:
--   For a property $P$ of times and a starting time $s\in\mathbb Z_+\cup\{\infty\}$,
--
--   $$
--   \mathrm{firstHitFrom}(P,s)=\min\{t\in\mathbb Z_+ : t\ge s,\ P(t)\},
--   $$
--
--   with the value $\infty$ when no such time exists. It expresses the hitting times of the paper: $\tau(\hat x)=\min\{t\ge1:p_{a^\star}(t)>1/\hat x\}$ in (8), the times $\sigma^{(k)},\tau^{(k)}$ of (11), and $\tau_B,\tau_C$ in Lemma 7.
--
--   **Formalization Note** The value lies in $\mathbb N\cup\{\infty\}$, so the expectation of a hitting time that is infinite with positive probability is $\infty$.
-- source:
--   Denisov & Walton, Regret Analysis of a Markov Policy Gradient Algorithm for Multi-arm Bandits, arXiv:2007.10229v3, (8), p.8; (11), p.9; Lemma 7, p.23

import Mathlib

namespace SambaPG

/-- **First time at or after `s` at which a property holds.**
Used for the hitting times of Denisov & Walton, arXiv:2007.10229v3: `τ(x̂) = min{t ≥ 1 : …}` of
(8), p.8; `σ^{(k)}`, `τ^{(k)}` of (11), p.9; `τ_B`, `τ_C` of Lemma 7, p.23.

`firstHitFrom P s = min{t ∈ ℤ₊ : t ≥ s, P t}`, and `= ∞` when no such time exists (in particular
when `s = ∞`), as in the convention below (11): "If no such time exists … then we let `σ^{(k)} = ∞`".

**Formalization Note.** The value is in `ℕ∞`, the infimum of the empty set being `⊤`, so an
expectation of a hitting time that is infinite with positive probability is `∞`. -/
noncomputable def firstHitFrom (P : ℕ → Prop) (s : ℕ∞) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : s ≤ t ∧ P t), (t : ℕ∞)

end SambaPG


