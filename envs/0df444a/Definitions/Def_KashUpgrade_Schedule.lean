-- Prove2me | Definitions.Def_KashUpgrade_Schedule
-- name    : KashUpgrade_Schedule
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:19:15.422156+00:00
-- url     : https://prove2.me/theorems/357efcf3-6fa8-43b3-99d2-2854b62353ec
-- title:
--   An introduction schedule $s_0=0<s_1<s_2<\dots$
-- statement:
--   An introduction schedule fixes the times of the technology introductions: $s_0=0$, and a finite or infinite sequence of times $s_1<s_2<\cdots$ in $\mathbb N$, where $s_i$ is the time of the $i$-th introduction. At most one class is introduced per period, and quality grows linearly with time, so a customer of type $\theta$ gets benefit $\theta\cdot s_i$ per period from class $i$.
--
--   **Formalization Note** The number of introductions $J$ is an extended natural number, $J=\infty$ for an infinite sequence. The values $s_i$ with $i>J$ are not part of the schedule. Every statement of the mission holds whatever they are.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), (1), p.10; §3, p.9

import Mathlib

namespace KashUpgrade

/-- **An introduction schedule.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), (1), p.10: `s₀ = 0` and a (possibly infinite) sequence of
introduction times `s₁ < s₂ < …` in `ℕ`, with up to one new technology class per period (§3, p.9).

**Formalization Note** `J : ℕ∞` is the number of introductions, `⊤` for an infinite sequence. The
values `s i` with `i > J` are not part of the schedule; no definition of this mission uses them
except through the zero-weight index range. -/
structure Schedule where
  /-- The number of introductions. -/
  J : ℕ∞
  /-- The introduction times; `s i` is the time of the `i`-th introduction. -/
  s : ℕ → ℕ
  /-- The convention `s₀ = 0`. -/
  s_zero : s 0 = 0
  /-- Introduction times are strictly increasing. -/
  s_lt : ∀ i : ℕ, ((i + 1 : ℕ) : ℕ∞) ≤ J → s i < s (i + 1)

end KashUpgrade


