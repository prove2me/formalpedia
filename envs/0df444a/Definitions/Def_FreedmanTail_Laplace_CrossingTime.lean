-- Prove2me | Definitions.Def_FreedmanTail_Laplace_CrossingTime
-- name    : FreedmanTail_Laplace_CrossingTime
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:21:07.644491+00:00
-- url     : https://prove2.me/theorems/e67baf6b-1d37-4793-8b58-b4159b904345
-- title:
--   Definition (1.7) — τ_a = least n with S_n ≥ a (∞ if none) and W_a = T_{τ_a} = Σ_{i=1}^{τ_a} V_i ∈ [0, ∞]
-- statement:
--   In the setting of Definition (1.2) fix a level $a$. Let $\tau_a$ be the least $n$, if any, with $S_n \ge a$, and let $\tau_a = \infty$ if there is no such $n$. Let
--   $$
--   W_a = T_{\tau_a} = \sum_{i=1}^{\tau_a} V_i \in [0, \infty] .
--   $$
--   Thus $W_a$ is the total amount of conditional variance it takes for the partial-sum process to cross the level $a$, if it crosses; otherwise $W_a = \sum_{i \ge 1} V_i$ is the total amount of conditional variance, which may be $+\infty$.
--
--   A third, auxiliary function: for $c \in \mathbb R$ and $w \in [0, \infty]$ let $\exp[-c w]$ denote $e^{-c w}$ for finite $w$ and $0$ for $w = \infty$. With $c = f(\lambda) > 0$ this is the paper's reading of $\exp[-f(\lambda) W_a]$ on the event $\{W_a = \infty\}$.
--
--   **Formalization Note** $\tau_a$ takes values in $\mathbb N \cup \{\infty\}$ (`WithTop ℕ`). $W_a$ takes values in $[0, \infty]$ (`ℝ≥0∞`) and is the sum over all $i \ge 1$ with $i \le \tau_a$ of the nonnegative part of $V_i$; since $V_i \ge 0$ almost surely, taking the nonnegative part changes nothing almost surely. The auxiliary function `expNegMul c w` is $0$ at $w = \infty$, so that an expectation of $\exp[-f(\lambda) W_a]$ gets no contribution from the event $\{W_a = \infty\}$ (a plain `Real.exp (-(c * w.toReal))` would wrongly give $1$ there).
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 102 (PDF p. 3), (1.7) Definition and the paragraph after it

import Mathlib
import Definitions.Def_FreedmanTail_Bernstein_PartialSums

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FreedmanTail.Laplace

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Freedman (1975), Definition (1.7), p. 102: `τ_a` is the least `n` with `S_n ≥ a`, and
`τ_a = ∞` (here `⊤`) if there is no such `n`. -/
noncomputable def tau (a : ℝ) (X : ℕ → Ω → ℝ) (ω : Ω) : WithTop ℕ := by
  classical
  exact if h : ∃ n : ℕ, a ≤ FreedmanTail.Bernstein.S X n ω then ((Nat.find h : ℕ) : WithTop ℕ) else ⊤

/-- Freedman (1975), Definition (1.7), p. 102: `W_a = T_{τ_a} = Σ_{i=1}^{τ_a} V_i`, a
`[0, ∞]`-valued random variable. On `{τ_a = ∞}` it is the whole series `Σ_{i ≥ 1} V_i`,
which may be `+∞`. Each `V_i` enters through `ENNReal.ofReal`; since `V_i ≥ 0` almost surely,
this clamp changes nothing almost surely. -/
noncomputable def W (a : ℝ) (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (P : Measure Ω) (ω : Ω) :
    ℝ≥0∞ :=
  ∑' i : ℕ, if 1 ≤ i ∧ ((i : WithTop ℕ) ≤ tau a X ω) then ENNReal.ofReal (FreedmanTail.Bernstein.V ℱ X P i ω) else 0

/-- `exp[−c·w]` for `w ∈ [0, ∞]`, with the value `0` at `w = ∞` (the paper's convention
`exp[−f(λ)·∞] = 0`, `f(λ) > 0`). -/
noncomputable def expNegMul (c : ℝ) (w : ℝ≥0∞) : ℝ :=
  if w = ⊤ then 0 else Real.exp (-(c * w.toReal))

end FreedmanTail.Laplace


