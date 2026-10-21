-- Prove2me | Definitions.Def_ReportDepSP_Honesty_Setting
-- name    : ReportDepSP_Honesty_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:19.160295+00:00
-- url     : https://prove2.me/theorems/b1af8fa0-1b38-4f78-a882-a644054d5cac
-- title:
--   §2, pp. 4–5 and (3), p. 7 — ROLs, attainability distribution, match probability f^R_r, expected payoff U(v|R) of (1), condition (3)
-- statement:
--   The model of a participant who submits a rank-ordered list in a strategy-proof direct mechanism, with report-dependent utility.
--
--   1. **Options, ranks, ROLs.** There are $n$ options $\mathcal S = \{1,\dots,n\}$ and $n$ ranks $⟦1,n⟧$. A **rank-ordered list (ROL)** is a bijection $R:\mathcal S\to⟦1,n⟧$ sending each option $s$ to its rank $R(s)$; its $r$-th ranked option is $s^R_r = R^{-1}(r)$. The true ROL is $R = (1,2,\dots,n)$, the identity.
--
--   2. **Attainability distribution.** In an attainability state $a\in\{0,1\}^n$, option $s$ is attainable ($A_s=1$) or not ($A_s = 0$). An attainability distribution is a function $P$ on the $2^n$ states with
--   $$P(a)\ge 0 \ \text{ for all } a, \qquad \sum_{a} P(a) = 1 .$$
--   The attainabilities may be arbitrarily correlated.
--
--   3. **Match probability.** The participant is matched with the highest-ranked attainable option of her submitted list. Hence the probability of being matched with her $r$-th ranked option under $R$ is
--   $$f^R_r = P\bigl(A_{s^R_r} = 1,\ A_{s^R_t} = 0 \ \ \forall t < r\bigr).$$
--
--   4. **Expected payoff (1).** Given report-independent payoffs $v = (v_s)_{s\in\mathcal S}$ and report-dependent payoffs $\rho(r)$ for being matched with one's $r$-th ranked option,
--   $$U(v\mid R) = \sum_{r=1}^n f^R_r\,\bigl(v_{s^R_r} + \rho(r)\bigr).$$
--
--   5. **Condition (3).** For a ROL $\widetilde R$ with match probabilities $\widetilde f_r = f^{\widetilde R}_r$ and the truth's $f_r = f^R_r$,
--   $$\sum_{r=1}^{\bar r}\bigl(f_r - \widetilde f_r\bigr)\ \ge\ 0 \qquad \forall\, \bar r\in⟦1,n⟧ ,$$
--   i.e. no rank cutoff $\bar r$ at which $\widetilde R$ gives a higher probability of being matched with one of the top $\bar r$ ranked options.
--
--   These objects are shared by every statement of the mission: Proposition 2 compares $U(v\mid R)$ with $U(v\mid\widetilde R)$ and characterizes it by condition (3).
--
--   **Formalization Note** Options and ranks are both `Fin n`, 0-indexed: Lean option `i` is the page's option $i+1$, rank `r` the page's rank $r+1$, and `rbar : Fin n` the page's $\bar r$ shifted by one, with `Iic rbar` the page's range $1,\dots,\bar r$. A ROL is `Equiv.Perm (Fin n)` read as option ↦ rank, so $s^R_r$ is `R.symm r` and the true ROL is `1`. States are `Fin n → Bool`; probabilities of events are finite sums of `P` over the states in the event (no measure theory). `IsAttainabilityDist P` is the probability-distribution condition; `matchProb`, `payoff` and `Condition3` are defined for every real weight function, and the theorems state which conditions on `P` they use.
-- source:
--   Meisner, Report-dependent utility and strategy-proofness, CRC TRR 190 Discussion Paper No. 289 (2021; Management Science doi:10.1287/mnsc.2022.4504), §2, pp. 4–5 (ROLs, A_s, f̃_r, display (1)); Proposition 2, display (3), p. 7

import Mathlib

namespace ReportDepSP.Honesty

open Finset

/-- An attainability distribution on `n` options (Meisner, §2, p. 5): nonnegative weights on the
attainability states `a : Fin n → Bool` (`a s = true` iff option `s` is attainable, the page's
`A_s = 1`) summing to one. The joint law is arbitrary; the attainabilities may be correlated. -/
def IsAttainabilityDist {n : ℕ} (P : (Fin n → Bool) → ℝ) : Prop :=
  (∀ a, 0 ≤ P a) ∧ ∑ a, P a = 1

/-- `f^R_r` (p. 5): the probability that the `r`-th ranked option `s^R_r = R⁻¹(r)` of the ROL `R`
(a bijection option ↦ rank) is attainable and no option ranked above it is, i.e. the probability
that the participant is matched with her `r`-th ranked option under the rule "matched with the
highest-ranked attainable option". Options and ranks are `Fin n`, 0-indexed. -/
noncomputable def matchProb {n : ℕ} (P : (Fin n → Bool) → ℝ) (R : Equiv.Perm (Fin n))
    (r : Fin n) : ℝ :=
  ∑ a : Fin n → Bool,
    if a (R.symm r) = true ∧ ∀ t : Fin n, t < r → a (R.symm t) = false then P a else 0

/-- The expected payoff `U(v|R) = Σ_r f^R_r (v_{s^R_r} + ρ(r))` of display (1), p. 5:
report-independent payoff `v` of the matched option plus report-dependent payoff `ρ` of its rank. -/
noncomputable def payoff {n : ℕ} (v ρ : Fin n → ℝ) (P : (Fin n → Bool) → ℝ)
    (R : Equiv.Perm (Fin n)) : ℝ :=
  ∑ r : Fin n, matchProb P R r * (v (R.symm r) + ρ r)

/-- Condition (3), p. 7, for the ROL `Rt` against the true ROL `1 = (1, 2, …, n)`: for every
`r̄`, the probability of being matched with one of the top `r̄` ranked options is at least as
large under the truth as under `Rt`. `rbar : Fin n` is the page's `r̄ ∈ ⟦1, n⟧` shifted by one,
and `Iic rbar` is the page's rank range `1, …, r̄`. -/
def Condition3 {n : ℕ} (P : (Fin n → Bool) → ℝ) (Rt : Equiv.Perm (Fin n)) : Prop :=
  ∀ rbar : Fin n, 0 ≤ ∑ r ∈ Iic rbar, (matchProb P 1 r - matchProb P Rt r)

end ReportDepSP.Honesty


