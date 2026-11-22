-- Prove2me | Definitions.Def_ZInQHeight
-- name    : ZInQHeight
-- status  : Definition
-- author  : @LG
-- created : 2026-11-21T19:08:58.092844+00:00
-- url     : https://prove2.me/theorems/1a8874a1-d10c-4e09-9de2-eca5e5c84a0a
-- title:
--   Height vocabulary and the six-contact estimate $H$ (Theorem 4.1)
-- statement:
--   This bundle defines the height vocabulary used by the six-contact estimate and the estimate itself (hypothesis $H$, Theorem 4.1 of the manuscript). The logarithmic height is $h(u)=\log\max(|a|,b)$ for $u=a/b$ in lowest terms. The contact set is $\mathcal{C}=\{0,-15,-20,-24,-30,-60\}$. For a finite set of primes $S$, $M_S(u)$ is the product of the primes $p\notin S$ for which some $u-c$ ($c\in\mathcal{C}$) has positive, odd $p$-adic valuation. The constants $F_0=324!$, $D=F_0\cdot 3^{256F_0^4}$, $G_0=116064000000$, $E_0=10(DG_0)^2$, $B_{cm}=D^2 3^{21000D^2}+1$, $C_{cm}=2B_{cm}+4096(1028+5D+84000D^2)$, $Q_R=R^{R E_0}$ and $H_6(R)=2\cdot10^{13}\max(1,C_{cm},Q_R^{17})$ are fixed. The six-contact estimate asserts $h(u)\le H_6(R)\,M_S(u)^{24}$ for every admissible $S,R$ and every $u\notin\mathcal{C}$.
-- source:
--   https://github.com/elliotglazer/diophantine-z-q/blob/964d7dd71f253091dbc5eac793b78cc56d1fcc73/ZInQKernel/Hypotheses/Height.lean#L96-L150

import Mathlib

namespace ZInQ

open scoped BigOperators

/-- The logarithmic height h(a/b) = log max(|a|, b) of a rational in lowest terms. -/
noncomputable def ratHeight (u : ℚ) : ℝ :=
  Real.log (max |(u.num : ℝ)| (u.den : ℝ))

/-- The six contact values. -/
def contactSet : Finset ℚ := {0, -15, -20, -24, -30, -60}

open Classical in
/-- M_S(u): the product of primes p not in S at which some u - c has positive odd p-adic valuation. -/
noncomputable def contactSupport (S : Finset ℕ) (u : ℚ) : ℕ :=
  ∏ p ∈ (∏ c ∈ contactSet, (u - c).num.natAbs).primeFactors with
      p ∉ S ∧ ∃ c ∈ contactSet, 0 < padicValRat p (u - c) ∧ Odd (padicValRat p (u - c)),
    p

noncomputable def heightF0 : ℕ := Nat.factorial 324
noncomputable def heightD : ℕ := heightF0 * 3 ^ (256 * heightF0 ^ 4)
def heightG0 : ℕ := 116064000000
noncomputable def heightE0 : ℕ := 10 * (heightD * heightG0) ^ 2
noncomputable def heightBcm : ℕ := heightD ^ 2 * 3 ^ (21000 * heightD ^ 2) + 1
noncomputable def heightCcm : ℕ := 2 * heightBcm + 4096 * (1028 + 5 * heightD + 84000 * heightD ^ 2)
noncomputable def heightQ (R : ℝ) : ℝ := R ^ (R * heightE0)
noncomputable def heightH6 (R : ℝ) : ℝ :=
  2 * 10 ^ 13 * max 1 (max (heightCcm : ℝ) (heightQ R ^ 17))

/-- Hypothesis H (Theorem 4.1, the six-contact estimate). -/
def SixContactEstimate : Prop :=
  ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → p ≤ 324 → p ∈ S) →
    ∀ R : ℝ, (heightD : ℝ) ≤ R → (∀ p ∈ S, (p : ℝ) ≤ R) → (10 : ℝ) ^ 12 ≤ R →
      ∀ u : ℚ, u ∉ contactSet → ratHeight u ≤ heightH6 R * (contactSupport S u : ℝ) ^ 24

end ZInQ


