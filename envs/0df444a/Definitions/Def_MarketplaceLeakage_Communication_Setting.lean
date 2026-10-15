-- Prove2me | Definitions.Def_MarketplaceLeakage_Communication_Setting
-- name    : MarketplaceLeakage_Communication_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:46.587986+00:00
-- url     : https://prove2.me/theorems/6690fc53-8921-4591-be66-3b5756c0e183
-- title:
--   §4, §5.2, pp. 7–15 — the leakage game with uniform switching costs, and the communication-ban game: seller options, ban value, Π_H, Π_L, η*
-- statement:
--   This file sets up the two games compared in §5.2 of Hagiu and Wright, *Marketplace Leakage*.
--
--   **Primitives.** A single seller $S$ sells a product of value $v$ and marginal cost $c<v$ to a unit mass of buyers, through a marketplace $M$ that charges a fee $f$ per transaction, or directly at a price $p_d$. A buyer who buys directly bears a switching cost $s$, distributed according to the uniform distribution
--   $$G(s)=\begin{cases}0 & s<0,\\ s/\mu & 0\le s\le \mu,\\ 1 & s>\mu,\end{cases}\qquad \mu>0 .$$
--
--   **Baseline (communication allowed).** Given the fee $f$ and with the on-platform price fixed at $p_m=v$ (Lemma 1 of the paper), the seller chooses $p_d\le v$ to maximize its profit (1),
--   $$\pi(p_d)=(p_d-c)\,G(v-p_d)+(v-c-f)\,\bigl(1-G(v-p_d)\bigr).$$
--   A price $p_d$ is *seller-optimal* at $f$ if $p_d\le v$ and $\pi(p_d)\ge \pi(p)$ for every $p\le v$. The marketplace earns $\Pi(f)=f\,(1-G(v-p_d))$. A pair $(f,p_d)$ is an *equilibrium* of (3) if $f\le v-c$, $p_d$ is seller-optimal at $f$, and no other feasible fee $f'\le v-c$ together with a seller-optimal response $p_d'$ gives the marketplace more. A number $P$ is the *baseline value* $\Pi^*$ at scale $\mu$ if it is the marketplace's profit at some equilibrium.
--
--   **Communication ban.** Each buyer values the product at $v$ with prior probability $q\in(0,1)$ and at $0$ otherwise. Under a ban, leakage is impossible, and a buyer learns their valuation only with probability $\eta\le 1$. The seller has two options:
--   1. the high price $p_m=v$, selling to the fraction $\eta q$ of informed high-value buyers, with profit $\eta q\,(v-c-f)$;
--   2. the low price $p_m=qv$, also selling to the $1-\eta$ uninformed buyers, with profit $(1-\eta+\eta q)(qv-c-f)$.
--
--   The seller takes the high option exactly when it pays strictly more (ties go to the low option), and lists on $M$ exactly when the chosen option pays at least $0$. The marketplace's revenue at fee $f$ is $f\eta q$ or $f(1-\eta+\eta q)$ accordingly, and $0$ if the seller does not list. A number $V$ is the *ban value* if it is the greatest revenue over all fees $f\in\mathbb R$ (attained).
--
--   **Named formulas** (p. 15 and p. 38):
--   $$\Pi_H(\eta)=\eta q(v-c),\qquad \Pi_L(\eta)=(1-\eta+\eta q)\Bigl(\frac{(1-(2-q)\eta)qv}{1-\eta}-c\Bigr),$$
--   $$\eta^*=\frac{qv(2-q)-c-q\sqrt{(1-q)v(v-c)}}{qv\,(3(1-q)+q^2)-c}.$$
--
--   **Preferences.** With communication allowed the marketplace earns $q\Pi^*$. It *prefers to ban* when the ban value strictly exceeds $q\Pi^*$, and *prefers to allow* when the ban value is strictly below $q\Pi^*$.
--
--   These objects are the vocabulary of Proposition 3 and of its proof in §8.4.
--
--   **Formalization Note.** The ban value is defined from the seller's option choice and listing rule, as a maximum over all real fees; it is not defined as $\max\{\Pi_H,\Pi_L\}$, which is a theorem. $\Pi_L$ divides by $1-\eta$ and is only meaningful for $\eta<1$ (Lean's convention $x/0=0$ applies at $\eta=1$). In Lean, $\Pi^*$ is written `PiStar` and the uniform CDF is the clamped `min (max (s/μ) 0) 1`.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript dated March 2023 (sha256 cb89c…98a6; published in Management Science, doi:10.1287/mnsc.2023.4757), pp. 5–9, §3.1, (1), (3); pp. 14–15, §5.2; p. 38, §8.4 (η*)

import Mathlib
import Definitions.Def_MarketplaceLeakage_Baseline_Setting

namespace MarketplaceLeakage.Communication

/-! # The leakage game with and without a communication ban

Hagiu–Wright, *Marketplace Leakage* (authors' manuscript, March 2023), §3.1, §4 and §5.2,
pp. 5–10 and 14–15. Primitives are plain reals: the buyers' value `v`, the seller's marginal
cost `c`, the uniform switching-cost scale `μ`, the prior probability `q` that a buyer values
the product at `v`, the probability `η` that a buyer learns their valuation under a ban, the
marketplace's fee `f` and the seller's direct price `pd`. -/

/-! ## Baseline (communication allowed), pp. 7–10 -/

/-- `P` is the baseline equilibrium profit `Π*` of (3) under the uniform `G` with scale `μ`. -/
def IsBaselineValue (v c μ P : ℝ) : Prop :=
  ∃ f pd : ℝ, MarketplaceLeakage.Baseline.IsEq v c μ f pd ∧ P = MarketplaceLeakage.Baseline.MProfit v μ f pd

/-! ## The communication ban, §5.2, pp. 14–15 -/

/-- The seller's profit from the high-price option `p_m = v`: it sells to the fraction `ηq`
of buyers who learn that they value the product at `v`, earning `ηq (v − c − f)`. -/
def highPay (v c q η f : ℝ) : ℝ := η * q * (v - c - f)

/-- The seller's profit from the low-price option `p_m = qv`: it also sells to the `1 − η`
uninformed buyers, earning `(1 − η + ηq)(qv − c − f)`. -/
def lowPay (v c q η f : ℝ) : ℝ := (1 - η + η * q) * (q * v - c - f)

/-- The marketplace's revenue under a ban at fee `f`. The seller takes the high-price option
iff it pays strictly more than the low-price option (ties go to the low-price option,
"Otherwise, S chooses the second", p. 15), and lists iff the chosen option pays `≥ 0`.
The marketplace earns `f` per transaction: `f ηq` or `f (1 − η + ηq)`, and `0` if the
seller does not list. -/
noncomputable def banRev (v c q η f : ℝ) : ℝ :=
  if lowPay v c q η f < highPay v c q η f then
    (if 0 ≤ highPay v c q η f then f * (η * q) else 0)
  else
    (if 0 ≤ lowPay v c q η f then f * (1 - η + η * q) else 0)

/-- `V` is the marketplace's profit after banning communication: the maximum, attained, of
its revenue over all fees `f ∈ ℝ`. -/
def IsBanValue (v c q η V : ℝ) : Prop := IsGreatest (Set.range (banRev v c q η)) V

/-- `Π_H(η) = ηq(v − c)` (p. 15). -/
def PiH (v c q η : ℝ) : ℝ := η * q * (v - c)

/-- `Π_L(η) = (1 − η + ηq)((1 − (2 − q)η) qv/(1 − η) − c)` (p. 15); meaningful for `η < 1`. -/
noncomputable def PiL (v c q η : ℝ) : ℝ :=
  (1 - η + η * q) * ((1 - (2 - q) * η) * q * v / (1 - η) - c)

/-- The printed threshold `η* = (qv(2 − q) − c − q√((1 − q)v(v − c)))/(qv(3(1 − q) + q²) − c)`
(§8.4, p. 38). -/
noncomputable def etaStar (v c q : ℝ) : ℝ :=
  (q * v * (2 - q) - c - q * Real.sqrt ((1 - q) * v * (v - c))) /
    (q * v * (3 * (1 - q) + q ^ 2) - c)

/-- The marketplace strictly prefers to ban communication: its ban value exceeds `q Π*`,
its expected profit when communication is allowed. -/
def PrefersBan (v c q η PiStar : ℝ) : Prop :=
  ∃ V : ℝ, IsBanValue v c q η V ∧ q * PiStar < V

/-- The marketplace strictly prefers to allow communication: its ban value is below `q Π*`. -/
def PrefersAllow (v c q η PiStar : ℝ) : Prop :=
  ∃ V : ℝ, IsBanValue v c q η V ∧ V < q * PiStar

end MarketplaceLeakage.Communication


