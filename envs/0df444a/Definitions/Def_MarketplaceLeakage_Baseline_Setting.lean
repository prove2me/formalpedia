-- Prove2me | Definitions.Def_MarketplaceLeakage_Baseline_Setting
-- name    : MarketplaceLeakage_Baseline_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:59.005462+00:00
-- url     : https://prove2.me/theorems/b298d957-9143-4a26-baa6-6890c7ab0bb7
-- title:
--   §3.1, §4, pp. 5–9 — the baseline leakage game: uniform switching costs G, the seller's reduced profit (1), seller-optimal direct prices, leakage, the marketplace's profit and the equilibrium of (3)
-- statement:
--   This file sets up the baseline model of Hagiu and Wright, *Marketplace Leakage* (§3.1 and §4).
--
--   **Players and primitives.** A marketplace $M$, a seller $S$ and a unit mass of buyers who each want one unit of $S$'s product. Every buyer values the product at $v$; $S$'s marginal cost is $c$, with $c<v$. $S$ sells either through $M$, paying a fee $f$ per transaction, or through its direct channel, which charges no fee. A buyer who buys directly bears a switching cost $s$, distributed according to the uniform distribution on $[0,\mu]$ with $\mu>0$:
--   $$G(s)=\begin{cases}0 & s<0,\\ s/\mu & 0\le s\le \mu,\\ 1 & s>\mu.\end{cases}$$
--
--   **The reduced game.** Given Lemma 1 of the paper, $S$ prices at $p_m=v$ on $M$ and only chooses its direct price $p_d\le v$. A buyer with switching cost $s$ buys directly iff $s\le v-p_d$, so the share of buyers who buy directly — the **leakage** — is $G(v-p_d)$. The seller's profit at fee $f$ and direct price $p_d$ is (1):
--   $$\pi_f(p_d)=(p_d-c)\,G(v-p_d)+(v-c-f)\,\bigl(1-G(v-p_d)\bigr).$$
--   A direct price $p_d$ is **seller-optimal at $f$** if $p_d\le v$ and $\pi_f(p)\le\pi_f(p_d)$ for every $p\le v$. When $M$ charges $f$ and $S$ answers with $p_d$, the marketplace earns
--   $$\Pi=f\,\bigl(1-G(v-p_d)\bigr).$$
--
--   **Equilibrium.** A pair $(f,p_d)$ is an **equilibrium outcome** of the reduced game (3) if
--   1. the fee is feasible, $f\le v-c$;
--   2. $p_d$ is seller-optimal at $f$;
--   3. for every feasible fee $f'\le v-c$ and every seller-optimal direct price $p_d'$ at $f'$, $f'(1-G(v-p_d'))\le f(1-G(v-p_d))$.
--
--   These are the objects about which Proposition 1 and its supporting displays (4)–(6) are stated.
--
--   **Formalization Note.** All parameters are real numbers. $G$ is the clamped uniform CDF $\min(\max(s/\mu,0),1)$; it is only meaningful for $\mu>0$, which every theorem assumes. Seller-optimality is a predicate (no closed form is built in), and the marketplace's problem is an optimality predicate over the game's feasible choices, not a supremum. Negative fees are feasible, as in (3); the paper's conclusion $f>0$ (Lemma 1) is not imposed. The predicate allows any seller-optimal response at a deviating fee; since the seller's optimum is unique at every fee, no tie-breaking convention is involved.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript dated March 2023 (sha256 cb89cc00…3c98a6; published in Management Science, doi:10.1287/mnsc.2023.4757), pp. 5–9, §3.1 (model, timing p. 6), §4 (buyer choice and Lemma 1 p. 7, (1) p. 7, Π(f) and (3) p. 8, uniform G p. 9)

import Mathlib

namespace MarketplaceLeakage.Baseline

/-!
# Hagiu & Wright, *Marketplace Leakage*, §3.1 and §4 (pp. 5–9): the reduced baseline game

A marketplace `M`, a seller `S` with product value `v` and marginal cost `c` (`c < v`, p. 5), and a
unit mass of buyers. A buyer who buys directly from `S` bears a switching cost `s`, drawn from the
uniform distribution `G` on `[0, μ]`, `μ > 0` (p. 9). Given Lemma 1 (p. 7), `S` sells on `M` at
`p_m = v` and only chooses its direct price `p_d ≤ v`; `M` chooses its per-transaction fee
`f ≤ v − c` ((3), p. 8). All parameters are real numbers; `μ` is written `μ`.
-/

/-- The uniform switching-cost distribution of p. 9: `G(s) = s/μ` on `[0, μ]`, `G(s) = 0` for
`s < 0`, `G(s) = 1` for `s > μ` (the clamped CDF). Meaningful for `μ > 0`. -/
noncomputable def G (μ s : ℝ) : ℝ := min (max (s / μ) 0) 1

/-- The seller's reduced profit (1), p. 7, at fee `f` and direct price `pd` (with `p_m = v`):
`π = (p_d − c) G(v − p_d) + (v − c − f)(1 − G(v − p_d))`. -/
noncomputable def sProfit (v c μ f pd : ℝ) : ℝ :=
  (pd - c) * G μ (v - pd) + (v - c - f) * (1 - G μ (v - pd))

/-- `pd` is a profit-maximizing direct price of `S` at fee `f`: `pd ≤ v` and `pd` maximizes (1)
over all direct prices `p ≤ v` (p. 7–8, "S's profit maximizing price p*_d(f)"). -/
def IsSOpt (v c μ f pd : ℝ) : Prop :=
  pd ≤ v ∧ ∀ p : ℝ, p ≤ v → sProfit v c μ f p ≤ sProfit v c μ f pd

/-- Leakage at direct price `pd`: the share `G(v − p_d)` of buyers who buy directly. -/
noncomputable def leakage (v μ pd : ℝ) : ℝ := G μ (v - pd)

/-- The marketplace's realized profit `Π = f (1 − G(v − p_d))` when it charges `f` and `S`
answers with `pd` (p. 8). -/
noncomputable def MProfit (v μ f pd : ℝ) : ℝ := f * (1 - G μ (v - pd))

/-- `(f, pd)` is an equilibrium outcome of the reduced game (3), p. 8: the fee is feasible
(`f ≤ v − c`), `pd` is S-optimal at `f`, and no feasible fee `f'`, followed by any S-optimal
response `pd'` at `f'`, gives `M` a strictly larger profit. -/
def IsEq (v c μ f pd : ℝ) : Prop :=
  f ≤ v - c ∧ IsSOpt v c μ f pd ∧
    ∀ f' pd' : ℝ, f' ≤ v - c → IsSOpt v c μ f' pd' → MProfit v μ f' pd' ≤ MProfit v μ f pd

end MarketplaceLeakage.Baseline


