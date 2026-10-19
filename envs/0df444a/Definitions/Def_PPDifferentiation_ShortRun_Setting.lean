-- Prove2me | Definitions.Def_PPDifferentiation_ShortRun_Setting
-- name    : PPDifferentiation_ShortRun_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T12:58:31.094982+00:00
-- url     : https://prove2.me/theorems/1d0a4b5f-39f7-4c4d-8194-740654517550
-- title:
--   §3, §4, §6 and Appendix A — quadratic-misfit pricing game and stage payoffs
-- statement:
--   Consumers are uniformly distributed on $[0,1]$ and must buy from one of two firms at real positions $x_i,x_j$. A consumer at $x$ incurs misfit $t(x-x_i)^2$, where $t>0$. The advantage of firm $i$ at equal prices is
--
--   $$a_i(x)=t(x-x_j)^2-t(x-x_i)^2.$$
--
--   With PP by both firms, firm $i$ earns $\int_0^1\max\{0,a_i(x)\}\,dx$. With only firm $j$ using PP, firm $i$ first sets one price $p$; its share is the measure of consumers satisfying $p<a_i(x)$, and its profit is $p$ times that share. The targeting follower earns $\int_0^1\max\{0,p-a_i(x)\}\,dx$. A leader price is optimal when no real alternative gives greater profit.
--
--   With uniform prices $p_i,p_j$, firm $i$ serves consumers with $p_i-p_j<a_i(x)$ and half of consumers tied at equality. Its profit is price times share. The definition includes the price Nash equilibrium and the positioning equilibria under uniform, both-personalized, and asymmetric pricing. The stage-1 payoff functions evaluate those primitive gross profits at the source's subgame positions and subtract $F$ exactly for firms using PP.
--
--   **Formalization Note** Positions and prices range over all real numbers. The model assumes complete market coverage, so the reservation value cancels. Ties under uniform pricing are split equally; at an asymmetric tie the targeted firm serves the consumer. When locations coincide, an asymmetric leader can have multiple optimal prices. The asymmetric positioning predicate therefore asks for an optimal continuation after each deviation. Implementation cost is sunk when firms position and price.
-- source:
--   Li, Wang, Nault, Is Personalized Pricing Profitable When Firms Can Differentiate?, working paper, SSRN abstract 3881900 (version of August 3, 2021), §3, pp. 5–8; §4, pp. 8–9; §6, pp. 23–25; Appendix A, p. 33, proof of Lemma 1

import Mathlib
import Definitions.Def_PPDifferentiation_ShortRun_Game
import Definitions.Def_PPDifferentiation_Costless_Setting

open MeasureTheory

namespace PPDifferentiation.ShortRun

/-- Equilibrium in the uniform-pricing position subgame, including every price equilibrium after a deviation. -/
def IsPosEqUU (t xA xB pA pB : ℝ) : Prop :=
  PPDifferentiation.Costless.IsPriceNE t xA xB pA pB ∧
  (∀ x qA qB : ℝ, PPDifferentiation.Costless.IsPriceNE t x xB qA qB →
    PPDifferentiation.Costless.uProf t x xB qA qB ≤ PPDifferentiation.Costless.uProf t xA xB pA pB) ∧
  (∀ x qA qB : ℝ, PPDifferentiation.Costless.IsPriceNE t xA x qA qB →
    PPDifferentiation.Costless.uProf t x xA qB qA ≤ PPDifferentiation.Costless.uProf t xB xA pB pA)

/-- The targeting follower at `xF` and uniform leader at `xL` play a position equilibrium. -/
def IsPosEqAS (t xF xL : ℝ) : Prop :=
  (∃ p : ℝ, PPDifferentiation.Costless.IsLeaderOpt t xL xF p) ∧
  (∀ p₀ x : ℝ, PPDifferentiation.Costless.IsLeaderOpt t xL xF p₀ →
    ∃ p : ℝ, PPDifferentiation.Costless.IsLeaderOpt t xL x p ∧
      PPDifferentiation.Costless.followProf t xL x p ≤ PPDifferentiation.Costless.followProf t xL xF p₀) ∧
  (∀ p₀ x : ℝ, PPDifferentiation.Costless.IsLeaderOpt t xL xF p₀ →
    ∃ p : ℝ, PPDifferentiation.Costless.IsLeaderOpt t x xF p ∧
      PPDifferentiation.Costless.leadProf t x xF p ≤ PPDifferentiation.Costless.leadProf t xL xF p₀)

/-- Firm A's net stage-one payoff, evaluated at the subgame positions. -/
noncomputable def stage1A (t F p₀ p₁ : ℝ) : PPChoice → PPChoice → ℝ
  | .PP, .PP => PPDifferentiation.Costless.profPP t (1/4) (3/4) - F
  | .PP, .U => PPDifferentiation.Costless.followProf t (1/2) (-1/2) p₀ - F
  | .U, .PP => PPDifferentiation.Costless.leadProf t (1/2) (3/2) p₁
  | .U, .U => PPDifferentiation.Costless.uProf t (-1/4) (5/4) (3*t/2) (3*t/2)

/-- Firm B's net stage-one payoff, evaluated at the subgame positions. -/
noncomputable def stage1B (t F p₀ p₁ : ℝ) : PPChoice → PPChoice → ℝ
  | .PP, .PP => PPDifferentiation.Costless.profPP t (3/4) (1/4) - F
  | .PP, .U => PPDifferentiation.Costless.leadProf t (1/2) (-1/2) p₀
  | .U, .PP => PPDifferentiation.Costless.followProf t (1/2) (3/2) p₁ - F
  | .U, .U => PPDifferentiation.Costless.uProf t (5/4) (-1/4) (3*t/2) (3*t/2)

end PPDifferentiation.ShortRun


