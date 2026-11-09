-- Prove2me | Definitions.Def_MatchingGFT_TightE_CappedExp
-- name    : MatchingGFT_TightE_CappedExp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:56.962937+00:00
-- url     : https://prove2.me/theorems/9ee99918-a0fa-4221-aeb9-e90a42360d43
-- title:
--   Capped-exponential laws and the knapsack market (L, N)
-- statement:
--   $v=\min\{X,L\}$, $c=L-\min\{Y,L\}$ with $X,Y$ independent $\mathrm{Exp}(1)$; $g_L$, $p_L^S$, $p_L^B$ as expectations of positive parts; $d_L=(1+1/L)p_L^S$; and the market $(L,N)$ with $N$ capped-exponential edges and one deterministic edge $e_0$, $\mathcal F_{L,N}=2^{\{e_1,\dots,e_N\}}\cup\{\{e_0\}\}$.
-- source:
--   Xiaohui Bei, Wenhao Wu, Shengwei Zhou, STOC 2027 submission #465 (October 2026), §4.1–4.2, PDF pp. 19, 21

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_MatchingGFT_TightE_Quantile

open MeasureTheory ProbabilityTheory

namespace MatchingGFT.TightE

/-- The law of `v = min{X, L}`, `X ∼ Exp(1)` (PDF p. 19). -/
noncomputable def cappedBuyerLaw (L : ℝ) : Measure ℝ :=
  (expMeasure 1).map fun x => min x L

/-- The law of `c = L - min{Y, L}`, `Y ∼ Exp(1)` (PDF p. 19). -/
noncomputable def cappedSellerLaw (L : ℝ) : Measure ℝ :=
  (expMeasure 1).map fun y => L - min y L

/-- The joint law of the independent pair `(v, c)`. -/
noncomputable def cappedPairLaw (L : ℝ) : Measure (ℝ × ℝ) :=
  (cappedBuyerLaw L).prod (cappedSellerLaw L)

/-- `g_L = E[(v - c)⁺]` (PDF p. 19). -/
noncomputable def cappedG (L : ℝ) : ℝ :=
  ∫ p, max (p.1 - p.2) 0 ∂cappedPairLaw L

/-- `p_L^S = E[(φ(v) - c)⁺]` (PDF p. 19), with `φ` the ironed virtual value of the buyer law. The
positive part is taken in `EReal`, so `φ(v) = -∞` gives `0`. -/
noncomputable def cappedPS (L : ℝ) : ℝ :=
  ∫ p, (max (virtualValue (cappedBuyerLaw L) p.1 - ((p.2 : ℝ) : EReal)) 0).toReal ∂cappedPairLaw L

/-- `p_L^B = E[(v - ψ(c))⁺]` (PDF p. 19), with `ψ` the ironed virtual cost of the seller law. The
positive part is taken in `EReal`, so `ψ(c) = +∞` gives `0`. -/
noncomputable def cappedPB (L : ℝ) : ℝ :=
  ∫ p, (max (((p.1 : ℝ) : EReal) - virtualCost (cappedSellerLaw L) p.2) 0).toReal ∂cappedPairLaw L

/-- `d_L = (1 + 1/L) p_L^S` (PDF p. 21). -/
noncomputable def cappedD (L : ℝ) : ℝ := (1 + 1 / L) * cappedPS L

/-- The market `(L, N)` of §4.2 (PDF p. 21). Agents `0, …, N`; the edges are `eₖ = (k, k)`. The edge `e₀`
has deterministic buyer value `N d_L` and seller cost `0`; `e₁, …, e_N` carry independent capped
exponentials; `ℱ_{L,N} = 2^{{e₁,…,e_N}} ∪ {{e₀}}`. -/
noncomputable def cappedMarket (L : ℝ) (N : ℕ) : Market (Fin (N + 1)) (Fin (N + 1)) where
  edges := Finset.univ.image fun k => (k, k)
  family :=
    ((Finset.univ.filter fun k : Fin (N + 1) => k ≠ 0).image fun k => (k, k)).powerset ∪ {{(0, 0)}}
  buyerLaw := fun k => if k = 0 then Measure.dirac ((N : ℝ) * cappedD L) else cappedBuyerLaw L
  sellerLaw := fun k => if k = 0 then Measure.dirac 0 else cappedSellerLaw L

end MatchingGFT.TightE


