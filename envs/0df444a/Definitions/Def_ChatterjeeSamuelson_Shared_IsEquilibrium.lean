-- Prove2me | Definitions.Def_ChatterjeeSamuelson_Shared_IsEquilibrium
-- name    : ChatterjeeSamuelson_Shared_IsEquilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:45:35.347529+00:00
-- url     : https://prove2.me/theorems/a5901373-ac25-466d-9c62-62ab112e5e99
-- title:
--   Bayesian (Nash) equilibrium of the sealed-offer bargaining game
-- statement:
--   Let the seller's reservation price range over $[\underline v_s, \bar v_s]$ and the buyer's over $[\underline v_b, \bar v_b]$, let $\mu_b$ be the buyer's belief about $v_s$ and $\mu_s$ the seller's belief about $v_b$, and fix $k$. A pair of offer strategies $(S, B)$ is an **equilibrium** if
--
--   1. for every buyer value $v \in [\underline v_b, \bar v_b]$ and every real offer $b$, $\pi_b(b, v) \le \pi_b(B(v), v)$;
--   2. for every seller value $v \in [\underline v_s, \bar v_s]$ and every real ask $s$, $\pi_s(s, v) \le \pi_s(S(v), v)$.
--
--   That is, each player's offer is a best response to the opponent's strategy for each of its possible reservation prices; the paper calls such a pair a Nash (or Bayesian) equilibrium.
--
--   This definition is shared by two missions of this series: 1 (the linked differential equations, Theorem 2 and its proof, p. 840 [PDF 6]) and 2 (the linear equilibrium of the uniform example, Example 1(a), p. 842 [PDF 8]).
--
--   **Formalization Note** Deviations range over all real numbers, as in the paper's "for all b". Values of $S$ and $B$ outside the value intervals do not enter the conditions.
-- source:
--   Chatterjee & Samuelson, Bargaining under Incomplete Information, Oper. Res. 31(5) (1983), p. 839 [PDF 5], §1, definition of best response and of Nash (Bayesian) equilibrium

import Mathlib
import Definitions.Def_ChatterjeeSamuelson_Shared_buyerProfit
import Definitions.Def_ChatterjeeSamuelson_Shared_sellerProfit

open MeasureTheory Set

namespace ChatterjeeSamuelson.Shared

/-- Nash (Bayesian) equilibrium of the sealed-offer bargaining game (Chatterjee &
Samuelson, *Bargaining under Incomplete Information*, Oper. Res. 31(5) 1983, §1, p. 839
[PDF 5], unnumbered text: "the seller's offer s* is a best response against B( ) if
π_s(s*, v_s) ≥ π_s(s, v_s), for all s. Similarly, a buyer holding v_b makes offer b* that
is a best response against S( ) if π_b(b*, v_b) ≥ π_b(b, v_b), for all b. Then player i
employs a best response strategy if for each v_i his offer is a best response against his
opponent's strategy. A pair of best response offer strategies constitute a Nash (or
Bayesian) equilibrium.").

The seller's values range over `[loS, hiS]` (= `[v̲_s, v̄_s]`), the buyer's over
`[loB, hiB]`; `μb` is the buyer's belief about `v_s`, `μs` the seller's belief about
`v_b`. `(S, B)` is an equilibrium if every buyer value `v ∈ [loB, hiB]` weakly prefers
`B v` to every real offer `b`, and every seller value `v ∈ [loS, hiS]` weakly prefers
`S v` to every real ask `s`.

*Formalization Note.* Deviations range over all of `ℝ`, as in "for all b"; values of `S`,
`B` outside the value intervals play no role in the best-response conditions. -/
def IsEquilibrium (k : ℝ) (μb μs : Measure ℝ) (loS hiS loB hiB : ℝ) (S B : ℝ → ℝ) : Prop :=
  (∀ v ∈ Icc loB hiB, ∀ b : ℝ, buyerProfit k μb S b v ≤ buyerProfit k μb S (B v) v) ∧
    (∀ v ∈ Icc loS hiS, ∀ s : ℝ, sellerProfit k μs B s v ≤ sellerProfit k μs B (S v) v)

end ChatterjeeSamuelson.Shared


