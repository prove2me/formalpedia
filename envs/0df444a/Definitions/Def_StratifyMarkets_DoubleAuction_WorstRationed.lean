-- Prove2me | Definitions.Def_StratifyMarkets_DoubleAuction_WorstRationed
-- name    : StratifyMarkets_DoubleAuction_WorstRationed
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:54:58.076476+00:00
-- url     : https://prove2.me/theorems/169f79ea-1784-43a1-a9af-7ad1f9501b51
-- title:
--   The worst-rationed fixed-price rule, globally and inside a submarket, and the double-auction gains Strat of a stratification (§2.2.1)
-- statement:
--   Fix a price $p$. A buyer is **eligible** if $v_i\ge p$ and a seller if $c_j\le p$; let $B_p$, $S_p$ be the numbers of eligible buyers and sellers. The **worst-rationed rule** trades $k=\min\{B_p,S_p\}$ units while minimizing gains from trade: if $S_p<B_p$ the $S_p$ eligible buyers with the lowest values trade with all eligible sellers; if $S_p>B_p$ the $B_p$ eligible sellers with the highest costs trade with all eligible buyers; if equal, all trade. Its realized gains are the sum of the selected buyers' values minus the sum of the selected sellers' costs, and
--   $$\mathrm{WorstRationed}(p)=\mathbb E_{\mathbf v,\mathbf c}\Big[\sum_{i\in\hat{\mathcal B}_p}v_i-\sum_{j\in\hat{\mathcal S}_p}c_j\Big].$$
--   Inside a submarket $[a,b]$ with price $p\in[a,b]$, the same rule runs on the buyers with $p\le v_i\le b$ and the sellers with $a\le c_j\le p$; its expected gains are $\mathrm{WorstRationed}(a,p,b)$. A stratification (Definition 2.3) in a double auction runs this rule in every submarket, and its gains are
--   $$\mathrm{Strat}=\sum_{k=1}^N\mathrm{WorstRationed}(m_{k-1},p_k,m_k).$$
--
--   **Formalization Note.** `worstRationedGains EB ES v c` is the minimum, over sets $T_B\subseteq EB$, $T_S\subseteq ES$ of size $k=\min(|EB|,|ES|)$, of $\sum_{T_B}v_i-\sum_{T_S}c_j$ (`Finset.inf'` over `powersetCard`); this is exactly the sum of the $k$ smallest eligible values minus the sum of the $k$ largest eligible costs, independent of tie-breaking. `worstRationed p` uses the eligible sets `{i | p ≤ v i}`, `{j | c j ≤ p}`; `worstRationedIn a p b` uses `{i | p ≤ v i ≤ b}`, `{j | a ≤ c j ≤ p}` (closed submarkets, Remark 2.4); both are integrals over `I.law` of bounded measurable functions. `DAInstance.strat I σ = Σ k : Fin σ.N, worstRationedIn (σ.m k.castSucc) (σ.p k) (σ.m k.succ)`.
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), p. 13, §2.2.1; footnote 3, p. 35

import Mathlib
import Definitions.Def_StratifyMarkets_DoubleAuction_Instance
import Definitions.Def_StratifyMarkets_DoubleAuction_Stratification

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

/-- Realized gains of the worst-rationed rule (§2.2.1, p. 13) when the eligible buyers are `EB` and
the eligible sellers are `ES`: with `k = min(|EB|, |ES|)` trades, the rule trades as many items as
possible while minimizing the gains from trade, so its gains are the minimum, over `k`-element sets
`T_B ⊆ EB` of buyers and `T_S ⊆ ES` of sellers, of `Σ_{i ∈ T_B} v_i − Σ_{j ∈ T_S} c_j`; that is,
the sum of the `k` smallest eligible values minus the sum of the `k` largest eligible costs. -/
noncomputable def worstRationedGains {n m : ℕ} (EB : Finset (Fin n)) (ES : Finset (Fin m))
    (v : Fin n → ℝ) (c : Fin m → ℝ) : ℝ :=
  ((EB.powersetCard (min EB.card ES.card)) ×ˢ (ES.powersetCard (min EB.card ES.card))).inf'
    ((Finset.powersetCard_nonempty.mpr (min_le_left _ _)).product
      (Finset.powersetCard_nonempty.mpr (min_le_right _ _)))
    (fun T => ∑ i ∈ T.1, v i - ∑ j ∈ T.2, c j)

/-- `WorstRationed(p) = E_{𝐯,𝐜}[Σ_{i ∈ B̂_p} v_i − Σ_{j ∈ Ŝ_p} c_j]` (p. 13): the worst-rationed
rule at the global price `p`, with eligible buyers `{i : v_i ≥ p}` and eligible sellers
`{j : c_j ≤ p}`. -/
noncomputable def DAInstance.worstRationed {n m : ℕ} (I : DAInstance n m) (p : ℝ) : ℝ :=
  ∫ x, worstRationedGains (Finset.univ.filter (fun i => p ≤ x.1 i))
    (Finset.univ.filter (fun j => x.2 j ≤ p)) x.1 x.2 ∂I.law

/-- `WorstRationed(a, p, b)` (p. 13 and footnote 3, p. 35): the worst-rationed rule with price `p`
restricted to the submarket `[a, b]`; eligible buyers are those with `p ≤ v_i ≤ b`, eligible sellers
those with `a ≤ c_j ≤ p` (closed submarkets, Remark 2.4). -/
noncomputable def DAInstance.worstRationedIn {n m : ℕ} (I : DAInstance n m) (a p b : ℝ) : ℝ :=
  ∫ x, worstRationedGains (Finset.univ.filter (fun i => p ≤ x.1 i ∧ x.1 i ≤ b))
    (Finset.univ.filter (fun j => a ≤ x.2 j ∧ x.2 j ≤ p)) x.1 x.2 ∂I.law

/-- Double-auction gains of a stratification running the worst-rationed rule in each submarket
(§2.2.1, p. 13): `Strat = Σ_{k=1}^{N} WorstRationed(m_{k−1}, p_k, m_k)`. -/
noncomputable def DAInstance.strat {n m : ℕ} (I : DAInstance n m) (σ : Stratification) : ℝ :=
  ∑ k : Fin σ.N, I.worstRationedIn (σ.m k.castSucc) (σ.p k) (σ.m k.succ)

end StratifyMarkets.DoubleAuction


