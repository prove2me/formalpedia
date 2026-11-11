-- Prove2me | Definitions.Def_StratifyMarkets_DoubleAuction_Submarket
-- name    : StratifyMarkets_DoubleAuction_Submarket
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:53:07.103976+00:00
-- url     : https://prove2.me/theorems/9a519e1b-e956-40b9-87b1-e71c43520dcd
-- title:
--   Inside a submarket: expected counts, super buyer and seller, SuperFP, thresholds, the sets 𝓑, 𝓢 and OneTrade (§4.2)
-- statement:
--   Fix a submarket $[a,b]=[\underline m,\overline m]\subseteq[0,1]$. Following footnote 3, the expected number of buyers with values in $[lo,hi]$ is $\sum_i\Pr[lo\le v_i\le hi]$ and of sellers with costs in $[lo,hi]$ is $\sum_j\Pr[lo\le c_j\le hi]$; "buyers with values above $p$" in the submarket are those in $[p,b]$, "sellers with costs below $p$" those in $[a,p]$.
--
--   The **super buyer** has value $v_{\max}=\max_iv_i$, the **super seller** cost $c_{\min}=\min_jc_j$ (needs $n,m\ge1$). The fixed-price mechanism for the pair $(v_{\max},c_{\min})$ with price $p$ inside $[a,b]$ has gains
--   $$\mathrm{SuperFP}(a,p,b)=\mathbb E_{\mathbf v,\mathbf c}\big[(v_{\max}-c_{\min})\cdot\mathbb 1\{a\le c_{\min}\le p\text{ and }p\le v_{\max}\le b\}\big].$$
--   A **buyer threshold** $\bar t\in[a,b]$ has $\sum_i\Pr[\bar t\le v_i\le b]=1/4$ and a **seller threshold** $\underline t\in[a,b]$ has $\sum_j\Pr[a\le c_j\le\underline t]=1/4$. Let $\mathcal B=\{i:\bar t\le v_i\le b\}$, $\mathcal S=\{j:a\le c_j\le\underline t\}$, $B=|\mathcal B|$, $S=|\mathcal S|$, and
--   $$\mathrm{OneTrade}(\mathcal B,\mathcal S)=\mathbb E\Big[\sum_{i\in\mathcal B,\,j\in\mathcal S}(v_i-c_j)\ \Big|\ B=1\text{ and }S=1\Big].$$
--   For a price $q$ between $\underline t$ and $\bar t$, $\mathbb E_{\mathbf v}[A]=\sum_i\Pr[q\le v_i\le\bar t]$ and $\mathbb E_{\mathbf c}[T]=\sum_j\Pr[\underline t\le c_j\le q]$ are `expBuyersIn q t̄` and `expSellersIn t̲ q`.
--
--   **Formalization Note.** `vmax`, `cmin` use `Finset.univ.sup'`/`inf'` under `[NeZero n]`, `[NeZero m]`; `superFP` is an integral over `I.law` of a bounded measurable integrand. `IsBuyerThreshold I a b t` and `IsSellerThreshold I a b t` are predicates (thresholds exist by continuity when the submarket's expected count is at least $1/4$ but need not be unique). `inRange lo hi x` is the finset `{k | lo ≤ x k ≤ hi}`. `oneTrade I a b tB tS` is the ratio $\mathbb E[\sum_{i\in\mathcal B,j\in\mathcal S}(v_i-c_j)\mathbb 1\{B=1,S=1\}]/\Pr[B=1,S=1]$ (the denominator is at least $9/256$ under the lemmas' hypotheses, (4.21); it is `toReal` of a probability). A **refinement** of $[a,b]$ (Remark 4.19) is a `Stratification` σ with `σ.m 0 = a` and `σ.m (Fin.last σ.N) = b`; its gains are `I.strat σ`.
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), pp. 25, 35, 37–40, footnote 3, (4.19), Remark 4.19 (p. 47)

import Mathlib
import Definitions.Def_StratifyMarkets_DoubleAuction_Instance

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

variable {n m : ℕ}

/-- `Σ_i Pr[lo ≤ v_i ≤ hi]`, the expected number of buyers with values in `[lo, hi]`. Inside a
submarket `[m̲, m̄]` (footnote 3, p. 35) the expected number of buyers with values above a price `p`
is `expBuyersIn p m̄`, the expected number of buyers in the submarket is `expBuyersIn m̲ m̄`, and
`E_𝐯[A] = expBuyersIn q t̄` (p. 42). -/
noncomputable def DAInstance.expBuyersIn (I : DAInstance n m) (lo hi : ℝ) : ℝ :=
  ∑ i, (I.μB i (Set.Icc lo hi)).toReal

/-- `Σ_j Pr[lo ≤ c_j ≤ hi]`, the expected number of sellers with costs in `[lo, hi]`; inside
`[m̲, m̄]` the expected number of sellers with costs below `p` is `expSellersIn m̲ p`, and
`E_𝐜[T] = expSellersIn t̲ q` (p. 42). -/
noncomputable def DAInstance.expSellersIn (I : DAInstance n m) (lo hi : ℝ) : ℝ :=
  ∑ j, (I.μS j (Set.Icc lo hi)).toReal

/-- The value of the super buyer, `v_max = max_i v_i` (p. 25); needs `n ≥ 1`. -/
noncomputable def vmax [NeZero n] (v : Fin n → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty v

/-- The cost of the super seller, `c_min = min_j c_j` (p. 25); needs `m ≥ 1`. -/
noncomputable def cmin [NeZero m] (c : Fin m → ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty c

/-- `SuperFP(m̲, p, m̄) = E_{𝐯,𝐜}[(v_max − c_min) · 1{m̲ ≤ c_min ≤ p and p ≤ v_max ≤ m̄}]` (p. 35):
the fixed-price mechanism with price `p` inside the submarket `[m̲, m̄] = [a, b]` for the
bilateral pair formed by the super buyer and the super seller. -/
noncomputable def DAInstance.superFP [NeZero n] [NeZero m] (I : DAInstance n m) (a p b : ℝ) : ℝ :=
  ∫ x, (if a ≤ cmin x.2 ∧ cmin x.2 ≤ p ∧ p ≤ vmax x.1 ∧ vmax x.1 ≤ b
    then vmax x.1 - cmin x.2 else 0) ∂I.law

/-- `t̄` is a buyer threshold of the submarket `[a, b]` (pp. 37–39): `t̄ ∈ [a, b]` and the expected
number of buyers with values in `[t̄, b]` is `1/4`. -/
def DAInstance.IsBuyerThreshold (I : DAInstance n m) (a b t : ℝ) : Prop :=
  t ∈ Set.Icc a b ∧ I.expBuyersIn t b = 1 / 4

/-- `t̲` is a seller threshold of the submarket `[a, b]` (pp. 37–39): `t̲ ∈ [a, b]` and the expected
number of sellers with costs in `[a, t̲]` is `1/4`. -/
def DAInstance.IsSellerThreshold (I : DAInstance n m) (a b t : ℝ) : Prop :=
  t ∈ Set.Icc a b ∧ I.expSellersIn a t = 1 / 4

/-- The set `{k : lo ≤ x_k ≤ hi}` of agents whose type lies in `[lo, hi]`; `𝓑 = inRange t̄ m̄ 𝐯`
and `𝓢 = inRange m̲ t̲ 𝐜` (p. 39), and `B = |𝓑|`, `S = |𝓢|`. -/
noncomputable def inRange {k : ℕ} (lo hi : ℝ) (x : Fin k → ℝ) : Finset (Fin k) :=
  Finset.univ.filter (fun i => lo ≤ x i ∧ x i ≤ hi)

/-- `OneTrade(𝓑, 𝓢) = E_{𝐯,𝐜}[Σ_{i ∈ 𝓑, j ∈ 𝓢} (v_i − c_j) | B = 1 and S = 1]` (p. 40) inside the
submarket `[a, b]` with buyer threshold `tB = t̄` and seller threshold `tS = t̲`, written as the ratio
`E[Σ_{i ∈ 𝓑, j ∈ 𝓢} (v_i − c_j) · 1{B = 1, S = 1}] / Pr[B = 1 and S = 1]` (the denominator is at
least `9/256` under the hypotheses of Lemmas 4.16–4.18, (4.21)). -/
noncomputable def DAInstance.oneTrade (I : DAInstance n m) (a b tB tS : ℝ) : ℝ :=
  (∫ x, (if (inRange tB b x.1).card = 1 ∧ (inRange a tS x.2).card = 1 then
      ∑ i ∈ inRange tB b x.1, ∑ j ∈ inRange a tS x.2, (x.1 i - x.2 j) else 0) ∂I.law) /
    (I.law {x | (inRange tB b x.1).card = 1 ∧ (inRange a tS x.2).card = 1}).toReal

end StratifyMarkets.DoubleAuction


