-- Prove2me | Definitions.Def_StratifyMarkets_DoubleAuction_Prices
-- name    : StratifyMarkets_DoubleAuction_Prices
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:53:07.235983+00:00
-- url     : https://prove2.me/theorems/161fc942-be7b-4d8c-a2d7-eb825060f7fa
-- title:
--   Expected eligible counts, balanced, excess-supply and excess-demand prices, and total surpluses ((4.1), (4.2))
-- statement:
--   For a price $p$, the expected numbers of eligible buyers and sellers are $\mathbb E_{\mathbf v}[B_p]=\sum_i\Pr[v_i\ge p]$ and $\mathbb E_{\mathbf c}[S_p]=\sum_j\Pr[c_j\le p]$. A **balanced price** $\tilde p\in[0,1]$ satisfies
--   $$\lambda:=\mathbb E_{\mathbf v}[B_{\tilde p}]=\mathbb E_{\mathbf c}[S_{\tilde p}]\qquad(4.1);$$
--   the common value $\lambda$ is the same for every balanced price. When $\lambda\ge4$, an **excess-supply price** $\bar p$ and an **excess-demand price** $\underline p$ in $[0,1]$ satisfy
--   $$\mathbb E_{\mathbf c}[S_{\bar p}]-\mathbb E_{\mathbf v}[B_{\bar p}]=2,\qquad \mathbb E_{\mathbf v}[B_{\underline p}]-\mathbb E_{\mathbf c}[S_{\underline p}]=2\qquad(4.2).$$
--   At a price $p$, buyer $i$'s surplus is $(v_i-p)_+$ and seller $j$'s is $(p-c_j)_+$; the total expected surpluses are $\sum_i\mathbb E_{\mathbf v}[(v_i-p)_+]$ and $\sum_j\mathbb E_{\mathbf c}[(p-c_j)_+]$.
--
--   These prices are used by Lemmas 4.3–4.6, 4.10 and 4.11.
--
--   **Formalization Note.** `expB p = Σ i, (μB i (Ici p)).toReal`, `expS p = Σ j, (μS j (Iic p)).toReal`. `IsBalancedPrice`, `IsExcessSupplyPrice`, `IsExcessDemandPrice` are predicates on a price (membership in `[0,1]` plus the defining equation); these prices exist by continuity but need not be unique, so statements quantify over every price satisfying the predicate, and $\lambda$ is `expB pt` for a balanced `pt`. `buyerSurplus p = Σ i, ∫ x, max (x − p) 0 ∂μB i`, `sellerSurplus p = Σ j, ∫ x, max (p − x) 0 ∂μS j` (bounded integrands on probability measures supported on $[0,1]$).
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), p. 27, (4.1), (4.2), footnote 1

import Mathlib
import Definitions.Def_StratifyMarkets_DoubleAuction_Instance

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

variable {n m : ℕ}

/-- `E_𝐯[B_p] = Σ_i Pr[v_i ≥ p]`, the expected number of eligible buyers at price `p` (p. 13). -/
noncomputable def DAInstance.expB (I : DAInstance n m) (p : ℝ) : ℝ :=
  ∑ i, (I.μB i (Set.Ici p)).toReal

/-- `E_𝐜[S_p] = Σ_j Pr[c_j ≤ p]`, the expected number of eligible sellers at price `p` (p. 13). -/
noncomputable def DAInstance.expS (I : DAInstance n m) (p : ℝ) : ℝ :=
  ∑ j, (I.μS j (Set.Iic p)).toReal

/-- `p̃` is a balanced price (4.1), p. 27: `p̃ ∈ [0, 1]` and `E_𝐯[B_p̃] = E_𝐜[S_p̃]`; the common
value is `λ` (it does not depend on the balanced price chosen). -/
def DAInstance.IsBalancedPrice (I : DAInstance n m) (p : ℝ) : Prop :=
  p ∈ Set.Icc (0 : ℝ) 1 ∧ I.expB p = I.expS p

/-- `p̄` is an excess-supply price (4.2), p. 27: `p̄ ∈ [0, 1]` and `E_𝐜[S_p̄] − E_𝐯[B_p̄] = 2`. -/
def DAInstance.IsExcessSupplyPrice (I : DAInstance n m) (p : ℝ) : Prop :=
  p ∈ Set.Icc (0 : ℝ) 1 ∧ I.expS p - I.expB p = 2

/-- `p̲` is an excess-demand price (4.2), p. 27: `p̲ ∈ [0, 1]` and `E_𝐯[B_p̲] − E_𝐜[S_p̲] = 2`. -/
def DAInstance.IsExcessDemandPrice (I : DAInstance n m) (p : ℝ) : Prop :=
  p ∈ Set.Icc (0 : ℝ) 1 ∧ I.expB p - I.expS p = 2

/-- The buyers' total expected surplus at price `p`, `Σ_{i=1}^{n} E_𝐯[(v_i − p)_+]` (footnote 1,
p. 27). -/
noncomputable def DAInstance.buyerSurplus (I : DAInstance n m) (p : ℝ) : ℝ :=
  ∑ i, ∫ x, max (x - p) 0 ∂I.μB i

/-- The sellers' total expected surplus at price `p`, `Σ_{j=1}^{m} E_𝐜[(p − c_j)_+]` (footnote 1,
p. 27). -/
noncomputable def DAInstance.sellerSurplus (I : DAInstance n m) (p : ℝ) : ℝ :=
  ∑ j, ∫ x, max (p - x) 0 ∂I.μS j

end StratifyMarkets.DoubleAuction


