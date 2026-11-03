-- Prove2me | Definitions.Def_MultiPurchaseMNL_Model
-- name    : MultiPurchaseMNL_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:23.943575+00:00
-- url     : https://prove2.me/theorems/1b0d375e-1098-4b5c-84a6-89a9c3bbd586
-- title:
--   §2.1–§2.3, pp.9–12 — the Multi-Purchase MNL model: utilities, rank, $\pi_m$ (1), $\pi$, $\mathcal R$ (2)
-- statement:
--   A retailer has $n$ products $1,\dots,n$ and the no-purchase option $0$. A customer draws a maximum number of purchases $M$, supported on $\{0,1,\dots,m_{\max}\}$ with $p_m=\Pr[M=m]$, and random utilities $U_i=v_i+e_i$ for $i\in\{0,\dots,n\}$, where $e_0,\dots,e_n$ are independent standard Gumbel variables and $v_0=0$. A customer with $M=m$ buys the $m$ highest-utility offered products among those whose utility exceeds $U_0$. Product $i$ has preference weight $w_i=e^{v_i}$ and revenue $r_i$; $w(S)=\sum_{j\in S}w_j$.
--
--   For an assortment $S\subseteq[n]$ and $i\in S$, the rank is $\mathrm{rank}(i,S)=|\{j\in S:U_j\ge U_i\}|$, and
--   $$
--   \pi_m(i,S)=\Pr\big[[\mathrm{rank}(i,S)\le m]\wedge[U_i>U_0]\big],\qquad \pi(i,S)=\sum_{m}\Pr[M=m]\,\pi_m(i,S),\qquad \mathcal R(S)=\sum_{i\in S}r_i\,\pi(i,S).
--   $$
--   The assortment problem (2) is $\max_{S\subseteq[n]}\mathcal R(S)$.
--
--   The standing assumptions (`Standing`) are $m_{\max}\ge1$, $w_i>0$, $r_i\ge0$, $p_m\ge0$ and $\sum_m p_m=1$.
--
--   **Formalization Note** Products are `Fin n` and the no-purchase option is `none : Option (Fin n)`. The shock vector has law `Measure.pi` of a law $\mu$ on $\mathbb R$; the theorems assume $\mu$ is the standard Gumbel law through the published predicate `McFadden1974.RandomUtility.IsExtremeValue`. $v_i=\log w_i$, so $w_0=1$ is the $1+$ in every denominator. $\pi_m$ is defined for every $m\in\mathbb N$ and $\pi_0(i,S)=0$ for $i\in S$. The paper's $r_i>0$ is relaxed to $r_i\ge0$.
-- source:
--   Bai, Feldman, Segev, Topaloglu, Wagner, Assortment Optimization under the Multi-Purchase Multinomial Logit Choice Model, author manuscript (Apr 2023), §2.1, pp.9–10, (1); §2.2, p.11; §2.3, p.12, (2); §4, p.16

import Mathlib
import Definitions.Def_McFadden1974_RandomUtility_Model

open MeasureTheory ProbabilityTheory

namespace MultiPurchaseMNL

/-- **An instance of the Multi-Purchase MNL assortment problem.** Bai, Feldman, Segev, Topaloglu,
Wagner, *Assortment Optimization under the Multi-Purchase Multinomial Logit Choice Model*, author
manuscript (Apr 2023), §2.1, pp.9–10; §2.2, p.11; §2.3, p.12; §4, p.16.

There are `n` products. Product `i` has preference weight `w i` (the paper's `wᵢ = e^{vᵢ}`, p.11) and
revenue `r i` (p.12). The maximum number of purchases `M` is supported on `{0, 1, …, m_max}` (§4,
p.16), and `p m = Pr[M = m]`.

**Formalization Note.** Products are `Fin n`; the no-purchase option `0` is `none : Option (Fin n)`
wherever shocks and utilities are indexed. The distribution of `M` is the vector `p` on
`{0, …, m_max}`. -/
structure Instance (n mmax : ℕ) where
  w : Fin n → ℝ
  r : Fin n → ℝ
  p : Fin (mmax + 1) → ℝ

namespace Instance

variable {n mmax : ℕ}

/-- The standing assumptions of §2.1–§2.3 and §4 (pp.10, 12, 16): positive preference weights
(`wᵢ = e^{vᵢ} > 0`), revenues, a probability vector `p` for `M`, and `m_max ≥ 1`.

**Formalization Note.** The paper has `rᵢ > 0` (p.12); `0 ≤ rᵢ` is a generalization. `1 ≤ m_max` is
the paper's presupposition that a customer is willing to buy a positive number of products ("we may
assume without loss of generality that Pr[M > 0] = 1", p.12): at `m_max = 0` every revenue is `0`. -/
structure Standing (I : Instance n mmax) : Prop where
  one_le_mmax : 1 ≤ mmax
  w_pos : ∀ i, 0 < I.w i
  r_nonneg : ∀ i, 0 ≤ I.r i
  p_nonneg : ∀ m, 0 ≤ I.p m
  p_sum : ∑ m, I.p m = 1

end Instance

/-- **The joint law of the shocks** `(e₀, e₁, …, eₙ)`, §2.1, p.10: "the random variables
`e₀, e₁, …, eₙ` are independently sampled", each with law `μ`. Under the paper's model `μ` is the
standard Gumbel law, `McFadden1974.RandomUtility.IsExtremeValue μ`.

**Formalization Note.** The shock of the no-purchase option is the coordinate `none`. -/
noncomputable def shockLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    Measure (Option (Fin n) → ℝ) :=
  Measure.pi (fun _ : Option (Fin n) => μ)

/-- **Random utilities**, §2.1, p.10: `Uᵢ = vᵢ + eᵢ` with `v₀ = 0`.

**Formalization Note.** `vᵢ = log wᵢ`, the inverse of the paper's `wᵢ = e^{vᵢ}` (p.11), so
`U₀ = e₀` and `Uᵢ = log wᵢ + eᵢ`. -/
noncomputable def utility {mmax : ℕ} {n : ℕ} (I : Instance n mmax) (e : Option (Fin n) → ℝ) :
    Option (Fin n) → ℝ
  | none => e none
  | some i => Real.log (I.w i) + e (some i)

/-- **The rank of a product in an assortment**, §2.1, p.10:
`rank(i, S) = |{j ∈ S : Uⱼ ≥ Uᵢ}|`, as a function of the shock vector `e`. -/
noncomputable def rank {n mmax : ℕ} (I : Instance n mmax) (S : Finset (Fin n)) (i : Fin n)
    (e : Option (Fin n) → ℝ) : ℕ :=
  (S.filter fun j => utility I e (some i) ≤ utility I e (some j)).card

/-- **The conditional choice probability (1)**, §2.1, p.10:
`πₘ(i, S) = Pr[[rank(i, S) ≤ m] ∧ [Uᵢ > U₀]]`, the probability that product `i ∈ S` is purchased
when the customer buys up to `m` products.

**Formalization Note.** Defined for every `m : ℕ` (the paper writes `m ∈ [n]`). For `i ∈ S` the rank
is at least `1`, so `π₀(i, S) = 0`. -/
noncomputable def piM (μ : Measure ℝ) [IsProbabilityMeasure μ] {n mmax : ℕ} (I : Instance n mmax)
    (m : ℕ) (i : Fin n) (S : Finset (Fin n)) : ℝ :=
  (shockLaw μ n {e | rank I S i e ≤ m ∧ utility I e none < utility I e (some i)}).toReal

/-- **The choice probability**, §2.1, p.10: `π(i, S) = Σₘ Pr[M = m] · πₘ(i, S)`.

**Formalization Note.** The sum runs over the support `{0, …, m_max}` of `M` (§4, p.16), where the
paper writes `m ∈ [n]`; the term `m = 0` is `0`. -/
noncomputable def choiceProb (μ : Measure ℝ) [IsProbabilityMeasure μ] {n mmax : ℕ}
    (I : Instance n mmax) (i : Fin n) (S : Finset (Fin n)) : ℝ :=
  ∑ m : Fin (mmax + 1), I.p m * piM μ I m i S

/-- **The expected revenue**, §2.3, p.12: `R(S) = Σ_{i∈S} rᵢ · π(i, S)`, the objective of (2). -/
noncomputable def R (μ : Measure ℝ) [IsProbabilityMeasure μ] {n mmax : ℕ} (I : Instance n mmax)
    (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, I.r i * choiceProb μ I i S

/-- **Total weight**, p.11: `w(S) = Σ_{j∈S} wⱼ`. The no-purchase weight is `w₀ = e^{v₀} = 1`, the
`1 +` of every denominator below. -/
def wsum {n mmax : ℕ} (I : Instance n mmax) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, I.w i

end MultiPurchaseMNL


