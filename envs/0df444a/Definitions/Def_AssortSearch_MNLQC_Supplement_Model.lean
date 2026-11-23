-- Prove2me | Definitions.Def_AssortSearch_MNLQC_Supplement_Model
-- name    : AssortSearch_MNLQC_Supplement_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T06:20:16.556969+00:00
-- url     : https://prove2.me/theorems/9cf94a21-3ba1-4961-b0fb-3e603af5f2ca
-- title:
--   Overlapping assortment model: the choice probability $q_i^{so}(S)$ and the §5.1 objects $d_i(x)$, $\hat v(x)$, $\pi(x)$, heuristic equilibrium
-- statement:
--   A retailer can carry product variants $N=\{1,\dots,n\}$; it offers an assortment $S\subseteq N$, and $\bar S=N-S$ are the variants it does not carry. A consumer's utility for variant $j$ is $U_j=(u_j-p_j)+\zeta_j$ and for not purchasing $U_0=u_0+\zeta_0$, where $\zeta_0,\zeta_1,\dots,\zeta_n$ are i.i.d. zero-mean Gumbel shocks of scale $\mu>0$. The preferences are $v_j=\exp((u_j-p_j)/\mu)$ and $v_0=\exp(u_0/\mu)$.
--
--   **Overlapping assortment model (§3.1).** The consumer sees $U_0$ and the utilities of the variants in $S$. Write $y=U_{\max}$ for the best of these. If she searches she pays a cost $b>0$ and can then buy the best variant of all of $N$. Let $w(\bar y,S)$ be the density of $\max_{i\in\bar S}U_i$. By rule (5) she searches when
--   $$\Phi_S(y)=\int_y^\infty(\bar y-y)\,w(\bar y,S)\,d\bar y\ \ge\ b .$$
--   The **choice probability** of variant $i\in S$ is the probability of the event that $U_i>U_j$ for every other $j\in S$, that $U_i>U_0$, and that $\Phi_S(U_i)<b$, so that she buys $i$ without searching:
--   $$q_i^{so}(S)=\Pr\big(U_i>\max_{j\in S\setminus\{i\}}U_j,\ U_i>U_0,\ \Phi_S(U_i)<b\big).$$
--
--   **Iterative assortment planning (§5.1).** The assortment of depth $x$ is $\{1,\dots,x\}$, the $x$ most popular variants. The observed demands are taken equal to the expected demands of the overlapping model, $d_i(x)=q_i^{so}(x)$, computed by Theorem 3's formula $q_i^m(x)\,(1-H(\bar U(x),x))$. When $x\ge n$ the full assortment is offered and there is no search, so $d_i(x)=q_i^m(x)$. The no-purchase demand is $d_0(x)=1-\sum_{i=1}^{x}d_i(x)$ (normalisation (14)). The estimates, normalised by $\hat v_1(x)=1$, are
--   $$\hat v_i(x)=\frac{d_i(x)}{d_1(x)}\quad(i\le x),\qquad \hat v_0(x)=\frac{d_0(x)}{d_1(x)},$$
--   and $\hat v_i(x)=\hat v_i(n)$ for the variants $i>x$ outside the assortment. With margins $m_i$ and operational cost $c$, the true profit is $\pi(x)=\sum_{i=1}^{x}\big(m_i d_i(x)-c(d_i(x))\big)$. The no-search model's predicted profit $\pi(x\mid\hat v)$ is the published `AssortSearch.HeurEq.estProfit`. A **heuristic equilibrium** is a depth $1\le x^*\le n$ that maximises $\pi(\cdot\mid\hat v(x^*))$ over the depths $0,\dots,n$. An **optimal depth** $x^o\le n$ maximises $\pi$ over the same depths.
--
--   These are the overlapping-model counterparts of the independent-model objects of `AssortSearch.HeurEq.Model`. Theorems 3, 7 and 8 of this supplement are stated with them.
--
--   **Formalization Note** The probability space is the product of the Gumbel law $G$ over `Option (Fin n)`, the no-purchase shock being `none`; utilities, preferences, $\lambda$ and $H$ come from `AssortSearch.Cannibal.Model`. The search gain $\Phi_S$, the closed-form density $w(\cdot,S)$ (its density property is the published `AssortSearch.FullAssort.outside_max_law`), the threshold $\bar U(S)$ and the closed-form demand $q_i^{so}(S)$ (`demandSO`) come from `AssortSearch.FullAssort.Model`. Variants are `Fin n`, 0-based, and depth $x$ is `popularSet n x`. $d_1(x)$ is set to $0$ when $n=0$. The estimates are meaningful only for $1\le x\le n$.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), pp. 10–11 (PDF 12–13), §3.1, overlapping assortment model, rule (5), Theorem 3; pp. 19–20 (PDF 21–22), §5.1, (14), estimates and heuristic equilibrium; p. 23 (PDF 25), proof of Theorem 8 (x^o)

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_Cannibal_Model
import Definitions.Def_AssortSearch_FullAssort_Model
import Definitions.Def_AssortSearch_HeurEq_Model

open MeasureTheory RetailVariety.Structure

namespace AssortSearch.MNLQC.Supplement

/-! # The overlapping assortment model: choice probability (Theorem 3) and §5.1 objects

Cachon, Terwiesch & Xu, *Retail Assortment Planning in the Presence of Consumer Search*,
working paper (Dec. 20, 2002), §3.1 (pp. 10–11, PDF 12–13) and §5.1 (pp. 19–23, PDF 21–25).

Variants are `Fin n` (index `⟨k, _⟩` is the paper's variant `k + 1`); the no-purchase option is
`none : Option (Fin n)` in the random-utility model of `AssortSearch.Cannibal`, and its preference
is the separate real `v0` elsewhere. The search gain `Φ_S`, the density `w(·, S)`, the threshold
`Ū(S)` and the closed-form demand `q_i^so(S)` are those of `AssortSearch.FullAssort`. -/

/-- Variant `i`'s choice probability in the **overlapping assortment model** (p. 10–11): under
i.i.d. shocks `ζ_0, ζ_1, …, ζ_n` with law `G`, utilities `U_j = a_j + ζ_j` (`a_j = u_j − p_j`,
`U_0 = u_0 + ζ_0`), the probability of the event that `U_i > U_j` for every other `j ∈ S`,
`U_i > U_0`, and the consumer, observing `U_max = U_i`, does not search: by rule (5) she searches
iff `∫_{U_max}^∞ (ȳ − U_max) w(ȳ, S) dȳ ≥ b`, so she buys `i` iff `Φ_S(U_i) < b`. The preferences
in `w(·, S)` are `v_j = exp(a_j/μ)`. -/
noncomputable def overlapProb {n : ℕ} (G : Measure ℝ) [IsProbabilityMeasure G] (μ : ℝ)
    (a : Fin n → ℝ) (u0 b : ℝ) (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  (Measure.pi (fun _ : Option (Fin n) => G)
    {ζ | (∀ j ∈ S, j ≠ i →
          AssortSearch.Cannibal.utility a u0 ζ (some j) <
            AssortSearch.Cannibal.utility a u0 ζ (some i)) ∧
      AssortSearch.Cannibal.utility a u0 ζ none < AssortSearch.Cannibal.utility a u0 ζ (some i) ∧
      AssortSearch.FullAssort.searchGain μ (AssortSearch.Cannibal.pref μ a) S
          (AssortSearch.Cannibal.utility a u0 ζ (some i)) < b}).toReal

/-- Observed demand of variant `i` with the assortment of depth `x` in the overlapping model
(§5.1, pp. 19–20): by the paper's assumption it equals the expected demand
`d_i(x) = q_i^so(x)`, given by Theorem 3's formula (`FullAssort.demandSO`; no search when
`x ≥ n`, the full assortment). Meaningful for `i.val < x`. -/
noncomputable def demandOv {n : ℕ} (μ b : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (x : ℕ) (i : Fin n) : ℝ :=
  AssortSearch.FullAssort.demandSO μ v v0 b (popularSet n x) i

/-- Observed no-purchase demand `d_0(x) = 1 − ∑_{i=1}^{x} d_i(x)` (normalisation (14), p. 19)
in the overlapping model. -/
noncomputable def demandNoPurchaseOv {n : ℕ} (μ b : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (x : ℕ) : ℝ :=
  1 - ∑ i ∈ popularSet n x, demandOv μ b v v0 x i

/-- Observed demand `d_1(x)` of the paper's variant 1 (index `0`); `0` when `n = 0`. -/
noncomputable def demandFirstOv {n : ℕ} (μ b : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (x : ℕ) : ℝ :=
  if h : 0 < n then demandOv μ b v v0 x ⟨0, h⟩ else 0

/-- Estimated preference `v̂_i(x)` from the sales data of assortment `x` in the overlapping model
(pp. 19–20), normalised by `v̂_1(x) = 1`: `d_i(x)/d_1(x)` for `i` in the assortment, and the
depth-test estimate `v̂_i(n) = d_i(n)/d_1(n)` for variants outside it. Meaningful for
`1 ≤ x ≤ n`. -/
noncomputable def estPrefOv {n : ℕ} (μ b : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (x : ℕ) (i : Fin n) : ℝ :=
  if i.val < x then demandOv μ b v v0 x i / demandFirstOv μ b v v0 x
  else demandOv μ b v v0 n i / demandFirstOv μ b v v0 n

/-- Estimated no-purchase preference `v̂_0(x) = d_0(x)/d_1(x)` in the overlapping model. -/
noncomputable def estPrefNoPurchaseOv {n : ℕ} (μ b : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (x : ℕ) : ℝ :=
  demandNoPurchaseOv μ b v v0 x / demandFirstOv μ b v v0 x

/-- True expected profit `π(x) = ∑_{i=1}^{x} (m_i d_i(x) − c(d_i(x)))` of the assortment of depth
`x` in the overlapping model ((1), p. 6, with Theorem 3): `FullAssort.profitSO` on the popular
set of depth `x`. -/
noncomputable def trueProfitOv {n : ℕ} (μ b : ℝ) (m : Fin n → ℝ) (c : ℝ → ℝ) (v : Fin n → ℝ)
    (v0 : ℝ) (x : ℕ) : ℝ :=
  AssortSearch.FullAssort.profitSO μ v v0 m c b (popularSet n x)

/-- Heuristic equilibrium of iterative no-search assortment planning (p. 20) when demand follows
the overlapping model: `1 ≤ x* ≤ n` and `x*` maximises, over the depths `0, …, n`, the no-search
profit `π(x | v̂(x*))` (`HeurEq.estProfit`) computed with the preferences estimated from `x*`. -/
def IsHeuristicEquilibriumOv {n : ℕ} (μ b : ℝ) (m : Fin n → ℝ) (c : ℝ → ℝ) (v : Fin n → ℝ)
    (v0 : ℝ) (xstar : ℕ) : Prop :=
  1 ≤ xstar ∧ xstar ≤ n ∧
    ∀ x : ℕ, x ≤ n →
      AssortSearch.HeurEq.estProfit m c (estPrefOv μ b v v0 xstar)
          (estPrefNoPurchaseOv μ b v v0 xstar) x ≤
        AssortSearch.HeurEq.estProfit m c (estPrefOv μ b v v0 xstar)
          (estPrefNoPurchaseOv μ b v v0 xstar) xstar

/-- `x^o` is an optimal depth of the overlapping model among `0, …, n`
(proof of Theorem 8, p. 23: `π(x^o) = max_{0 ≤ x ≤ n} π(x)`). -/
def IsOptimalDepthOv {n : ℕ} (μ b : ℝ) (m : Fin n → ℝ) (c : ℝ → ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (xo : ℕ) : Prop :=
  xo ≤ n ∧ ∀ x : ℕ, x ≤ n → trueProfitOv μ b m c v v0 x ≤ trueProfitOv μ b m c v v0 xo

end AssortSearch.MNLQC.Supplement


