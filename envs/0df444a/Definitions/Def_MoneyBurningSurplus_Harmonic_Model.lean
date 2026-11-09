-- Prove2me | Definitions.Def_MoneyBurningSurplus_Harmonic_Model
-- name    : MoneyBurningSurplus_Harmonic_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:12.28699+00:00
-- url     : https://prove2.me/theorems/aebd1333-88a2-4ce2-9116-a45bc894c813
-- title:
--   §2–§3 — HASM, sampled welfare and exact finite expectations
-- statement:
--   Let $N$ be a set of $n\ge2$ agents, $O$ a nonempty finite outcome set, and $v_i:O\to\mathbb R_{\ge0}$ their valuations. The admissible report domain contains every such valuation. For $T\subseteq N$, define
--
--   $$W(T)=\max_{o\in O}\sum_{i\in T}v_i(o).$$
--
--   A fixed tie-break rule chooses an element of every nonempty subset of $O$. Let $o_R$ be that rule applied to the set maximizing $\sum_{i\in R}v_i(o)$. For $i\in R$ set $p_i(R)=W(R\setminus\{i\})-\sum_{j\in R\setminus\{i\}}v_j(o_R)$; otherwise set $p_i(R)=0$. Thus reports outside $R$ do not affect the mechanism.
--
--   HASM draws $k\in\{1,\ldots,n\}$ with probability $q_k=1/(kH_n)$, where $H_n=\sum_{k=1}^n1/k$, and then draws a uniform $k$-subset $R$. The definitions also compute
--
--   $$\overline W_k=\binom nk^{-1}\sum_{|R|=k}W(R),\qquad C_k=\binom nk^{-1}\sum_{|R|=k}\sum_{i\in R}(v_i(o_R)-p_i(R)),$$
--   $$\operatorname{ERS}=\sum_{k=1}^n q_k\binom nk^{-1}\sum_{|R|=k}\sum_{i\in N}(v_i(o_R)-p_i(R)).$$
--
--   These operations specify the mechanism and the averages used in Theorem 1; no incentive or surplus guarantee is built into a definition.
--
--   **Formalization Note** Agents are `Fin n`; valuations use real functions with pointwise nonnegativity expressed through AGT's domain predicate. Finite nonempty maxima use `Finset.sup'`; the maximizer set is computed from sampled reports. The harmonic number is Mathlib's rational `harmonic n`, cast to the reals. The size weights are used only for $1\le k\le n$, and conditional averages only for $0\le k\le n$. Outside these ranges Lean's total division convention applies; no claim concerns those inputs.
-- source:
--   Tomer Ezra, Money Burning Mechanism Design: From Welfare to Surplus, STOC 2027 submission #585 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/585.pdf, §2 Model, PDF pp. 6–7 (printed pp. 5–6); §3 HASM, PDF p. 8 (printed p. 7); sampled utility and residual surplus, PDF p. 9 (printed p. 8)

import Mathlib
import Definitions.Def_agt_mechanism

noncomputable section

namespace MoneyBurningSurplus.Harmonic

open Finset

variable {n : ℕ} {O : Type*} [Fintype O] [Nonempty O] [DecidableEq O]

/-- All nonnegative valuations; reports and deviations have this same domain (§2, PDF 6). -/
def valuationDomain : Fin n → Set (O → ℝ) :=
  fun _ => {u | ∀ o, 0 ≤ u o}

/-- Welfare of the sampled agents, maximized over the entire outcome space (§2, PDF 6). -/
def welfare (v : Fin n → O → ℝ) (T : Finset (Fin n)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun o => ∑ i ∈ T, v i o)

/-- A fixed choice from every nonempty set of tied outcomes (§2, PDF 6). -/
def IsTieBreak (tb : Finset O → O) : Prop :=
  ∀ S : Finset O, S.Nonempty → tb S ∈ S

/-- The maximizing outcomes computed using only the reports in R (§3, PDF 8). -/
def maximizers (v : Fin n → O → ℝ) (R : Finset (Fin n)) : Finset O := by
  classical
  exact Finset.univ.filter (fun o => (∑ i ∈ R, v i o) = welfare v R)

/-- The deterministic outcome for a sampled set, with fixed report-independent tie-breaking. -/
def vcgOutcome (tb : Finset O → O) (R : Finset (Fin n))
    (v : Fin n → O → ℝ) : O := tb (maximizers v R)

/-- Clarke pivot on R, and zero outside R (§3, PDF 8–9). -/
def hasmPay (tb : Finset O → O) (R : Finset (Fin n)) (i : Fin n)
    (v : Fin n → O → ℝ) : ℝ :=
  if i ∈ R then welfare v (R.erase i) - ∑ j ∈ R.erase i, v j (vcgOutcome tb R v)
  else 0

/-- Probability of sample size k on the mechanism's domain 1 ≤ k ≤ n (§3, PDF 8). -/
def hasmProb (n k : ℕ) : ℝ := 1 / ((k : ℝ) * (harmonic n : ℝ))

/-- Expected welfare of a uniform k-subset, for 0 ≤ k ≤ n (§3, PDF 8). -/
def avgWelfare (v : Fin n → O → ℝ) (k : ℕ) : ℝ :=
  (Nat.choose n k : ℝ)⁻¹ *
    ∑ R ∈ (Finset.univ : Finset (Fin n)).powersetCard k, welfare v R

/-- Expected total utility of sampled agents conditional on size k (§3, PDF 9). -/
def sampledUtility (tb : Finset O → O) (v : Fin n → O → ℝ) (k : ℕ) : ℝ :=
  (Nat.choose n k : ℝ)⁻¹ *
    ∑ R ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      ∑ i ∈ R, (v i (vcgOutcome tb R v) - hasmPay tb R i v)

/-- Expected residual surplus under the exact two-stage HASM law (§3, PDF 8–9). -/
def expectedResidualSurplus (tb : Finset O → O) (v : Fin n → O → ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, hasmProb n k * ((Nat.choose n k : ℝ)⁻¹ *
    ∑ R ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      ∑ i : Fin n, (v i (vcgOutcome tb R v) - hasmPay tb R i v))

end MoneyBurningSurplus.Harmonic


