-- Prove2me | Definitions.Def_MoneyBurningSurplus_Harmonic_Supplement_MIDR
-- name    : MoneyBurningSurplus_Harmonic_Supplement_MIDR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:55:54.3682+00:00
-- url     : https://prove2.me/theorems/bc657aec-b501-4601-bedb-f448958508a3
-- title:
--   App. B.2 — distributional ranges and the harmonic MIDR mechanism
-- statement:
--   Let $\mathcal D$ be a nonempty fixed collection of probability vectors on the finite outcome set $O$, and write $\mathbb E_{o\sim D}[g]=\sum_o D(o)g(o)$. For a profile $v$ and a set of agents $T$,
--
--   $$W_{\mathcal D}(T)=\sup_{D\in\mathcal D}\mathbb E_{o\sim D}\Big[\sum_{i\in T}v_i(o)\Big];$$
--
--   the paper assumes, and the theorems state, that this supremum is attained for every admissible profile and every $T$. A fixed rule chooses a member of every nonempty set of distributions; $D_T$ is its choice among the maximizers for $T$. For $i\in T$, $a_i(T)=\mathbb E_{o\sim D_T}[v_i(o)]$ and
--
--   $$p_i(T)=W_{\mathcal D}(T\setminus\{i\})-\mathbb E_{o\sim D_T}\Big[\sum_{j\in T\setminus\{i\}}v_j(o)\Big].$$
--
--   After $o\sim D_T$ is drawn, agent $i\in T$ pays $p_i(o;T)=p_i(T)\,v_i(o)/a_i(T)$ if $a_i(T)>0$ and $0$ if $a_i(T)=0$; agents outside $T$ pay $0$. All of these use the reported valuations. The **harmonic MIDR mechanism** draws $k$ with probability $1/(kH_n)$, a uniform $k$-subset $T$, and then $o\sim D_T$. The definitions give an agent's expected utility for any true valuation at any reported profile, and the expected residual surplus at a truthful profile, both over $k$, $T$ and $o$.
--
--   **Formalization Note** $\mathcal D$ is a `Set (O → ℝ)` of probability vectors; $W_{\mathcal D}$ is a real `sSup` (the set is nonempty and bounded by $\max_o\sum_{i\in T}v_i(o)$), and attainment is a separate predicate used as a hypothesis, as in the paper. The tie-break rule is a function on sets of distributions returning a member of every nonempty set.
-- source:
--   Tomer Ezra, Money Burning Mechanism Design: From Welfare to Surplus, STOC 2027 submission #585 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/585.pdf, App. B.2 (distributional range, W_D, D_{R_k}, a_i, p_i, realized payment), PDF p. 19 (printed p. 18)

import Mathlib
import Definitions.Def_MoneyBurningSurplus_Harmonic_Model

noncomputable section

namespace MoneyBurningSurplus.Harmonic.Supplement

open Finset

variable {n : ℕ} {O : Type*} [Fintype O] [DecidableEq O]

/-- Expectation `E_{o ∼ D}[g(o)] = ∑_o D(o) g(o)` of `g` under a probability vector `D` on the
finite outcome set (App. B.2, PDF 19). -/
def lotteryValue (D : O → ℝ) (g : O → ℝ) : ℝ :=
  ∑ o, D o * g o

/-- `D` is a probability vector on `O`: nonnegative entries summing to one. -/
def IsProbVector (D : O → ℝ) : Prop :=
  (∀ o, 0 ≤ D o) ∧ ∑ o, D o = 1

/-- A distributional range: a nonempty, fixed collection of distributions over `O`
(App. B.2, PDF 19). -/
def IsDistRange (Dset : Set (O → ℝ)) : Prop :=
  Dset.Nonempty ∧ ∀ D ∈ Dset, IsProbVector D

/-- `W_𝒟(T) = max_{D ∈ 𝒟} E_{o ∼ D}[∑_{i ∈ T} v_i(o)]`, taken as a supremum; the theorems
assume it is attained (App. B.2, PDF 19). -/
def distWelfare (Dset : Set (O → ℝ)) (v : Fin n → O → ℝ) (T : Finset (Fin n)) : ℝ :=
  sSup ((fun D => lotteryValue D (fun o => ∑ i ∈ T, v i o)) '' Dset)

/-- The paper's standing assumption on `𝒟` (App. B.2, PDF 19): for every admissible profile and
every set of agents `T`, the maximum defining `W_𝒟(T)` is attained by some `D ∈ 𝒟`. -/
def AttainsDistMax (Dset : Set (O → ℝ)) (V : Fin n → Set (O → ℝ)) : Prop :=
  ∀ v, AGT.IsValProfile V v → ∀ T : Finset (Fin n),
    ∃ D ∈ Dset, lotteryValue D (fun o => ∑ i ∈ T, v i o) = distWelfare Dset v T

/-- The maximizing distributions of `𝒟` for the agents in `T`. -/
def distMaximizers (Dset : Set (O → ℝ)) (v : Fin n → O → ℝ) (T : Finset (Fin n)) :
    Set (O → ℝ) :=
  {D | D ∈ Dset ∧ lotteryValue D (fun o => ∑ i ∈ T, v i o) = distWelfare Dset v T}

/-- A fixed, report-independent rule choosing a member of every nonempty set of
distributions (App. B.2, PDF 19). -/
def IsDistTieBreak (tbD : Set (O → ℝ) → (O → ℝ)) : Prop :=
  ∀ S : Set (O → ℝ), S.Nonempty → tbD S ∈ S

/-- The selected distribution `D_T`: the tie-broken maximizer for the reports of `T`. -/
def midrLottery (tbD : Set (O → ℝ) → (O → ℝ)) (Dset : Set (O → ℝ)) (T : Finset (Fin n))
    (v : Fin n → O → ℝ) : O → ℝ :=
  tbD (distMaximizers Dset v T)

/-- `a_i(T) = E_{o ∼ D_T}[v_i(o)]`, agent `i`'s expected reported value. -/
def midrExpValue (tbD : Set (O → ℝ) → (O → ℝ)) (Dset : Set (O → ℝ)) (T : Finset (Fin n))
    (i : Fin n) (v : Fin n → O → ℝ) : ℝ :=
  lotteryValue (midrLottery tbD Dset T v) (v i)

/-- The VCG-in-expectation payment
`p_i(T) = W_𝒟(T ∖ {i}) − E_{o ∼ D_T}[∑_{j ∈ T ∖ {i}} v_j(o)]`. -/
def midrVCGPay (tbD : Set (O → ℝ) → (O → ℝ)) (Dset : Set (O → ℝ)) (T : Finset (Fin n))
    (i : Fin n) (v : Fin n → O → ℝ) : ℝ :=
  distWelfare Dset v (T.erase i) -
    lotteryValue (midrLottery tbD Dset T v) (fun o => ∑ j ∈ T.erase i, v j o)

/-- The realized payment after `o ∼ D_T` (App. B.2, PDF 19): for `i ∈ T`,
`p_i(T) v_i(o) / a_i(T)` if `a_i(T) > 0` and `0` if `a_i(T) = 0`; agents outside `T` pay `0`.
All valuations here are the reported ones. -/
def midrPay (tbD : Set (O → ℝ) → (O → ℝ)) (Dset : Set (O → ℝ)) (T : Finset (Fin n))
    (i : Fin n) (v : Fin n → O → ℝ) (o : O) : ℝ :=
  if i ∈ T then
    (if 0 < midrExpValue tbD Dset T i v then
      midrVCGPay tbD Dset T i v * v i o / midrExpValue tbD Dset T i v
    else 0)
  else 0

/-- Expected utility of an agent `i` with true valuation `u` under the harmonic MIDR mechanism at
the reported profile `w`: the expectation over `k` (probability `1/(k H_n)`), the uniform
`k`-subset `T`, and `o ∼ D_T` (App. B.2, PDF 19). -/
def midrExpectedUtility (tbD : Set (O → ℝ) → (O → ℝ)) (Dset : Set (O → ℝ)) (u : O → ℝ)
    (i : Fin n) (w : Fin n → O → ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, hasmProb n k * ((Nat.choose n k : ℝ)⁻¹ *
    ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      ∑ o, midrLottery tbD Dset T w o * (u o - midrPay tbD Dset T i w o))

/-- Expected residual surplus of the harmonic MIDR mechanism at the truthful profile `v`, over
the harmonic sampling and the lottery `o ∼ D_T`. -/
def midrSurplus (tbD : Set (O → ℝ) → (O → ℝ)) (Dset : Set (O → ℝ)) (v : Fin n → O → ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, hasmProb n k * ((Nat.choose n k : ℝ)⁻¹ *
    ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      ∑ o, midrLottery tbD Dset T v o * ∑ i : Fin n, (v i o - midrPay tbD Dset T i v o))

end MoneyBurningSurplus.Harmonic.Supplement


