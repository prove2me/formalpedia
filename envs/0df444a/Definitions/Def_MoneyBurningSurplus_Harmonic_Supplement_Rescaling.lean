-- Prove2me | Definitions.Def_MoneyBurningSurplus_Harmonic_Supplement_Rescaling
-- name    : MoneyBurningSurplus_Harmonic_Supplement_Rescaling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:55:07.008357+00:00
-- url     : https://prove2.me/theorems/02c24a14-81d0-4512-ba20-fd4be7e056fd
-- title:
--   §2, §4 — seeded randomized mechanisms, scalable domains and the random-rescaling mechanism M̃
-- statement:
--   A randomized direct mechanism for $n$ agents and a finite outcome set $O$ is given by its seeds: for every seed $r$ in a measurable space $\Omega$, a deterministic mechanism $M^r=(o^r,p^r)$ with outcome rule $o^r(w)\in O$ and payments $p_i^r(w)\in\mathbb R$ at every reported profile $w$. The seed is drawn from a probability measure $\mu$ independently of the reports. Relative to valuation domains $V_i$, the mechanism is
--
--   1. **seed-measurable** if, at every admissible profile $w$, the maps $r\mapsto o^r(w)$ and $r\mapsto p_i^r(w)$ are measurable;
--   2. **universally truthful** if every $M^r$ is truthful on the domains;
--   3. **ex-post individually rational** if every $M^r$ gives every agent nonnegative utility $v_i(o^r(v))-p_i^r(v)\ge0$ at admissible truthful profiles;
--   4. of **nonnegative payments** if $p_i^r(v)\ge0$ for every seed.
--
--   Its expected welfare at $v$ is $\mathbb E_{r\sim\mu}\big[\sum_i v_i(o^r(v))\big]$. A domain profile is **scalable** if every member of $V_i$ is pointwise nonnegative and $s\,u\in V_i$ for every $u\in V_i$ and every real $s>0$.
--
--   Given $\alpha\ge1$, set $L=\lceil\log_2(6\alpha n)\rceil$ and $\rho=1+1/L$. The **random-rescaling mechanism** $\widetilde M$ draws, independently for every agent, a level $K_i\in\{0,\dots,L\}$ with
--
--   $$q_k=\Pr[K_i=k]=\begin{cases}2^{-(k+1)},&0\le k<L,\\2^{-L},&k=L,\end{cases}$$
--
--   sets $s_i=\rho^{K_i}$, runs $M$ once (with its own seed $r$) on the scaled profile $sv=(s_iv_i)_i$, returns that outcome and charges $p_i/s_i$. Its seed is $(K,r)$, and its expected residual surplus at $v$ is
--
--   $$\sum_{K}\Big(\prod_i q_{K_i}\Big)\,\mathbb E_{r\sim\mu}\Big[\sum_i\big(v_i(o^r(sv))-p_i^r(sv)/s_i\big)\Big].$$
--
--   These objects specify the reduction of Theorem 2; no incentive or surplus property is built in.
--
--   **Formalization Note** Agents are `Fin n`; valuations are real functions. The level vector ranges over the finite type `Fin n → Fin (L+1)`, so the expectation over $K$ is a finite sum, and the expectation over $r$ is a Bochner integral against $\mu$. $L$ is a natural number via `Nat.ceil` of `Real.logb 2`.
-- source:
--   Tomer Ezra, Money Burning Mechanism Design: From Welfare to Surplus, STOC 2027 submission #585 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/585.pdf, §2 Model (mechanisms, UT, EPIR, approximation for welfare), PDF pp. 6–7 (printed pp. 5–6); scalability, PDF p. 8 (printed p. 7); §4 random-rescaling mechanism, PDF p. 10 (printed p. 9)

import Mathlib
import Definitions.Def_MoneyBurningSurplus_Harmonic_Model

noncomputable section

namespace MoneyBurningSurplus.Harmonic.Supplement

open Finset MeasureTheory

variable {n : ℕ} {O : Type*} [Fintype O] [Nonempty O] [DecidableEq O]

/-- A randomized direct mechanism given by its seeds: for each seed `r ∈ Ω`, a deterministic
mechanism with outcome rule `out r` and payment rule `pay r` (§2, PDF 6). -/
structure SeededMech (n : ℕ) (O : Type*) (Ω : Type*) where
  out : Ω → (Fin n → O → ℝ) → O
  pay : Ω → Fin n → (Fin n → O → ℝ) → ℝ

variable {Ω : Type*}

/-- Outcome and payments are measurable functions of the seed at every admissible reported
profile, so that the expectations over the seed are defined. -/
def IsSeedMeasurable [MeasurableSpace Ω] (V : Fin n → Set (O → ℝ)) (M : SeededMech n O Ω) :
    Prop :=
  ∀ w : Fin n → O → ℝ, AGT.IsValProfile V w →
    (∀ a : O, MeasurableSet {r | M.out r w = a}) ∧ ∀ i, Measurable (fun r => M.pay r i w)

/-- Universal truthfulness on the domains `V`: every seed's deterministic mechanism is
truthful (§2, PDF 6). -/
def IsUniversallyTruthful (V : Fin n → Set (O → ℝ)) (M : SeededMech n O Ω) : Prop :=
  ∀ r, AGT.MechIncentiveCompatible V (M.out r) (M.pay r)

/-- Ex-post individual rationality on `V`: nonnegative utility at every seed (§2, PDF 7). -/
def IsExPostIR (V : Fin n → Set (O → ℝ)) (M : SeededMech n O Ω) : Prop :=
  ∀ r, AGT.IndividuallyRational V (M.out r) (M.pay r)

/-- Nonnegative payments on `V` at every seed (§2, PDF 6). -/
def HasNonnegPayments (V : Fin n → Set (O → ℝ)) (M : SeededMech n O Ω) : Prop :=
  ∀ r, AGT.NoPositiveTransfers V (M.out r) (M.pay r)

/-- Expected welfare `E_r[∑_i v_i(o^r(v))]` over the seed law `μ` (§2, PDF 7). -/
def expectedWelfare [MeasurableSpace Ω] (μ : Measure Ω) (M : SeededMech n O Ω)
    (v : Fin n → O → ℝ) : ℝ :=
  ∫ r, ∑ i, v i (M.out r v) ∂μ

/-- A scalable domain of nonnegative valuations: every member is pointwise nonnegative and
`s • u ∈ V i` for every `u ∈ V i` and every real `s > 0` (§2, PDF 8; §4, PDF 10). -/
def IsScalableDomain (V : Fin n → Set (O → ℝ)) : Prop :=
  (∀ i, ∀ u ∈ V i, ∀ o, 0 ≤ u o) ∧ ∀ i, ∀ u ∈ V i, ∀ s : ℝ, 0 < s → s • u ∈ V i

/-- `L := ⌈log₂(6 α n)⌉` (§4, PDF 10). -/
def rescaleLevels (n : ℕ) (α : ℝ) : ℕ := ⌈Real.logb 2 (6 * α * n)⌉₊

/-- `ρ := 1 + 1/L` (§4, PDF 10). -/
def rescaleBase (L : ℕ) : ℝ := 1 + 1 / (L : ℝ)

/-- `q_k = Pr[K_i = k]`: `2^{-(k+1)}` for `0 ≤ k < L` and `2^{-L}` for `k = L` (§4, PDF 10). -/
def scaleLevelProb (L k : ℕ) : ℝ :=
  if k < L then (1 / 2 : ℝ) ^ (k + 1) else (1 / 2 : ℝ) ^ L

/-- The scale `s_i = ρ^{K_i}` of agent `i` under the level vector `K`. -/
def scaleFactor (L : ℕ) (K : Fin n → Fin (L + 1)) (i : Fin n) : ℝ :=
  rescaleBase L ^ (K i : ℕ)

/-- The scaled profile `s v = (s_i v_i)_i`. -/
def scaledProfile (L : ℕ) (K : Fin n → Fin (L + 1)) (w : Fin n → O → ℝ) :
    Fin n → O → ℝ :=
  fun i => scaleFactor L K i • w i

/-- The random-rescaling mechanism `M̃` (§4, PDF 10): seed `(K, r)`; run `M` with seed `r`
once on the scaled profile, return its outcome and charge `p_i / s_i`. -/
def rescaledMech (M : SeededMech n O Ω) (L : ℕ) :
    SeededMech n O ((Fin n → Fin (L + 1)) × Ω) where
  out := fun Kr w => M.out Kr.2 (scaledProfile L Kr.1 w)
  pay := fun Kr i w => M.pay Kr.2 i (scaledProfile L Kr.1 w) / scaleFactor L Kr.1 i

/-- Probability `∏_i q_{K_i}` of the level vector `K` (independent levels). -/
def scaleVectorProb (L : ℕ) (K : Fin n → Fin (L + 1)) : ℝ :=
  ∏ i, scaleLevelProb L (K i)

/-- Expected residual surplus of `M̃` at `v`: the expectation over the independent levels
`K` (a finite sum) and over the seed `r ∼ μ` of `M`. -/
def rescaledSurplus [MeasurableSpace Ω] (μ : Measure Ω) (M : SeededMech n O Ω) (L : ℕ)
    (v : Fin n → O → ℝ) : ℝ :=
  ∑ K : Fin n → Fin (L + 1), scaleVectorProb L K *
    ∫ r, ∑ i, (v i ((rescaledMech M L).out (K, r) v) - (rescaledMech M L).pay (K, r) i v) ∂μ

end MoneyBurningSurplus.Harmonic.Supplement


