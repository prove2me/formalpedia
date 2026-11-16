-- Prove2me | Definitions.Def_MoneyBurningSurplus_Harmonic_Supplement_Range
-- name    : MoneyBurningSurplus_Harmonic_Supplement_Range
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:55:30.244852+00:00
-- url     : https://prove2.me/theorems/cb53633a-8704-457f-a305-c9fb1e19c5cf
-- title:
--   App. B.1, App. D — range-restricted welfare, range VCG, harmonic MIR and outcome sampling
-- statement:
--   Let $n$ agents have valuations $v_i:O\to\mathbb R_{\ge0}$ on a nonempty finite outcome set $O$, and let $w(o)=\sum_i v_i(o)$. For a finite set $S\subseteq O$ and a set of agents $T$ the **range-restricted welfare** is
--
--   $$W_S(T)=\max_{o\in S}\sum_{i\in T}v_i(o),$$
--
--   with the convention that the maximum over $S=\emptyset$ is $0$ (used only for $F(\emptyset)=0$ in Appendix D). **VCG over the range $S$ on the agents in $T$** chooses $o_{S,T}$, the fixed tie-break rule applied to the maximizers of $\sum_{i\in T}v_i$ in $S$, and charges $i\in T$ the Clarke pivot
--
--   $$p_i=W_S(T\setminus\{i\})-\sum_{j\in T\setminus\{i\}}v_j(o_{S,T}),$$
--
--   and $0$ to $i\notin T$. Two harmonic mechanisms are built from it:
--
--   1. the **harmonic MIR mechanism** over a fixed range $R$: draw $k\in\{1,\dots,n\}$ with probability $1/(kH_n)$ and a uniform $k$-subset $T$ of agents, run VCG over $R$ on $T$; its expected residual surplus is
--   $$\sum_{k=1}^n\frac1{kH_n}\binom nk^{-1}\sum_{|T|=k}\sum_{i\in N}\big(v_i(o_{R,T})-p_i\big);$$
--   2. **harmonic outcome sampling**: with $m=|O|$, draw $s\in\{1,\dots,m\}$ with probability $1/(sH_m)$ and a uniform $s$-subset $S_s$ of outcomes, run VCG over $S_s$ on all agents; its expected residual surplus is the analogous finite average.
--
--   Finally, with $F(S)=\max_{o\in S}w(o)$, $F(\emptyset)=0$, and $o_S=o_{S,N}$, the **outcome gap** is $\Delta(S)=F(S)-F(S\setminus\{o_S\})$.
--
--   **Formalization Note** Finite maxima use `Finset.sup'` guarded by nonemptiness; the empty range gives $0$. The harmonic weights reuse the published `hasmProb` ($1/(kH_n)$, with Mathlib's `harmonic`). Nothing in these definitions asserts an incentive or surplus property.
-- source:
--   Tomer Ezra, Money Burning Mechanism Design: From Welfare to Surplus, STOC 2027 submission #585 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/585.pdf, App. B.1 (W_R, harmonic MIR mechanism), PDF p. 18 (printed p. 17); App. D.1 (harmonic outcome sampling), PDF p. 26 (printed p. 25); App. D.2 (F, o_S, Δ), PDF p. 26 (printed p. 25)

import Mathlib
import Definitions.Def_MoneyBurningSurplus_Harmonic_Model

noncomputable section

namespace MoneyBurningSurplus.Harmonic.Supplement

open Finset

variable {n : ℕ} {O : Type*} [Fintype O] [Nonempty O] [DecidableEq O]

/-- Maximum of `g` over a finite set `S` of outcomes, with the convention that the maximum over
the empty set is `0` (App. D.2, PDF 26: `F(∅) := 0`). -/
def rangeMax (S : Finset O) (g : O → ℝ) : ℝ :=
  if h : S.Nonempty then S.sup' h g else 0

/-- Range-restricted welfare `W_S(T) = max_{o ∈ S} ∑_{i ∈ T} v_i(o)` of the agents in `T`
(App. B.1, PDF 18; App. D.1, PDF 26). -/
def rangeWelfare (S : Finset O) (v : Fin n → O → ℝ) (T : Finset (Fin n)) : ℝ :=
  rangeMax S (fun o => ∑ i ∈ T, v i o)

/-- The outcomes of the range `S` that maximize the welfare of the agents in `T`. -/
def rangeMaximizers (S : Finset O) (v : Fin n → O → ℝ) (T : Finset (Fin n)) : Finset O :=
  S.filter (fun o => (∑ i ∈ T, v i o) = rangeWelfare S v T)

/-- VCG over the range `S` using only the reports of the agents in `T`: the tie-broken
welfare maximizer of `T` within `S`. -/
def rangeVCGOutcome (tb : Finset O → O) (S : Finset O) (T : Finset (Fin n))
    (v : Fin n → O → ℝ) : O :=
  tb (rangeMaximizers S v T)

/-- Clarke-pivot payment of VCG over the range `S` on the agents in `T`:
`W_S(T ∖ {i}) − ∑_{j ∈ T ∖ {i}} v_j(o)` for `i ∈ T`, and `0` for `i ∉ T`. -/
def rangeVCGPay (tb : Finset O → O) (S : Finset O) (T : Finset (Fin n)) (i : Fin n)
    (v : Fin n → O → ℝ) : ℝ :=
  if i ∈ T then
    rangeWelfare S v (T.erase i) - ∑ j ∈ T.erase i, v j (rangeVCGOutcome tb S T v)
  else 0

/-- Expected residual surplus of the harmonic MIR mechanism over the fixed range `R`
(App. B.1, PDF 18): `k` with probability `1/(k H_n)`, a uniform `k`-subset `T` of agents,
and VCG over `R` on `T`. -/
def mirSurplus (tb : Finset O → O) (R : Finset O) (v : Fin n → O → ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, hasmProb n k * ((Nat.choose n k : ℝ)⁻¹ *
    ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      ∑ i : Fin n, (v i (rangeVCGOutcome tb R T v) - rangeVCGPay tb R T i v))

/-- Expected residual surplus of harmonic outcome sampling (App. D.1, PDF 26): `s ∈ {1,…,m}`,
`m = |O|`, with probability `1/(s H_m)`, a uniform `s`-subset `S` of outcomes, and VCG over the
range `S` on all agents. -/
def outcomeSamplingSurplus (tb : Finset O → O) (v : Fin n → O → ℝ) : ℝ :=
  ∑ s ∈ Finset.Icc 1 (Fintype.card O), hasmProb (Fintype.card O) s *
    ((Nat.choose (Fintype.card O) s : ℝ)⁻¹ *
      ∑ S ∈ (Finset.univ : Finset O).powersetCard s,
        ∑ i : Fin n, (v i (rangeVCGOutcome tb S Finset.univ v) -
          rangeVCGPay tb S Finset.univ i v))

/-- The outcome gap `Δ(S) = F(S) − F(S ∖ {o_S})` with `F(S) = max_{o ∈ S} ∑_i v_i(o)`,
`F(∅) = 0`, and `o_S` the tie-broken maximizer in `S` (App. D.2, PDF 26). -/
def outcomeGap (tb : Finset O → O) (S : Finset O) (v : Fin n → O → ℝ) : ℝ :=
  rangeMax S (fun o => ∑ i, v i o) -
    rangeMax (S.erase (rangeVCGOutcome tb S Finset.univ v)) (fun o => ∑ i, v i o)

end MoneyBurningSurplus.Harmonic.Supplement


