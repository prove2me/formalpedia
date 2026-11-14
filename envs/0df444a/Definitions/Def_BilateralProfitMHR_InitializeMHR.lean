-- Prove2me | Definitions.Def_BilateralProfitMHR_InitializeMHR
-- name    : BilateralProfitMHR_InitializeMHR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-13T19:19:11.400574+00:00
-- url     : https://prove2.me/theorems/5b2de6f4-8c3a-438e-a4b7-12c59dec0d25
-- title:
--   Algorithm 4 — Initialize mhr: recursive-bisection probing, the estimates $\hat\mu$, the trigger and the region $\mathcal K$
-- statement:
--   This file encodes Algorithm 4 (Initialize mhr), which takes a horizon $T$ and a grid resolution $2\le K\le T$.
--
--   1. The grid is the triangle grid $G_K=\{(i/K,j/K):0\le i\le j\le K\}$.
--   2. The set $\{0,\dots,K\}$ is bisected recursively down to singletons: an interval $I=\{m,\dots,M\}$ with $m<M$ has midpoint $k_I=\lfloor (m+M)/2\rfloor$ and children $\{m,\dots,k_I\}$ and $\{k_I+1,\dots,M\}$. Each interval contributes $S_I=\{(r,k_I):r\in I,\ k_I\ge r\}\cup\{(k_I,r):r\in I,\ k_I<r\}$, and $S=\bigcup_I S_I$.
--   3. For the scales $\delta=1,1/2,1/4,\dots$ with $\delta\ge1/K$, every pair $(i,j)\in S$ is posted for $N=\lceil 2^{16}\log(2T)/\delta\rceil$ fresh rounds and $\overline P_{ij}$ is the fraction of these rounds with trade.
--   4. For $1\le i<j\le K-1$, with $k$ the midpoint of the first recursive split separating $i$ and $j$,
--   $$\hat\mu(i/K,j/K)=\frac{j-i}{K}\cdot\frac{\overline P_{ik}\,\overline P_{kj}}{\max\{\overline P_{ik},\overline P_{kj},\overline P_{kk}\}}\qquad(0/0=0),$$
--   and $\hat\mu(e)=0$ for every other $e\in G_K$.
--   5. At the first scale with $\max_{e\in G_K}\hat\mu(e)\ge 3\delta/2$ the procedure returns $\delta$ and $\mathcal K=\mathrm{conv}\{e\in G_K:\hat\mu(e)\ge3\delta/4\}$; if no scale triggers it returns "no trigger".
--
--   The file also records the number of trading rounds the procedure uses ($|S|\cdot N$ at every tested scale), the regret $\sum(\mu^\star-\mu(p_t,q_t))$ of these probing rounds, the grid maximizers of $\mu$, and the resolution $K=\lfloor c_0\sqrt T/\log(2T)\rfloor$ of Equation (28). These are the objects of Proposition 5.4 and Lemmas 3.3 and 5.3.
--
--   **Formalization Note** The probing rounds use fresh i.i.d. valuations, modelled as an array of independent samples indexed by (scale, grid pair, repetition); the run at a scale reads only that scale's samples, so events about the procedure have the same probability as for the sequential run, which stops at the trigger. "The first recursive split separating $i$ and $j$" is read as the midpoint of the smallest bisection interval containing both, so that $i\le k<j$. A scale index $h$ stands for $\delta=2^{-h}$.
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Algorithm 4, p.31 (PDF 33); round count, proof of Lemma 5.3, p.34 (PDF 36); Equation (28), p.33 (PDF 35)

import Mathlib
import Definitions.Def_BilateralProfitMHR_Model

namespace BilateralProfitMHR

open MeasureTheory BilateralProfit
open scoped Classical

/-! # Algorithm 4 (Initialize mhr)

Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…), Algorithm 4, p.31
(PDF 33), and the round count of the proof of Lemma 5.3, p.34 (PDF 36).

Input: horizon `T` and grid resolution `2 ≤ K ≤ T`. The triangle grid `G_K = 𝒜` is `Act K`.
The set `S` of probed pairs comes from recursively bisecting `{0, …, K}`: an interval
`I = {m, …, M}` with `m < M` has midpoint `k_I = ⌊(m + M)/2⌋` and children `{m, …, k_I}` and
`{k_I + 1, …, M}`; `S_I = {(r, k_I) : r ∈ I, k_I ≥ r} ∪ {(k_I, r) : r ∈ I, k_I < r}` and
`S = ⋃_I S_I`. For `δ = 1, 1/2, 1/4, …` with `δ ≥ 1/K` (scale index `h`, `δ = 2^{−h}`), every pair
of `S` is posted for `N_h = ⌈2^16 log(2T)/δ⌉` fresh rounds and `P̄_ij` is the fraction with trade;
for `1 ≤ i < j ≤ K − 1`, with `k` the midpoint of the first recursive split separating `i` and
`j`, `µ̂(i/K, j/K) = (j − i)/K · P̄_ik P̄_kj / max{P̄_ik, P̄_kj, P̄_kk}` (with `0/0 = 0`), and
`µ̂(e) = 0` for the other `e ∈ G_K`. At the first scale with `max_e µ̂(e) ≥ 3δ/2` the procedure
returns `(δ, 𝒦)`, `𝒦 = conv{e ∈ G_K : µ̂(e) ≥ 3δ/4}`; otherwise "no trigger".

**Formalization Note.** The probing rounds use fresh i.i.d. valuations. They are modelled as an
array of independent valuation pairs indexed by (scale `h`, grid pair `(i, j)`, repetition
`r < N_h`), each with law `D`; the run at scale `h` reads the samples of that scale only, so the
probability of any event about the procedure is the same as for the sequential run, which stops
at the trigger (samples of untested scales and of pairs outside `S` are never used). Reading of
"the first recursive split separating `i` and `j`": the midpoint of the smallest interval of the
bisection that contains both, so that `i ≤ k < j` (the reading under which the proof of
Proposition 5.4, p.60, holds as printed). Lean's `x / 0 = 0` is the paper's convention `0/0 = 0`
(a zero maximum forces a zero numerator). The recursions use the fuel `M − m + 1`, which is
enough because each level strictly shrinks the interval. -/

/-- The intervals `(min I, max I)` of the recursive bisection of `{m, …, M}` down to singletons
(fuel-driven). -/
def bisectAux : ℕ → ℕ → ℕ → Finset (ℕ × ℕ)
  | 0, m, M => {(m, M)}
  | f + 1, m, M =>
      if m < M then
        insert (m, M) (bisectAux f m ((m + M) / 2) ∪ bisectAux f ((m + M) / 2 + 1) M)
      else {(m, M)}

/-- The intervals of the recursive bisection of `{0, …, K}`. -/
def bisect (K : ℕ) : Finset (ℕ × ℕ) := bisectAux (K + 1) 0 K

/-- `S_I` for the interval `I = {I.1, …, I.2}`, with `k_I = ⌊(max I + min I)/2⌋`. -/
def sPairsOf (I : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc I.1 I.2).filter (fun r => r ≤ (I.1 + I.2) / 2)).image
      (fun r => (r, (I.1 + I.2) / 2)) ∪
    ((Finset.Icc I.1 I.2).filter (fun r => (I.1 + I.2) / 2 < r)).image
      (fun r => ((I.1 + I.2) / 2, r))

/-- The probed index pairs `S = ⋃_I S_I`. -/
def Spairs (K : ℕ) : Finset (ℕ × ℕ) := (bisect K).biUnion sPairsOf

/-- The midpoint of the first recursive split of `{m, …, M}` separating `i < j` (fuel-driven). -/
def sepMidAux : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, m, _ => m
  | f + 1, i, j, m, M =>
      if m < M then
        if j ≤ (m + M) / 2 then sepMidAux f i j m ((m + M) / 2)
        else if (m + M) / 2 < i then sepMidAux f i j ((m + M) / 2 + 1) M
        else (m + M) / 2
      else m

/-- The midpoint `k` of the first recursive split of `{0, …, K}` separating `i` and `j`. -/
def sepMid (K i j : ℕ) : ℕ := sepMidAux (K + 1) i j 0 K

/-- The number of tested scales: `δ = 2^{−h} ≥ 1/K` iff `h ≤ log₂ K`. -/
def numScales (K : ℕ) : ℕ := Nat.log 2 K + 1

/-- The scale `δ_h = 2^{−h}`. -/
noncomputable def delta (h : ℕ) : ℝ := (1 / 2 : ℝ) ^ h

/-- `N_h = ⌈2^16 log(2T)/δ_h⌉`, the number of fresh rounds per probed pair at scale `h`. -/
noncomputable def nSamp (T h : ℕ) : ℕ := ⌈(2 : ℝ) ^ 16 * Real.log (2 * T) / delta h⌉₊

/-- The index set of the probing samples: (scale, grid pair, repetition). -/
abbrev SampleIdx (K T : ℕ) : Type :=
  (h : Fin (numScales K)) × (Fin (K + 1) × Fin (K + 1)) × Fin (nSamp T h)

/-- A realization of all probing valuations. -/
abbrev Samples (K T : ℕ) : Type := SampleIdx K T → ℝ × ℝ

/-- The law of the probing valuations: i.i.d. with law `D`. -/
noncomputable def initLaw (K T : ℕ) (D : Measure (ℝ × ℝ)) : Measure (Samples K T) :=
  Measure.pi fun _ : SampleIdx K T => D

/-- `P̄_ij` at scale `h`: the fraction of the `N_h` probing rounds at `(i/K, j/K)` with trade
(`0` for indices out of range). -/
noncomputable def Pbar (K T h : ℕ) (ω : Samples K T) (i j : ℕ) : ℝ :=
  if hh : h < numScales K ∧ i < K + 1 ∧ j < K + 1 then
    (∑ r : Fin (nSamp T h),
        tradeBit (ω ⟨⟨h, hh.1⟩, (⟨i, hh.2.1⟩, ⟨j, hh.2.2⟩), r⟩) ((i : ℝ) / K, (j : ℝ) / K)) /
      (nSamp T h : ℝ)
  else 0

/-- The estimate `µ̂(e)` at scale `h` of the grid pair `e = (i/K, j/K) ∈ G_K`. -/
noncomputable def muHat (K T h : ℕ) (ω : Samples K T) (e : Act K) : ℝ :=
  if 1 ≤ (e.1.1 : ℕ) ∧ (e.1.1 : ℕ) < e.1.2 ∧ (e.1.2 : ℕ) < K then
    (((e.1.2 : ℕ) : ℝ) - ((e.1.1 : ℕ) : ℝ)) / K *
      (Pbar K T h ω e.1.1 (sepMid K e.1.1 e.1.2) * Pbar K T h ω (sepMid K e.1.1 e.1.2) e.1.2 /
        max (max (Pbar K T h ω e.1.1 (sepMid K e.1.1 e.1.2))
              (Pbar K T h ω (sepMid K e.1.1 e.1.2) e.1.2))
            (Pbar K T h ω (sepMid K e.1.1 e.1.2) (sepMid K e.1.1 e.1.2)))
  else 0

/-- Scale `h` triggers: `max_{e ∈ G_K} µ̂(e) ≥ 3δ_h/2`. -/
def Triggers (K T h : ℕ) (ω : Samples K T) : Prop :=
  ∃ e : Act K, 3 * delta h / 2 ≤ muHat K T h ω e

/-- The first triggering scale among `h = 0, …, numScales K − 1`, if any. -/
noncomputable def firstTrigger (K T : ℕ) (ω : Samples K T) : Option ℕ :=
  if hx : ∃ h, h < numScales K ∧ Triggers K T h ω then some (Nat.find hx) else none

/-- `𝒦 = conv{e ∈ G_K : µ̂(e) ≥ 3δ_h/4}` at scale `h`. -/
noncomputable def region (K T h : ℕ) (ω : Samples K T) : Set (ℝ × ℝ) :=
  convexHull ℝ ((fun e : Act K => pt K e.1) '' {e | 3 * delta h / 4 ≤ muHat K T h ω e})

/-- The output of Initialize mhr: `some (h, 𝒦)` (scale `δ_h` and region `𝒦`), or `none` for
"no trigger". -/
noncomputable def initOut (K T : ℕ) (ω : Samples K T) : Option (ℕ × Set (ℝ × ℝ)) :=
  (firstTrigger K T ω).map fun h => (h, region K T h ω)

/-- The scales actually tested ("reached") by the run. -/
noncomputable def testedScales (K T : ℕ) (ω : Samples K T) : Finset ℕ :=
  match firstTrigger K T ω with
  | some h => Finset.range (h + 1)
  | none => Finset.range (numScales K)

/-- The number of trading rounds used by Initialize mhr: `|S|·N_h` at every tested scale. -/
noncomputable def initRounds (K T : ℕ) (ω : Samples K T) : ℕ :=
  ∑ h ∈ testedScales K T ω, (Spairs K).card * nSamp T h

/-- The regret of the probing rounds, `∑_{rounds} (µ⋆ − µ(p_t, q_t))`: each pair of `S` is posted
`N_h` times at every tested scale. -/
noncomputable def filterRegret (K T : ℕ) (D : Measure (ℝ × ℝ)) (ω : Samples K T) : ℝ :=
  ∑ h ∈ testedScales K T ω,
    (nSamp T h : ℝ) * ∑ e ∈ Spairs K, (muStar D - muP D ((e.1 : ℝ) / K, (e.2 : ℝ) / K))

/-- `e ∈ G_K` maximizes `µ` over the triangle grid `G_K = 𝒜`. -/
def IsGridMax (K : ℕ) (D : Measure (ℝ × ℝ)) (e : Act K) : Prop :=
  ∀ e' : Act K, muP D (pt K e'.1) ≤ muP D (pt K e.1)

/-- The grid resolution of Equation (28), `K = ⌊c₀ √T / log(2T)⌋`. -/
noncomputable def Kpar (c0 : ℝ) (T : ℕ) : ℕ := ⌊c0 * Real.sqrt T / Real.log (2 * T)⌋₊

end BilateralProfitMHR


