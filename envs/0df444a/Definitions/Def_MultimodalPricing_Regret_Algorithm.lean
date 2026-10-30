-- Prove2me | Definitions.Def_MultimodalPricing_Regret_Algorithm
-- name    : MultimodalPricing_Regret_Algorithm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T08:03:19.704003+00:00
-- url     : https://prove2.me/theorems/67fface1-81c3-4d76-b04f-18b82e46cfcc
-- title:
--   Equal-bin multimodal pricing transitions
-- statement:
--   For horizon $T$ and dimension $k$, set $N=\lceil T^{1/(2k+1)}\rceil$, $a_j=a+j(b-a)/N$, and $\Delta=C((b-a)/N)^k$. Bin $j<N$ is $[a_j,a_{j+1}]$. Its history consists exactly of earlier observations with recorded label $j$, ordered chronologically. The visit count is its length, and its cumulative revenue is the sum of price times demand.
--
--   A nonempty bin has index $s_j/n_j+(\Delta+2\max\{1,C\}/\sqrt{n_j})3k\log(2kT)$. An empty bin has index $b$, as in the printed footnote. Each predictable selected label maximizes the index; the posted price is a local BiasedLinearBandit output with $\delta=1/T^2$. Prefix filtering implements the append update of the selected bin only. Equal closed bins share endpoints, but the label assigns each observation to just one bin. This encodes transitions, not a confidence event or performance guarantee.
-- source:
--   Wang, Chen, Simchi-Levi, Multi-Modal Dynamic Pricing, https://doi.org/10.1287/mnsc.2020.3819, supplied artifact (published metadata; SSRN 3489355 footer), Algorithm 1, printed/PDF p. 11

import Definitions.Def_MultimodalPricing_Regret_LocalBandit

open MeasureTheory

noncomputable section

namespace MultimodalPricing.Regret

/-- The prescribed ceiling; a positive horizon makes this positive. -/
def binCount (k T : ℕ) : ℕ := ⌈(T : ℝ) ^ ((1 : ℝ) / (2 * k + 1))⌉₊

def binEdge (a b : ℝ) (N j : ℕ) : ℝ := a + j * (b - a) / N

def binBias (k N : ℕ) (C a b : ℝ) : ℝ := C * ((b - a) / N) ^ k

/-- Membership uses the recorded bin label, so shared endpoints do not duplicate data. -/
def binHistory {Ω : Type*} (p d : ℕ → Ω → ℝ) (j : ℕ → Ω → ℕ)
    (n bin : ℕ) (ω : Ω) : History :=
  ((List.range n).filter (fun i => j i ω = bin)).map (fun i => (p i ω, d i ω))

def binRevenue (h : History) : ℝ := (h.map (fun z => z.1 * z.2)).sum

/-- Exactly the empty-bin footnote of Algorithm 1. -/
def confidenceIndex (k T : ℕ) (C Δ pmax : ℝ) (h : History) : ℝ :=
  if h = [] then pmax else
    binRevenue h / h.length +
      (Δ + 2 * max 1 C / Real.sqrt h.length) * (3 * k * Real.log (2 * k * T))

/-- Algorithms 1 and 2 as nonanticipating, set-valued transitions.
All maximizing-bin and maximizing-price ties are universally covered. -/
def AlgorithmRun {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (k T : ℕ) (C a b : ℝ) (O : Observation Ω) (j : ℕ → Ω → ℕ) : Prop :=
  (∀ n < T, Measurable[O.info n] (j n)) ∧
  ∀ᵐ ω ∂μ, ∀ n < T,
    let N := binCount k T
    let Δ := binBias k N C a b
    let h := fun bin => binHistory O.price O.demand j n bin ω
    j n ω < N ∧
    (∀ bin < N,
      confidenceIndex k T C Δ b (h bin) ≤ confidenceIndex k T C Δ b (h (j n ω))) ∧
    LocalChoice k (binEdge a b N (j n ω)) (binEdge a b N (j n ω + 1))
      C Δ (1 / (T : ℝ) ^ 2) (h (j n ω)) (O.price n ω)

end MultimodalPricing.Regret


