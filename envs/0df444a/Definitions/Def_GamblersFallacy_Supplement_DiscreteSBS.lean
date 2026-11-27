-- Prove2me | Definitions.Def_GamblersFallacy_Supplement_DiscreteSBS
-- name    : GamblersFallacy_Supplement_DiscreteSBS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:14:50.320678+00:00
-- url     : https://prove2.me/theorems/f573f905-604f-5f32-b4a7-e6ebfefcb981
-- title:
--   The joint size/inter-arrival law $p_{kj}$ and the biased estimates $\tilde p_{kj}(n)$
-- statement:
--   Let $p_{kj}$ be the joint probability that a demand of size $k\in[K]=\{1,\dots,K\}$ arrives with inter-arrival time $j\in[J]$, with $p_{kj}\ge0$ and $\sum_{k,j}p_{kj}=1$. The cycles $(Z_t,Y_t)$, $t\ge1$, are i.i.d. with this law, so a cycle has mass $p_{kj}$ at $(Z,Y)=(j,k)$.
--
--   In the notation of the CPUGS, with $[\tau]=\{1,\dots,\tau\}$, $[\tau]^+=[\tau]\cup\{n\}$ and $Y_n=\max\{1,X_n\}$, the **biased estimate** of Theorem 4 is
--   $$
--   \tilde p_{kj}(n)=\mathbb E\Bigg[\sum_{t\in[\tau]}\frac{\chi(Z_t=j,Y_t=k)}{\big(\sum_{s\in[\tau]^+,s\ne t}Y_s+k\big)/k}+\frac{\chi\big(\sum_{s=1}^{\tau}Z_s=n-j\big)\,\chi(Z_{\tau+1}=j,X_n=k)}{\big(\sum_{s\in[\tau]}Y_s+k\big)/k}\Bigg].
--   $$
--
--   It replaces $p_{kj}$ in the single-cycle cost when the CPUGS is evaluated over a finite horizon (Theorem 4, problem (4)).
--
--   **Formalization Note** The cycle law is the measure $\sum_{k\in[K]}\sum_{j\in[J]}p_{kj}\,\delta_{(j,k)}$ on $\mathbb N\times\mathbb R$. The event $\sum_{s=1}^\tau Z_s=n-j$ is written $Z_1+\dots+Z_\tau+j=n$, which avoids natural-number subtraction. The expectation is a lower Lebesgue integral in $[0,\infty]$.
-- source:
--   Bi–He–Teo, Taming the Long Tail, MSOM (2023), doi:10.1287/msom.2023.1217, §4.2.1, p.19 (p_kj, D ∈ [K]); Theorem 4, p.21 (p̃_kj(n), [τ]^+, Y_n = max{1, X_n})

import Mathlib
import Definitions.Def_GamblersFallacy_Supplement_CPUGS

namespace GamblersFallacy.Supplement

open MeasureTheory

/-- **The joint law `p_kj` of demand size and inter-arrival time** (§4.2.1, p.19).
S. Bi, L. He, C.-P. Teo, *Taming the Long Tail: The Gambler's Fallacy in Intermittent Demand
Management*, MSOM (2023), doi:10.1287/msom.2023.1217, p.19: "Let p_kj denote the joint probability
that demand of size k arrives with inter-arrival time of j periods, with j ∈ [J] and k ∈ [K]",
the nonzero demand being `D ∈ [K] = {1, 2, …, K}`.

**Formalization Note.** `q k j = p_kj`; only the entries with `k ∈ [K]`, `j ∈ [J]` are read. -/
structure JointDemandLaw where
  /-- the largest inter-arrival time `J` -/
  J : ℕ
  /-- the largest demand size `K` -/
  K : ℕ
  /-- `q k j = p_kj = P(Y = k, Z = j)` -/
  q : ℕ → ℕ → ℝ
  nonneg : ∀ k j, 0 ≤ q k j
  sum_eq_one : ∑ k ∈ Finset.Icc 1 K, ∑ j ∈ Finset.Icc 1 J, q k j = 1

/-- The law of one cycle `(Z_t, Y_t)` on `ℕ × ℝ`: mass `p_kj` at `(j, k)`. -/
noncomputable def JointDemandLaw.cycleLaw (D : JointDemandLaw) : Measure (ℕ × ℝ) :=
  ∑ k ∈ Finset.Icc 1 D.K, ∑ j ∈ Finset.Icc 1 D.J,
    ENNReal.ofReal (D.q k j) • Measure.dirac ((j, (k : ℝ)) : ℕ × ℝ)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The biased estimate `p̃_kj(n)`** (Theorem 4, p.21, as printed):
`p̃_kj(n) := E[ Σ_{t∈[τ]} χ(Z_t = j, Y_t = k) / ((Σ_{s∈[τ]⁺, s≠t} Y_s + k)/k)
  + χ(Σ_{s=1}^τ Z_s = n − j) χ(Z_{τ+1} = j, X_n = k) / ((Σ_{s∈[τ]} Y_s + k)/k) ]`,
with `[τ]⁺ = [τ] ∪ {n}` and `Y_n = max{1, X_n}`.

**Formalization Note.** `Σ_{s∈[τ]⁺, s≠t} Y_s` is `Σ_{s∈[τ], s≠t} Y_s + max{1, X_n}`. The event
`Σ_{s=1}^τ Z_s = n − j` is written `Z₁ + ⋯ + Z_τ + j = n`, which avoids natural-number
subtraction (for `j > n` the event is empty, as in the paper). The expectation is a lower Lebesgue
integral of the nonnegative integrand. -/
noncomputable def biasedJointWeight (P : Measure Ω) (Z : ℕ → Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (n k j : ℕ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal
    ((∑ t ∈ Finset.Icc 1 (lastCycle Z n ω),
        (if Z t ω = j ∧ Y t ω = k then (1 : ℝ) else 0) /
          (((∑ s ∈ (Finset.Icc 1 (lastCycle Z n ω)).erase t, Y s ω) +
              max 1 (demandAtHorizon Z Y n ω) + k) / k)) +
      (if arrivalTime Z (lastCycle Z n ω) ω + j = n ∧ Z (lastCycle Z n ω + 1) ω = j ∧
          demandAtHorizon Z Y n ω = k then (1 : ℝ) else 0) /
        (((∑ s ∈ Finset.Icc 1 (lastCycle Z n ω), Y s ω) + k) / k)) ∂P

end GamblersFallacy.Supplement


