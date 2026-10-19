-- Prove2me | Definitions.Def_SpeedFactory_BreakEven_Dynamics
-- name    : SpeedFactory_BreakEven_Dynamics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:09.6663+00:00
-- url     : https://prove2.me/theorems/8248b102-0124-4e1f-b074-f38491c3579c
-- title:
--   §2–§3 and Online App. A, pp. 5, 8, 33, 36 — TBS-POUT and OUT inventory recursions, period costs (2)–(4), long-run average (5), optimized costs C^{TBS-POUT,k⋆} and C^s
-- statement:
--   This file defines the two replenishment systems of the paper and their long-run average costs, directly from the dynamics.
--
--   **Period costs.** For inventory $x$, capacity $k$ and local order $q$, the holding/backlog cost (2) and the local production cost (4) are
--   $$C^i=h[x]^++b[-x]^+,\qquad C^q=uk+um[q-k]^+.$$
--   The long-run average of a sequence of per-period costs $(c_t)$ is
--   $$\operatorname{lrAvg}(c)=\liminf_{n\to\infty}\frac1n\sum_{t=1}^n c_t .\qquad (5)$$
--
--   **TBS-POUT (dual sourcing).** Fix an allocation $\gamma$, a smoothing parameter $\alpha$, a safety stock $i^\star$ and a deterministic initial inventory $i_0$. The global order is the constant $\mu(1-\gamma)$ (8), so $\mu(1-\gamma)$ is received every period. The local order is $q_t=\mu\gamma+(1-\alpha)(i^\star-i_t)$ (9), received one period later. The inventory evolves by (1):
--   $$i_t=i_{t-1}-d_t+\mu(1-\gamma)+q_{t-1},\qquad t\ge1 .$$
--   With capacity $k$, the expected cost of period $t$ is $\mathbb E[C^i(i_t)]+p\mu(1-\gamma)+\mathbb E[C^q(k,q_t)]$, and $C^{\mathrm{TBS}}(\gamma,\alpha,i^\star,k)$ is its long-run average. Its inventory and capacity parts $C_i(i^\star)$ and $C_q(i^\star,k)$ are the long-run averages of $\mathbb E[C^i(i_t)]$ and $\mathbb E[C^q(k,q_t)]$. The optimized dual-sourcing cost is
--   $$C^{\mathrm{TBS\text{-}POUT},k^\star}(\gamma,\alpha)=\inf_{(i^\star,k)\in\mathbb R^2}C^{\mathrm{TBS}}(\gamma,\alpha,i^\star,k).$$
--
--   **OUT (single off-shore sourcing).** Fix a target $i^\star$, a deterministic initial inventory $i_0$ and deterministic outstanding orders $q^g_{-1},\dots,q^g_{-(L-1)}$. For $t\ge1$, the inventory evolves by (55), $i_t=i_{t-1}-d_t+q^g_{t-L}$. In every period $t\ge0$, the order-up-to rule (75) with the iid forecast $\hat d^\star=\mu$ orders
--   $$q^g_t=(i^\star+L\mu)-\Big(i_t+\sum_{j=1}^{L-1}q^g_{t-j}\Big).$$
--   The expected cost of period $t$ is $\mathbb E[C^i(i_t)]+p\,\mathbb E[q^g_t]$, its long-run average is $C^{\mathrm{OUT}}(i^\star)$, and the benchmark is
--   $$C^s=\inf_{i^\star\in\mathbb R}C^{\mathrm{OUT}}(i^\star).$$
--
--   These are the costs that Propositions 1, 3, 4 and equations (18)–(20) are about.
--
--   **Formalization Note** The long-run average (5) is printed pathwise; here it is applied to expected period costs, which is what the proof of Proposition 1 computes. Safety stocks and capacities range over all of $\mathbb R$ and orders may be negative, as in the paper's linearized model. The TBS global receipts equal $\mu(1-\gamma)$ from the first period on, so the lead time drops out of the TBS system. $C^s$ is the optimized cost of the OUT policy only; the paper's claim that OUT is optimal among single-sourcing policies is not built in. Periods start at $t=1$; $d_0$ is never used.
-- source:
--   Boute, Disney, Gijsbrechts, Van Mieghem, Dual Sourcing and Smoothing under Non-Stationary Demand Time Series: Re-shoring with SpeedFactories, accepted manuscript (revised Nov 28, 2020), p. 5 ((1)–(4)), p. 6 ((5)), p. 8 ((8), (9)), p. 33 ((55)), p. 36 ((75)–(76))

import Mathlib
import Definitions.Def_SpeedFactory_BreakEven_Model

open MeasureTheory ProbabilityTheory

namespace SpeedFactory.BreakEven

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The per-period inventory holding and backlog cost `C^i_t = h[i_t]⁺ + b[−i_t]⁺`, (2), p. 5. -/
noncomputable def invCost (M : Model) (x : ℝ) : ℝ := M.h * max x 0 + M.b * max (-x) 0

/-- The per-period local production cost `C^q_t = uk + um[q_t − k]⁺`, (4), p. 5, at capacity
`k` and local order `q`. -/
noncomputable def capCost (M : Model) (k q : ℝ) : ℝ := M.u * k + M.u * M.m * max (q - k) 0

/-- The long-run average of a sequence of per-period costs, `liminf_{n→∞} (1/n) Σ_{t=1}^n c_t`,
(5), p. 6.

**Formalization Note.** It is applied to *expected* per-period costs (the expected Cesàro
reading of (5)), which is what the proof of Proposition 1, (39)–(48), computes. -/
noncomputable def lrAvg (c : ℕ → ℝ) : ℝ :=
  Filter.liminf (fun n : ℕ => (∑ t ∈ Finset.Icc 1 n, c t) / n) Filter.atTop

/-- The finished-goods inventory `i_t` under the TBS-POUT policy, (1), (8), (9), pp. 5 and 8:
`i_t = i_{t−1} − d_t + q^g_{t−L} + q_{t−1}`, with constant global receipts
`q^g_{t−L} = µ(1 − γ)` and local orders `q_{t−1} = µγ + (1 − α)(i⋆ − i_{t−1})`.
The initial inventory `i_0 = i0` is deterministic.

**Formalization Note.** The global order is constant, so the receipts equal `µ(1 − γ)` in every
period `t ≥ 1` (the policy is in force before time 0); `L` drops out of the TBS dynamics, as the
paper says (p. 12). Local orders may be negative (the linearized model, no positive part). -/
noncomputable def invTBS (M : Model) (γ α iStar i0 : ℝ) (d : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => i0
  | t + 1 => fun ω =>
      invTBS M γ α iStar i0 d t ω - d (t + 1) ω + M.μ * (1 - γ)
        + (M.μ * γ + (1 - α) * (iStar - invTBS M γ α iStar i0 d t ω))

/-- The local (SpeedFactory) order placed in period `t`, `q_t = µγ + (1 − α)(i⋆ − i_t)`, (9),
p. 8. -/
noncomputable def qTBS (M : Model) (γ α iStar i0 : ℝ) (d : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  M.μ * γ + (1 - α) * (iStar - invTBS M γ α iStar i0 d t ω)

/-- The expected total cost of period `t` under TBS-POUT with allocation `γ`, smoothing `α`,
safety stock `i⋆` and capacity `k`: `E[C^i_t + C^p_t + C^q_t]` with `C^p_t = p µ(1 − γ)`,
(2)–(4), (8). -/
noncomputable def periodCostTBS (M : Model) (γ α iStar k i0 : ℝ) (P : Measure Ω)
    (d : ℕ → Ω → ℝ) (t : ℕ) : ℝ :=
  ∫ ω, (invCost M (invTBS M γ α iStar i0 d t ω) + M.p * (M.μ * (1 - γ))
          + capCost M k (qTBS M γ α iStar i0 d t ω)) ∂P

/-- The long-run average cost (5) of TBS-POUT with parameters `(γ, α, i⋆, k)`. -/
noncomputable def lrCostTBS (M : Model) (γ α iStar k i0 : ℝ) (P : Measure Ω)
    (d : ℕ → Ω → ℝ) : ℝ :=
  lrAvg (periodCostTBS M γ α iStar k i0 P d)

/-- The long-run average inventory cost `C_i` (the `C^i_t` part of (5)) of TBS-POUT. -/
noncomputable def lrInvCostTBS (M : Model) (γ α iStar i0 : ℝ) (P : Measure Ω)
    (d : ℕ → Ω → ℝ) : ℝ :=
  lrAvg (fun t => ∫ ω, invCost M (invTBS M γ α iStar i0 d t ω) ∂P)

/-- The long-run average local production cost `C_q` (the `C^q_t` part of (5)) of TBS-POUT at
capacity `k`. -/
noncomputable def lrCapCostTBS (M : Model) (γ α iStar k i0 : ℝ) (P : Measure Ω)
    (d : ℕ → Ω → ℝ) : ℝ :=
  lrAvg (fun t => ∫ ω, capCost M k (qTBS M γ α iStar i0 d t ω) ∂P)

/-- The optimized TBS-POUT cost `C^{TBS-POUT,k⋆}` at allocation `γ` and smoothing `α`:
the infimum of the long-run cost over the safety stock `i⋆ ∈ ℝ` and the capacity `k ∈ ℝ`.

**Formalization Note.** `i⋆` and `k` range over all of `ℝ` (the linearized model of
Proposition 1 allows `k⋆ < 0`, p. 9). -/
noncomputable def costTBS (M : Model) (γ α i0 : ℝ) (P : Measure Ω) (d : ℕ → Ω → ℝ) : ℝ :=
  sInf (Set.range fun x : ℝ × ℝ => lrCostTBS M γ α x.1 x.2 i0 P d)

/-- The pipeline initial condition `(q^g_{−1}, …, q^g_{−(L−1)})`, read as a sequence
(`j ↦ q^g_{−1−j}`, zero beyond `L − 2`). -/
noncomputable def pipeSeq (M : Model) (pipe0 : Fin (M.L - 1) → ℝ) (j : ℕ) : ℝ :=
  if hj : j < M.L - 1 then pipe0 ⟨j, hj⟩ else 0

/-- The state of the single-sourcing order-up-to (OUT) system at the start of period `t`'s
ordering decision: the inventory `i_t` and the outstanding global orders
`j ↦ q^g_{t−1−j}` (`j = 0, …, L − 2`). (55), p. 33, and (75)–(76), p. 36, with the iid
forecast `d̂⋆_{t+i,t} = µ` (p. 33):
`i_t = i_{t−1} − d_t + q^g_{t−L}` and
`q^g_t = (i⋆ + Lµ) − (i_t + Σ_{i=1}^{L−1} q^g_{t−i})`.
The initial inventory `i0` and pipeline `pipe0` are deterministic and arbitrary. -/
noncomputable def outState (M : Model) (iStar i0 : ℝ) (pipe0 : Fin (M.L - 1) → ℝ)
    (d : ℕ → Ω → ℝ) (ω : Ω) : ℕ → ℝ × (ℕ → ℝ)
  | 0 => (i0, pipeSeq M pipe0)
  | t + 1 =>
      let s := outState M iStar i0 pipe0 d ω t
      let q := iStar + M.L * M.μ - (s.1 + ∑ j ∈ Finset.range (M.L - 1), s.2 j)
      (s.1 - d (t + 1) ω + s.2 (M.L - 2), fun j => Nat.casesOn j q s.2)

/-- The inventory `i_t` under the single-sourcing OUT policy, (55), p. 33. -/
noncomputable def invOUT (M : Model) (iStar i0 : ℝ) (pipe0 : Fin (M.L - 1) → ℝ)
    (d : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  (outState M iStar i0 pipe0 d ω t).1

/-- The global order `q^g_t` placed in period `t` under the single-sourcing OUT policy with
target inventory position `i⋆ + Lµ`, (75)–(76), p. 36. -/
noncomputable def qOUT (M : Model) (iStar i0 : ℝ) (pipe0 : Fin (M.L - 1) → ℝ)
    (d : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  let s := outState M iStar i0 pipe0 d ω t
  iStar + M.L * M.μ - (s.1 + ∑ j ∈ Finset.range (M.L - 1), s.2 j)

/-- The long-run average cost (5) of single off-shore sourcing with the OUT policy and safety
stock `i⋆`: expected holding/backlog cost (2) plus purchasing cost (3), no local capacity. -/
noncomputable def lrCostOUT (M : Model) (iStar i0 : ℝ) (pipe0 : Fin (M.L - 1) → ℝ)
    (P : Measure Ω) (d : ℕ → Ω → ℝ) : ℝ :=
  lrAvg (fun t => ∫ ω, (invCost M (invOUT M iStar i0 pipe0 d t ω)
                          + M.p * qOUT M iStar i0 pipe0 d t ω) ∂P)

/-- The single-sourcing benchmark cost `C^s`: the infimum over the safety stock `i⋆ ∈ ℝ` of the
long-run cost of the OUT policy (p. 11, (18)).

**Formalization Note.** `C^s` is the optimized OUT-policy cost; the paper's assertion that the
OUT policy is optimal among all single-sourcing policies is not built in. -/
noncomputable def costOUT (M : Model) (i0 : ℝ) (pipe0 : Fin (M.L - 1) → ℝ) (P : Measure Ω)
    (d : ℕ → Ω → ℝ) : ℝ :=
  sInf (Set.range fun s : ℝ => lrCostOUT M s i0 pipe0 P d)

end SpeedFactory.BreakEven


