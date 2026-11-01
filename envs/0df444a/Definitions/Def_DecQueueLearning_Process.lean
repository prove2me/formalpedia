-- Prove2me | Definitions.Def_DecQueueLearning_Process
-- name    : DecQueueLearning_Process
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:41:21.328302+00:00
-- url     : https://prove2.me/theorems/b22235be-fb2d-490d-a472-f22460824f6c
-- title:
--   The DAM processes: DAM.K, DAM.FE, DAM.UPDATE, queue lengths, events $\mathcal E_P$, $\mathcal E_W$, collected samples
-- statement:
--   A **DAM policy** fixes, at the start $t_0$ of each epoch $\ell$, each queue's mode from its own data only: its queue length $Q_i(t_0)$, its estimates $\hat\mu_{i,\cdot}(t_0)$, its sample counts $n_{i,\cdot}(t_0)$, its exploration coin, its explored-server sample and $\eta_i$. The epoch then runs the auction of one epoch, the queues evolve by eq. (1),
--   $$
--   Q_i(t+1)=(Q_i(t)+A_i(t)-S_i(t))^+,\qquad Q_i(1)=0,
--   $$
--   and the estimates of an exploring queue are updated by **DAM.UPDATE** (Algorithm 5): with $Y(t)$ the indicator that the request is successful at slot $t\in[t_s,t_e]$, nothing changes if no request succeeded; otherwise, with $\tau$ the first success, $\hat n=n+t_e-\tau$ and $\hat\mu=(n\hat\mu+\sum_{t=\tau+1}^{t_e}Y(t))/\hat n$.
--
--   1. **DAM.K** (Algorithm 1): every queue converges with weights $w_{i,j}=\mu_{i,j}Q_i(t_0)$.
--   2. **DAM.FE** (Algorithm 4): a queue whose exploration coin is $1$ explores its sampled server with bid $(t_0+L_{\mathrm{epoch}}+1)(1+\eta_i)$; otherwise it converges with weights $\bar\mu_{i,j}(t_0)Q_i(t_0)$, where
--   $$
--   \bar\mu_{i,j}(t_0)=\begin{cases}\min\big(1,\hat\mu_{i,j}(t_0)+\sqrt{3\ln t_0/n_{i,j}(t_0)}\big)&n_{i,j}(t_0)\ge1,\\ 0&\text{otherwise.}\end{cases}
--   $$
--
--   At an epoch start $t_0$ the **events** are $\mathcal E_P$: some queue explores in this epoch; and $\mathcal E_W$: there is a pair $(i,j)$ with $\mu_{i,j}>0$ such that $|\hat\mu_{i,j}(t_0)-\mu_{i,j}|>\Delta_{i,j}(t_0)$ or $\Delta_{i,j}(t_0)>\tfrac1{16}\varepsilon\delta$, where $\Delta_{i,j}(t_0)=\sqrt{3\ln t_0/n_{i,j}(t_0)}$ and $\Delta=\infty$ when $n_{i,j}(t_0)=0$. The module also lists, in order, the samples $Y(\tau+1),\dots,Y(t_e)$ that DAM.UPDATE collects for each pair up to an epoch start, and defines the guard of the corrected Lemma 4.1: if queue $i$ explores server $j$ in epoch $\ell$, it outbids at $j$ every non-exploring queue in every slot of the epoch.
--
--   **Formalization Note** Unvisited estimates carry over between epochs. In $\mathcal E_W$ the case $n_{i,j}(t_0)=0$ is an explicit disjunct, since $\sqrt{x/0}=0$ in Lean.
-- source:
--   Freund, Lykouris, Weng, Efficient decentralized multi-agent learning in asymmetric bipartite queueing systems, arXiv:2206.03324v3, eq. (1) p. 7; Algorithm 1 p. 10; Algorithms 4–5 pp. 17–18; ℰ_P, ℰ_W pp. 18–19

import Mathlib
import Definitions.Def_DecQueueLearning_System
import Definitions.Def_DecQueueLearning_Constants
import Definitions.Def_DecQueueLearning_TieRules
import Definitions.Def_DecQueueLearning_Auction
import Definitions.Def_DecQueueLearning_ProbSpace

open Finset Classical

namespace DecQueueLearning

/-- The local data of all queues at the start `t₀` of an epoch: queue lengths `Qᵢ(t₀)`, sample
means `µ̂ᵢⱼ(t₀)` and sample counts `nᵢⱼ(t₀)`. -/
structure EpochData (N K : ℕ) where
  Q : Fin N → ℕ
  muHat : Fin N → Fin K → ℝ
  n : Fin N → Fin K → ℕ

/-- All queues initially empty, `µ̂ᵢⱼ = 0`, `nᵢⱼ = 0` (p. 7; Algorithm 4, line 3). -/
def EpochData.init {N K : ℕ} : EpochData N K := ⟨0, 0, 0⟩

/-- A **DAM policy**: what queue `i` does in epoch `ℓ` (starting at slot `t₀`), as a function of
its own local data only: `Qᵢ(t₀)`, `µ̂ᵢ·(t₀)`, `nᵢ·(t₀)`, its exploration coin `E_ℓ`, its explored
server sample and its perturbation `ηᵢ`. Arguments: `ℓ t₀ i Qᵢ µ̂ᵢ nᵢ Eℓ σ ηᵢ`. -/
abbrev Policy (N K : ℕ) :=
  ℕ → ℕ → Fin N → ℕ → (Fin K → ℝ) → (Fin K → ℕ) → Bool → Fin K → ℝ → Mode K

/-- **DAM.UPDATE** (Algorithm 5, arXiv:2206.03324v3, p. 18) for the pair `(i, σ(i))`, with
`Y t = 1{request to σ(i) is successful at slot t}` for `t ∈ [t_s, t_e]`: if no request succeeded,
return `(µ̂, n)`; else, with `τ = min{t ∈ [t_s, t_e] : Y t = 1}`, return
`µ̂′ = (n µ̂ + Σ_{t=τ+1}^{t_e} Y t)/n̂` and `n̂ = n + t_e − τ`. -/
noncomputable def damUpdate (ts te : ℕ) (Y : ℕ → Bool) (mh : ℝ) (n : ℕ) : ℝ × ℕ :=
  if (∑ t ∈ Icc ts te, if Y t then (1 : ℕ) else 0) = 0 then (mh, n)
  else
    let τ := sInf {t | t ∈ Icc ts te ∧ Y t = true}
    ((n * mh + ∑ t ∈ Icc (τ + 1) te, if Y t then (1 : ℝ) else 0) / ((n + te - τ : ℕ) : ℝ),
      n + te - τ)

section Process

variable {N K : ℕ} (ε δ : ℝ) (rules : TieRules N K) (pol : Policy N K) (ω : Omega N K)

/-- The modes of all queues in epoch `ℓ`, from the epoch-start data `d`. -/
noncomputable def modesOf (ℓ : ℕ) (d : EpochData N K) : Fin N → Mode K := fun i =>
  pol ℓ (epochStart (Lepoch N K ε δ) ℓ) i (d.Q i) (d.muHat i) (d.n i) (exploreCoin ω ℓ i)
    (exploreServer ω ℓ i) (eta ω i)

/-- The auction run of epoch `ℓ` from the epoch-start data `d`. -/
noncomputable def runOf (ℓ : ℕ) (d : EpochData N K) : ℕ → Fin N → AState K :=
  auctionRun ε δ rules (modesOf ε δ pol ω ℓ d) (eta ω) (services ω) (epochStart (Lepoch N K ε δ) ℓ)

/-- Queue `i`'s request is successful in slot `t` of epoch `ℓ`. -/
def servedIn (ℓ : ℕ) (d : EpochData N K) (t : ℕ) (i : Fin N) : Prop :=
  Served rules (services ω) t
    (stateAt (runOf ε δ rules pol ω ℓ d) (epochStart (Lepoch N K ε δ) ℓ) t) i

/-- Queue lengths within epoch `ℓ`: `qIn ℓ d k = Q(t₀ + k)`, by eq. (1),
`Qᵢ(t + 1) = (Qᵢ(t) + Aᵢ(t) − Sᵢ(t))⁺`. -/
noncomputable def qIn (ℓ : ℕ) (d : EpochData N K) : ℕ → Fin N → ℕ
  | 0 => d.Q
  | k + 1 => fun i =>
      qIn ℓ d k i + (if arrivals ω (epochStart (Lepoch N K ε δ) ℓ + k) i then 1 else 0) -
        (if servedIn ε δ rules pol ω ℓ d (epochStart (Lepoch N K ε δ) ℓ + k) i then 1 else 0)

/-- The data at the start of epoch `ℓ + 1` from that of epoch `ℓ`: queue lengths
`Q(t₀ + L_epoch)`, and for each exploring queue `i` with server `σ(i)` the pair
`(µ̂_{i,σ(i)}, n_{i,σ(i)})` updated by DAM.UPDATE over `[t₀, t₀ + L_epoch − 1]` (Algorithm 4,
line 10); all other estimates are unchanged. -/
noncomputable def nextData (ℓ : ℕ) (d : EpochData N K) : EpochData N K where
  Q := qIn ε δ rules pol ω ℓ d (Lepoch N K ε δ)
  muHat := fun i j =>
    match modesOf ε δ pol ω ℓ d i with
    | .explore j' _ =>
      if j' = j then
        (damUpdate (epochStart (Lepoch N K ε δ) ℓ)
          (epochStart (Lepoch N K ε δ) ℓ + Lepoch N K ε δ - 1)
          (fun t => decide (servedIn ε δ rules pol ω ℓ d t i)) (d.muHat i j) (d.n i j)).1
      else d.muHat i j
    | .converge _ => d.muHat i j
  n := fun i j =>
    match modesOf ε δ pol ω ℓ d i with
    | .explore j' _ =>
      if j' = j then
        (damUpdate (epochStart (Lepoch N K ε δ) ℓ)
          (epochStart (Lepoch N K ε δ) ℓ + Lepoch N K ε δ - 1)
          (fun t => decide (servedIn ε δ rules pol ω ℓ d t i)) (d.muHat i j) (d.n i j)).2
      else d.n i j
    | .converge _ => d.n i j

/-- Epoch-start data, by recursion: `dataAux m` is the data at the start of epoch `m + 1`. -/
noncomputable def dataAux : ℕ → EpochData N K
  | 0 => EpochData.init
  | m + 1 => nextData ε δ rules pol ω (m + 1) (dataAux m)

/-- The data `(Q(t₀), µ̂(t₀), n(t₀))` at the start `t₀ = (ℓ − 1) L_epoch + 1` of epoch `ℓ ≥ 1`. -/
noncomputable def epochData (ℓ : ℕ) : EpochData N K := dataAux ε δ rules pol ω (ℓ - 1)


/-- **The queue length** `Qᵢ(t)` at the start of slot `t ≥ 1` (so `Qᵢ(1) = 0`) when all queues
follow the policy `pol`. -/
noncomputable def queue (i : Fin N) (t : ℕ) : ℕ :=
  qIn ε δ rules pol ω (epochOf (Lepoch N K ε δ) t) (epochData ε δ rules pol ω (epochOf (Lepoch N K ε δ) t))
    (t - epochStart (Lepoch N K ε δ) (epochOf (Lepoch N K ε δ) t)) i

/-- The auction run of epoch `ℓ` of the process. -/
noncomputable def epochAuction (ℓ : ℕ) : ℕ → Fin N → AState K :=
  runOf ε δ rules pol ω ℓ (epochData ε δ rules pol ω ℓ)

end Process

/-- **DAM.K** (Algorithm 1, arXiv:2206.03324v3, p. 10): in every epoch every queue runs
DAM.CONVERGE with the weights `wᵢⱼ = µᵢⱼ Qᵢ(t₀)` (known service rates) and then DAM.COMMIT. -/
def damKPolicy {N K : ℕ} (s : System N K) : Policy N K :=
  fun _ _ i q _ _ _ _ _ => .converge fun j => s.mu i j * q

/-- The optimistic estimate of Algorithm 4, line 12 (p. 17):
`µ̄ᵢⱼ(t₀) = min(1, µ̂ᵢⱼ(t₀) + √(3 ln t₀ / nᵢⱼ(t₀)))` if `nᵢⱼ(t₀) ≥ 1`, and `0` otherwise. -/
noncomputable def muBar (t0 : ℕ) (mh : ℝ) (n : ℕ) : ℝ :=
  if 1 ≤ n then min 1 (mh + Real.sqrt (3 * Real.log t0 / n)) else 0

/-- **DAM.FE** (Algorithm 4, arXiv:2206.03324v3, p. 17): in epoch `ℓ` with start `t₀`, a queue
whose coin `E_ℓ` is `1` explores its uniformly sampled server `σ(i)` with bid
`(t₀ + L_epoch + 1)(1 + ηᵢ)`; otherwise it runs DAM.CONVERGE with weights
`wᵢⱼ = µ̄ᵢⱼ(t₀) Qᵢ(t₀)` and then DAM.COMMIT. -/
noncomputable def damFEPolicy {N K : ℕ} (ε δ : ℝ) : Policy N K :=
  fun _ t0 _ q mh n e x η =>
    if e then .explore x (((t0 + Lepoch N K ε δ + 1 : ℕ) : ℝ) * (1 + η))
    else .converge fun j => muBar t0 (mh j) (n j) * q

/-- The confidence radius `∆ᵢⱼ(t₀) = √(3 ln t₀ / nᵢⱼ(t₀))`, arXiv:2206.03324v3, p. 18
(`∆ᵢⱼ = ∞` when `nᵢⱼ(t₀) = 0`, p. 51; that case is handled separately where `∆` is used). -/
noncomputable def confRadius (t0 n : ℕ) : ℝ := Real.sqrt (3 * Real.log t0 / n)

/-- **The event `ℰ_P`** of epoch `ℓ` (p. 18): at least one queue explores in this epoch. -/
def EventP {N K : ℕ} (ω : Omega N K) (ℓ : ℕ) : Prop := ∃ i, exploreCoin ω ℓ i = true

/-- **The event `ℰ_W`** of epoch `ℓ` with start `t₀` (p. 19): some service-rate estimate is
incorrect, i.e. there is a pair `(i, j)` with `µᵢⱼ > 0` such that either the estimate is out of
the confidence bound, `|µ̂ᵢⱼ(t₀) − µᵢⱼ| > ∆ᵢⱼ(t₀)`, or the confidence bound exceeds the
threshold, `∆ᵢⱼ(t₀) > (1/16) ε δ`.

**Formalization Note** When `nᵢⱼ(t₀) = 0`, `∆ᵢⱼ(t₀) = ∞` exceeds the threshold; this is the
disjunct `nᵢⱼ(t₀) = 0`. -/
def EventW {N K : ℕ} (s : System N K) (ε δ : ℝ) (rules : TieRules N K) (ω : Omega N K)
    (ℓ : ℕ) : Prop :=
  ∃ i j, 0 < s.mu i j ∧
    let d := epochData ε δ rules (damFEPolicy ε δ) ω ℓ
    let t0 := epochStart (Lepoch N K ε δ) ℓ
    (d.n i j = 0 ∨ confRadius t0 (d.n i j) < |d.muHat i j - s.mu i j| ∨
      ε * δ / 16 < confRadius t0 (d.n i j))

/-- The samples `Yᵢⱼ(τ + 1), …, Yᵢⱼ(t_e)` that DAM.UPDATE (Algorithm 5) collects for the pair
`(i, j)` in epoch `ℓ` of DAM.FE, in order (empty unless `i` explores `j` in epoch `ℓ` and has a
successful request in it). -/
noncomputable def epochSamples {N K : ℕ} (ε δ : ℝ) (rules : TieRules N K) (ω : Omega N K)
    (i : Fin N) (j : Fin K) (ℓ : ℕ) : List Bool :=
  let d := epochData ε δ rules (damFEPolicy ε δ) ω ℓ
  let t0 := epochStart (Lepoch N K ε δ) ℓ
  let te := t0 + Lepoch N K ε δ - 1
  let Y : ℕ → Prop := fun t => servedIn ε δ rules (damFEPolicy ε δ) ω ℓ d t i
  match modesOf ε δ (damFEPolicy ε δ) ω ℓ d i with
  | .explore j' _ =>
    if j' = j ∧ ∃ t ∈ Icc t0 te, Y t then
      let τ := sInf {t | t ∈ Icc t0 te ∧ Y t}
      (List.range (te - τ)).map fun k => decide (Y (τ + 1 + k))
    else []
  | .converge _ => []

/-- The samples `𝒴ᵢⱼ(t₀)` collected by Algorithm 5 for the pair `(i, j)` up to the start `t₀` of
epoch `ℓ` (from epochs `1, …, ℓ − 1`), in the order collected. -/
noncomputable def collectedSamples {N K : ℕ} (ε δ : ℝ) (rules : TieRules N K) (ω : Omega N K)
    (i : Fin N) (j : Fin K) (ℓ : ℕ) : List Bool :=
  (List.range (ℓ - 1)).flatMap fun m => epochSamples ε δ rules ω i j (m + 1)

/-- Queue `i`, if it explores server `j` in epoch `ℓ` of DAM.FE, outbids at `j` every queue that is
not exploring, in every slot of the epoch. This is the claim of arXiv:2206.03324v3, p. 17 ("the bid
from an exploring queue always dominate that from an exploiting queue") and p. 50 (proof of
Lemma 4.1) for the pair `(i, j)` and epoch `ℓ`.

**Formalization Note** The claim can fail. An exploiting queue's price can reach
`wᵢⱼ (1 + ε/16)` (Algorithm 2, lines 7–8), and so `Qᵢ(t₀)(1 + ε/16)`, not only `Qᵢ(t₀) ≤ t₀` as the
page says; this exceeds the explorer's bid `(t₀ + L_epoch + 1)(1 + ηᵢ)` once `t₀` is large against
`L_epoch/ε`. -/
def ExplorerOutbids {N K : ℕ} (ε δ : ℝ) (rules : TieRules N K) (ω : Omega N K) (i : Fin N)
    (j : Fin K) (ℓ : ℕ) : Prop :=
  let run := epochAuction ε δ rules (damFEPolicy ε δ) ω ℓ
  let t0 := epochStart (Lepoch N K ε δ) ℓ
  exploreCoin ω ℓ i = true → exploreServer ω ℓ i = j →
    ∀ t, t0 ≤ t → t ≤ t0 + Lepoch N K ε δ - 1 → ∀ i', exploreCoin ω ℓ i' = false →
      (stateAt run t0 t i').J = some j → (stateAt run t0 t i').bid < (stateAt run t0 t i).bid

end DecQueueLearning


