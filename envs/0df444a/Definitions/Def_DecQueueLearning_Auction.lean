-- Prove2me | Definitions.Def_DecQueueLearning_Auction
-- name    : DecQueueLearning_Auction
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:40:03.780551+00:00
-- url     : https://prove2.me/theorems/7b1c5e23-e7b1-47c3-acec-09cc8cd73c11
-- title:
--   The decentralized auction of one epoch (DAM.CONVERGE, DAM.COMMIT, exploration requests) and the good checking event
-- statement:
--   This module defines what happens inside one epoch starting at slot $t_0$. Each queue $i$ has a **mode**: either it explores a fixed server $j$ with a fixed bid $b$, or it runs DAM.CONVERGE (Algorithm 2) with weights $w_{i,j}$ followed by DAM.COMMIT (Algorithm 3). Queue $i$ keeps prices $p_{i,j}(t)$, a request $J(i,t)\in\mathcal K\cup\{\bot\}$ with its bid, and an event log $\tau_i(t)$, initialised by $p_{i,j}(t_0-1)=0$ and $\tau_i(t_0-1)=t_0-1$. In slot $t$ a converging queue
--
--   1. in the commit phase ($t\ge t_0+L_{\mathrm{conv}}$) repeats its request and bid of slot $t_0+L_{\mathrm{conv}}-1$;
--   2. within its checking period ($t>t_0$ and $t-\tau_i(t-1)\le L_{\mathrm{check}}$) repeats its request and keeps its prices;
--   3. otherwise picks $j^\star\in\arg\max_j w_{i,j}-p_{i,j}(t-1)$; if $w_{i,j^\star}-p_{i,j^\star}(t-1)>0$ it raises $p_{i,j^\star}$ by $\tfrac1{16}\varepsilon(1-\eta_i)w_{i,j^\star}$ and requests $j^\star$ with that price, and otherwise it stops requesting.
--
--   Each server $j$ selects among its requesters $R_j(t)=\{i:J(i,t)=j\}$ one with the highest bid, $I(j,t)$; the request of $I(j,t)$ succeeds if the service coin of the pair $(I(j,t),j)$ at slot $t$ succeeds. Then $\tau_i(t)=t$ if queue $i$ updated a price or was served, and $\tau_i(t)=\tau_i(t-1)$ otherwise. The **epoch auction** `epochRun` is the case in which every queue converges with weights $w$; the committed server is $\sigma(i)=J(i,t_0+L_{\mathrm{conv}}-1)$.
--
--   The **good checking event** of the epoch is
--   $$
--   \mathcal E_\ell=\big\{\forall t\in[t_0+L_{\mathrm{check}}-1,\,t_0+L_{\mathrm{conv}}-1],\ j\in\mathcal K,\ \exists t'\in[t-L_{\mathrm{check}}+1,t]:\ S_{I(j,t'),j}(t')=1\big\},
--   $$
--   where a slot with $I(j,t')=\bot$ counts as a success ($\mu_{\bot,j}=1$). The system **converges** in slot $t$ if $|R_j(t)|\le1$ for every server $j$. The module also defines the absence of bid ties at a server during the epoch.
--
--   **Formalization Note** DAM.COMMIT is read as requesting in every slot of $[t_s,t_e]$, inclusive of $t_e$. Each slot records whether lines 6–10 of Algorithm 2 ran (`reselect`) and whether line 8 ran (`priceInc`).
-- source:
--   Freund, Lykouris, Weng, Efficient decentralized multi-agent learning in asymmetric bipartite queueing systems, arXiv:2206.03324v3, Algorithms 2–4, pp. 11–12, 17; ℰ_ℓ p. 12; convergence p. 13

import Mathlib
import Definitions.Def_DecQueueLearning_Constants
import Definitions.Def_DecQueueLearning_TieRules

open Finset Classical

namespace DecQueueLearning

/-- What a queue does during one epoch, arXiv:2206.03324v3, Algorithms 1–4, pp. 10–17:
`explore j b` requests server `j` with bid `b` in every slot of the epoch (Algorithm 4, line 9);
`converge w` runs DAM.CONVERGE (Algorithm 2) with weights `w j = wᵢⱼ` and then DAM.COMMIT
(Algorithm 3). -/
inductive Mode (K : ℕ) where
  | explore (j : Fin K) (b : ℝ)
  | converge (w : Fin K → ℝ)

/-- The state of one queue in the auction after a time slot `t` of an epoch: its prices `pᵢⱼ(t)`,
its request `J(i, t)` (`none` is the paper's `⊥`), the bid sent with it, the event log `τᵢ(t)`,
and two flags recording which branch of Algorithm 2 ran in slot `t`: `reselect` (lines 6–10 ran,
i.e. the queue left its checking period and re-selected) and `priceInc` (line 8 ran, a price
update). -/
structure AState (K : ℕ) where
  p : Fin K → ℝ
  J : Option (Fin K)
  bid : ℝ
  tau : ℕ
  reselect : Bool
  priceInc : Bool

/-- The state before the first slot `t₀` of an epoch: `pᵢⱼ(t₀ − 1) = 0` and `τᵢ(t₀ − 1) = t₀ − 1`
(Algorithm 2, line 1). -/
def AState.init {K : ℕ} (t0 : ℕ) : AState K :=
  ⟨0, none, 0, t0 - 1, false, false⟩

/-- The request decision of queue `i` in time slot `t` of the epoch starting at `t₀`, from its
state after slot `t − 1`, arXiv:2206.03324v3, Algorithm 2 (lines 3–11), Algorithm 3 and
Algorithm 4 (line 9). The event log `τ` is updated afterwards, in `auctionStep`.

* exploring queue: request `j` with bid `b`;
* commit phase (`t ≥ t₀ + L_conv`): keep the request and bid of slot `t₀ + L_conv − 1`;
* within the checking period (`t > t₀` and `t − τᵢ(t − 1) ≤ L_check`): keep request and prices;
* otherwise `j⋆ ∈ arg maxⱼ (wᵢⱼ − pᵢⱼ(t − 1))`; if `wᵢⱼ⋆ − pᵢⱼ⋆(t − 1) > 0`, raise
  `pᵢⱼ⋆ ← pᵢⱼ⋆ + (1/16) ε (1 − ηᵢ) wᵢⱼ⋆` and request `j⋆` with that price; else request nothing
  (`J(i, t) = ⊥`, bid `0`), prices unchanged.

**Formalization Note** DAM.COMMIT (Algorithm 3) is read as requesting in every slot of
`[t_s, t_e]`, inclusive of `t_e`. -/
noncomputable def decideRequest {N K : ℕ} (ε δ : ℝ) (rules : TieRules N K) (i : Fin N) (m : Mode K)
    (η : ℝ) (t0 t : ℕ) (a : AState K) : AState K :=
  match m with
  | .explore j b => { a with J := some j, bid := b, reselect := false, priceInc := false }
  | .converge w =>
    if Lconv N K ε δ ≤ t - t0 ∨ (t0 < t ∧ t - a.tau ≤ Lcheck N K ε δ) then
      { a with reselect := false, priceInc := false }
    else
      let js := rules.argmax i t (fun j => w j - a.p j)
      if 0 < w js - a.p js then
        { a with p := Function.update a.p js (a.p js + ε / 16 * (1 - η) * w js), J := some js,
                 bid := a.p js + ε / 16 * (1 - η) * w js, reselect := true, priceInc := true }
      else
        { a with J := none, bid := 0, reselect := true, priceInc := false }

/-- The set `R(j, t) = {i : J(i, t) = j}` of queues requesting server `j`, for the request
profile `D`. -/
noncomputable def requesters {N K : ℕ} (D : Fin N → AState K) (j : Fin K) : Finset (Fin N) :=
  univ.filter fun i => (D i).J = some j

/-- The queue `I(j, t)` selected by server `j` in slot `t` for the request profile `D`: a
requester with the highest bid (`none` = `⊥` iff nobody requests `j`). -/
noncomputable def selected {N K : ℕ} (rules : TieRules N K) (t : ℕ) (D : Fin N → AState K)
    (j : Fin K) : Option (Fin N) :=
  rules.serve t j (requesters D j) fun i => (D i).bid

/-- Queue `i`'s request is successful in slot `t` (`Sᵢ(t) = 1`), for the request profile `D` and
the service coins `S t i j` (`= true` with probability `µᵢⱼ`): it requests some server `j`, `j`
selects it, and the coin of the pair `(i, j)` at `t` succeeds. -/
def Served {N K : ℕ} (rules : TieRules N K) (S : ℕ → Fin N → Fin K → Bool) (t : ℕ)
    (D : Fin N → AState K) (i : Fin N) : Prop :=
  ∃ j, (D i).J = some j ∧ selected rules t D j = some i ∧ S t i j = true

/-- One time slot `t` of the auction: every queue decides (`decideRequest`), the servers select, and the
event log is updated, `τᵢ(t) = t` if a price was updated or the request was successful and
`τᵢ(t) = τᵢ(t − 1)` otherwise (Algorithm 2, lines 12–14). -/
noncomputable def auctionStep {N K : ℕ} (ε δ : ℝ) (rules : TieRules N K) (modes : Fin N → Mode K)
    (η : Fin N → ℝ) (S : ℕ → Fin N → Fin K → Bool) (t0 t : ℕ) (a : Fin N → AState K) :
    Fin N → AState K :=
  let D := fun i => decideRequest ε δ rules i (modes i) (η i) t0 t (a i)
  fun i => { D i with tau := if (D i).priceInc = true ∨ Served rules S t D i then t else (D i).tau }

/-- **The auction of one epoch** (Algorithms 2–4) starting at slot `t₀`, with per-queue modes,
perturbations `ηᵢ`, and service coins `S`: `auctionRun … k` is the state of all queues after the
`k` slots `t₀, …, t₀ + k − 1` (`k = 0`: before `t₀`). -/
noncomputable def auctionRun {N K : ℕ} (ε δ : ℝ) (rules : TieRules N K) (modes : Fin N → Mode K)
    (η : Fin N → ℝ) (S : ℕ → Fin N → Fin K → Bool) (t0 : ℕ) : ℕ → Fin N → AState K
  | 0 => fun _ => AState.init t0
  | k + 1 => auctionStep ε δ rules modes η S t0 (t0 + k) (auctionRun ε δ rules modes η S t0 k)

/-- The state of all queues after slot `t ≥ t₀` of a run started at `t₀`; in particular
`(stateAt run t₀ t i).J = J(i, t)` and `.bid` is the bid sent with it. -/
def stateAt {N K : ℕ} (run : ℕ → Fin N → AState K) (t0 t : ℕ) : Fin N → AState K :=
  run (t + 1 - t0)

/-- **The epoch auction of Section 3.3** (`epochRun`), arXiv:2206.03324v3, p. 13: all queues run
DAM.CONVERGE with general weights `wᵢⱼ` in the epoch starting at `t₀` and then DAM.COMMIT. -/
noncomputable def epochRun {N K : ℕ} (ε δ : ℝ) (rules : TieRules N K) (w : Fin N → Fin K → ℝ)
    (η : Fin N → ℝ) (S : ℕ → Fin N → Fin K → Bool) (t0 : ℕ) : ℕ → Fin N → AState K :=
  auctionRun ε δ rules (fun i => .converge (w i)) η S t0

/-- `R(j, t)` in a run started at `t₀`. -/
noncomputable def R {N K : ℕ} (run : ℕ → Fin N → AState K) (t0 : ℕ) (j : Fin K) (t : ℕ) :
    Finset (Fin N) :=
  requesters (stateAt run t0 t) j

/-- **The good checking event** `ℰ_ℓ` of the epoch with slots `[t₀, t₀ + L_epoch − 1]`,
arXiv:2206.03324v3, p. 12:
`ℰ_ℓ = {∀ t ∈ [t₀ + L_check − 1, t₀ + L_conv − 1], j ∈ 𝒦, ∃ t′ ∈ [t − L_check + 1, t],
S_{I(j,t′),j}(t′) = 1}`.

**Formalization Note** With `µ_{⊥,j} = 1` (p. 6), a server that receives no request in slot `t′`
(`I(j, t′) = ⊥`) counts as a success. -/
def GoodChecking {N K : ℕ} (ε δ : ℝ) (rules : TieRules N K) (run : ℕ → Fin N → AState K)
    (S : ℕ → Fin N → Fin K → Bool) (t0 : ℕ) : Prop :=
  ∀ t, t0 + Lcheck N K ε δ - 1 ≤ t → t ≤ t0 + Lconv N K ε δ - 1 → ∀ j : Fin K,
    ∃ t', t + 1 - Lcheck N K ε δ ≤ t' ∧ t' ≤ t ∧
      ∀ i, selected rules t' (stateAt run t0 t') j = some i → S t' i j = true

/-- No two queues send equal bids to the same server in any slot of the epoch
(arXiv:2206.03324v3, p. 7, footnote 2: "our algorithms will ensure that, almost surely, ties do not
exist"). -/
def NoBidTies {N K : ℕ} (ε δ : ℝ) (run : ℕ → Fin N → AState K) (t0 : ℕ) : Prop :=
  ∀ t, t0 ≤ t → t ≤ t0 + Lepoch N K ε δ - 1 → ∀ i i' : Fin N, ∀ j : Fin K, i ≠ i' →
    (stateAt run t0 t i).J = some j → (stateAt run t0 t i').J = some j →
      (stateAt run t0 t i).bid ≠ (stateAt run t0 t i').bid

/-- The queues and servers **converge** in slot `t` (arXiv:2206.03324v3, p. 13): every server
receives at most one request, `|R_j(t)| ≤ 1`. -/
def ConvergesAt {N K : ℕ} (run : ℕ → Fin N → AState K) (t0 t : ℕ) : Prop :=
  ∀ j : Fin K, (R run t0 j t).card ≤ 1

/-- The committed server `σ(i) = J(i, t₀ + L_conv − 1)` returned by DAM.CONVERGE
(Algorithm 2, line 15). -/
noncomputable def committed {N K : ℕ} (ε δ : ℝ) (run : ℕ → Fin N → AState K) (t0 : ℕ) :
    Fin N → Option (Fin K) :=
  fun i => (stateAt run t0 (t0 + Lconv N K ε δ - 1) i).J

end DecQueueLearning


