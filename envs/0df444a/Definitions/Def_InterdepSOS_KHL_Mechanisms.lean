-- Prove2me | Definitions.Def_InterdepSOS_KHL_Mechanisms
-- name    : InterdepSOS_KHL_Mechanisms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T10:58:32.14414+00:00
-- url     : https://prove2.me/theorems/8112a572-40cb-46ac-a66c-a2e75133bb52
-- title:
--   §6.1 — the Random Threshold, Random Sampling and k-HL mechanisms (p_RT = (k−1)/(k+3)) and their expected welfare
-- statement:
--   This file defines the three mechanisms of §6.1 (pp. 19–20) on top of the model of `InterdepSOS.KHL.Setting`.
--
--   **Random Threshold** with threshold $\ell\in\{1,\dots,k-1\}$. The high agents are $N_{\ge\ell}=\{i:s_i\ge\ell\}$ and the low agents $N_{<\ell}=[n]\setminus N_{\ge\ell}$. The proxy profile $(\mathbf s_{N_{<\ell}},\ell_{N_{\ge\ell}})$ sets every high agent's signal to $\ell$ and keeps the low agents' signals. The allocation $\bar T$ is a feasible allocation to the high agents maximizing
--   $$\sum_{i\in N_{\ge\ell}}\bar v_{iS_i},\qquad \bar v_{iT}=v_{iT}(\mathbf s_{N_{<\ell}},\ell_{N_{\ge\ell}}),$$
--   and agent $i$ receiving $\bar T_i$ pays $v_{i\bar T_i}(\mathbf s_{-i},s_i=\ell-1)$ (zero when $\bar T_i=\emptyset$).
--
--   **Random Sampling** with partition $(A,B)$, $A=[n]\setminus B$. The allocation $\tilde T$ is a feasible allocation to the agents of $B$ maximizing
--   $$\sum_{i\in B}\tilde v_{iS_i},\qquad \tilde v_{iT}=v_{iT}(\mathbf s_A,\mathbf 0_B),$$
--   and nobody pays.
--
--   In both cases the allocation is produced by a **selector**: a function of the threshold (resp. of $B$) and of the proxy profile, required to return a feasible maximizer of the proxy welfare at every grid profile. Ties may be broken arbitrarily, but only through the proxy data.
--
--   **k-HL** runs Random Threshold with probability $p_{RT}=\frac{k-1}{k+3}$, with $\ell$ uniform in $\{1,\dots,k-1\}$, and Random Sampling otherwise, with $B$ uniform among the subsets of $[n]$. Its expected welfare at the truthful profile $\mathbf s$, measured with the true values, is
--   $$p_{RT}\cdot\frac{1}{k-1}\sum_{\ell=1}^{k-1}\sum_i v_{i\bar T^{\ell}_i}(\mathbf s)\;+\;(1-p_{RT})\cdot\frac{1}{2^n}\sum_{B\subseteq[n]}\sum_i v_{i\tilde T^{B}_i}(\mathbf s).$$
--
--   **Formalization Note** The uniform average over $B$ is `InterdepSOS.RSV.avgB` of the shared file `InterdepSOS.RSV.Setting`, which this file imports. The selectors are `rtSel : ℕ → Signal n → Allocation n m` and `rsSel : Finset (Fin n) → Signal n → Allocation n m`; the mechanisms' allocations are `rtSel ℓ (rtProfile s ℓ)` and `rsSel B (keepOn Bᶜ s)`, so the allocation depends on the reports only through the proxy data (the proxy profile determines $N_{\ge\ell}$: its coordinates equal to $\ell$). `IsRTSelector` and `IsRSSelector` state the maximizer property at grid profiles. In the Random Sampling proxy agent $i$'s own signal is zeroed too ($i\in B$); the page's "$v_{ij}(\mathbf s_A,\mathbf 0_B)$" is read as $v_{iT}(\mathbf s_A,\mathbf 0_B)$. For $k\le1$ the threshold sum is empty and Lean's $1/0=0$ makes the Random Threshold average $0$.
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), pp. 19–20, §6.1, Mechanisms k-HL, Random Threshold and Random Sampling

import Mathlib
import Definitions.Def_InterdepSOS_RSV_Setting
import Definitions.Def_InterdepSOS_KHL_Setting

namespace InterdepSOS.KHL

/-- The "high" agents `N_{≥ℓ} = {i : s_i ≥ ℓ}`. -/
def high {n : ℕ} (s : Signal n) (ℓ : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ℓ ≤ s i)

/-- The proxy profile `(s_{N<ℓ}, ℓ_{N≥ℓ})` of Random Threshold: agents at or above `ℓ` are set
to `ℓ`, the others keep their signal. It determines `high s ℓ` (the coordinates equal to `ℓ`). -/
def rtProfile {n : ℕ} (s : Signal n) (ℓ : ℕ) : Signal n :=
  fun j => if ℓ ≤ s j then ℓ else s j

/-- Random Threshold with threshold `ℓ`: the selector `rtSel` is fed with `ℓ` and the proxy
profile, so the allocation depends on the reports only through the proxy data. -/
def rtAlloc {n m : ℕ} (rtSel : ℕ → Signal n → Allocation n m) (ℓ : ℕ) : AllocRule n m :=
  fun s => rtSel ℓ (rtProfile s ℓ)

/-- `rtSel` returns, for every grid profile and every threshold `ℓ ∈ {1, …, k-1}`, a feasible
allocation to the high agents maximizing their proxy welfare
`∑_{i ∈ N_{≥ℓ}} v̄_{i S_i}` with `v̄_{iT} = v_{iT}(s_{N<ℓ}, ℓ_{N≥ℓ})`. -/
def IsRTSelector {n m : ℕ} (k : ℕ) (v : Valuation n m)
    (rtSel : ℕ → Signal n → Allocation n m) : Prop :=
  ∀ ℓ ∈ Finset.Icc 1 (k - 1), ∀ s : Signal n, InGrid k s →
    IsAllocOn (high s ℓ) (rtAlloc rtSel ℓ s) ∧
    ∀ T : Allocation n m, IsAllocOn (high s ℓ) T →
      ∑ i ∈ high s ℓ, v i (T i) (rtProfile s ℓ) ≤
        ∑ i ∈ high s ℓ, v i (rtAlloc rtSel ℓ s i) (rtProfile s ℓ)

/-- Random Threshold payment: agent `i` receiving `T̄_i` pays `v_{i T̄_i}(s_{-i}, s_i = ℓ - 1)`
(which is `0` when `T̄_i = ∅`). -/
def rtPay {n m : ℕ} (v : Valuation n m) (rtSel : ℕ → Signal n → Allocation n m) (ℓ : ℕ) :
    Payment n :=
  fun s i => v i (rtAlloc rtSel ℓ s i) (Function.update s i (ℓ - 1))

/-- Random Sampling with partition `(A, B) = (Bᶜ, B)`: the selector sees only the proxy
profile `(s_A, 0_B)`. -/
def rsAlloc {n m : ℕ} (rsSel : Finset (Fin n) → Signal n → Allocation n m)
    (B : Finset (Fin n)) : AllocRule n m :=
  fun s => rsSel B (keepOn Bᶜ s)

/-- `rsSel` returns, for every grid profile and every `B`, a feasible allocation to the agents
of `B` maximizing `∑_{i ∈ B} ṽ_{i S_i}` with `ṽ_{iT} = v_{iT}(s_A, 0_B)`. -/
def IsRSSelector {n m : ℕ} (k : ℕ) (v : Valuation n m)
    (rsSel : Finset (Fin n) → Signal n → Allocation n m) : Prop :=
  ∀ (B : Finset (Fin n)) (s : Signal n), InGrid k s →
    IsAllocOn B (rsAlloc rsSel B s) ∧
    ∀ T : Allocation n m, IsAllocOn B T →
      ∑ i ∈ B, v i (T i) (keepOn Bᶜ s) ≤ ∑ i ∈ B, v i (rsAlloc rsSel B s i) (keepOn Bᶜ s)

/-- `p_RT = (k - 1)/(k + 3)`. -/
noncomputable def pRT (k : ℕ) : ℝ := ((k : ℝ) - 1) / ((k : ℝ) + 3)

/-- Expected welfare of Random Threshold at the truthful profile `s`, with `ℓ` uniform in
`{1, …, k-1}` (the sum is empty, and the average `0`, when `k ≤ 1`). -/
noncomputable def rtAvg {n m : ℕ} (k : ℕ) (v : Valuation n m)
    (rtSel : ℕ → Signal n → Allocation n m) (s : Signal n) : ℝ :=
  ((k - 1 : ℕ) : ℝ)⁻¹ * ∑ ℓ ∈ Finset.Icc 1 (k - 1), welfare v (rtAlloc rtSel ℓ s) s

/-- Expected welfare of Random Sampling at the truthful profile `s`, with `B` uniform among the
subsets of `[n]` (`InterdepSOS.RSV.avgB` is the uniform average `2^{-n} ∑_B`). -/
noncomputable def rsAvg {n m : ℕ} (v : Valuation n m)
    (rsSel : Finset (Fin n) → Signal n → Allocation n m) (s : Signal n) : ℝ :=
  InterdepSOS.RSV.avgB (fun B => welfare v (rsAlloc rsSel B s) s)

/-- Expected welfare of k-HL: Random Threshold with probability `p_RT`, Random Sampling with
probability `1 - p_RT`. -/
noncomputable def khlWelfare {n m : ℕ} (k : ℕ) (v : Valuation n m)
    (rtSel : ℕ → Signal n → Allocation n m)
    (rsSel : Finset (Fin n) → Signal n → Allocation n m) (s : Signal n) : ℝ :=
  pRT k * rtAvg k v rtSel s + (1 - pRT k) * rsAvg v rsSel s

end InterdepSOS.KHL


