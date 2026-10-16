-- Prove2me | Definitions.Def_InterdepSOS_KSS_Mechanisms
-- name    : InterdepSOS_KSS_Mechanisms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T12:36:46.580094+00:00
-- url     : https://prove2.me/theorems/16428494-a80b-4b46-a675-809a08a442b2
-- title:
--   §6.1–§6.2 — Random Sampling, Random Bucket and the mixture k-SS with p_RB = log₂k/(log₂k + 2)
-- statement:
--   Let $k=2^q$, so that $\log_2 k=q$, and let $v$ be a combinatorial valuation over the grid $\{0,\dots,k-1\}^n$.
--
--   **Random Bucket** with bucket index $\ell\in\{1,\dots,q\}$ uses the threshold $t=2^{\ell-1}$. The bucket-high agents are $N_{B_\ell}=\{i: s_i\ge 2^{\ell-1}\}$ and the others form $N_{\neg B_\ell}$. The proxy profile $(\mathbf s_{N_{\neg B_\ell}},\mathbf{2^{\ell-1}}_{N_{B_\ell}})$ sets every high signal to $2^{\ell-1}$ and keeps the low signals. The allocation $\bar T$ is a feasible allocation to $N_{B_\ell}$ maximizing
--   $$\sum_{i\in N_{B_\ell}} v_{iS_i}(\mathbf s_{N_{\neg B_\ell}},\mathbf{2^{\ell-1}}_{N_{B_\ell}})$$
--   over all feasible $S$ on $N_{B_\ell}$, and agent $i$ pays $v_{i\bar T_i}(\mathbf s_{-i},s_i=2^{\ell-1}-1)$ (zero if $\bar T_i=\emptyset$).
--
--   **Random Sampling** with partition $(A,B)$ allocates a feasible allocation to $B$ maximizing $\sum_{i\in B}v_{iS_i}(\mathbf s_A,\mathbf 0_B)$ and charges nothing. Random Sampling, its selector hypothesis, its expected welfare, the high set $\{i:s_i\ge t\}$ and the proxy profile at threshold $t$ are the shared definitions of `InterdepSOS.KHL.Mechanisms` (`rsAlloc`, `IsRSSelector`, `rsAvg`, `high`, `rtProfile`), used here at $t=2^{\ell-1}$.
--
--   **k-SS** runs Random Bucket with probability $p_{RB}=\frac{q}{q+2}$ (with $\ell$ uniform in $\{1,\dots,q\}$) and Random Sampling with probability $1-p_{RB}$ (with $B$ uniform among the $2^n$ subsets). Its expected welfare at the truthful profile $\mathbf s$ is
--   $$p_{RB}\cdot\frac1q\sum_{\ell=1}^{q}\sum_i v_{i\bar T^{\ell}_i}(\mathbf s)+(1-p_{RB})\cdot\frac1{2^n}\sum_{B\subseteq[n]}\sum_i v_{i\tilde T^{B}_i}(\mathbf s),$$
--   true values of the allocations chosen from the proxies.
--
--   These are the mechanisms of Lemma 6.4 and Theorem 6.5.
--
--   **Formalization Note** The argmax is modelled by a selector: a function of the bucket index (or of $B$) and of the **proxy profile** only, with a hypothesis (`IsRBSelector`, `IsRSSelector`) that on grid profiles it returns a feasible maximizer. Theorems quantify over every such selector. Making the allocation depend on the reports only through the proxy data is what "argmax of the proxy welfare" means, and incentive compatibility needs it: a selector reading the whole report could break ties differently after a misreport. The proxy profile at threshold $t\ge1$ determines the high set (its coordinates equal to $t$). The paper's Random Sampling writes $v_{ij}(\mathbf s_A,\mathbf 0_B)$, a misprint for $v_{iT}(\mathbf s_A,\mathbf 0_B)$; agent $i$'s own signal is zeroed too. $k=2^q$ is a disclosed reading: the buckets $[2^{\ell-1},2^\ell)$, $\ell=1,\dots,\log_2 k$, cover $\{1,\dots,k-1\}$ only when $k$ is a power of $2$. At $q=0$ Lean's $(0:\mathbb R)^{-1}=0$ makes the Random Bucket average $0$, matching $p_{RB}=0$.
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), p. 20, Mechanism Random Sampling; p. 22, Mechanism Random Bucket; p. 23, Mechanism k-SS

import Mathlib
import Definitions.Def_InterdepSOS_KSS_Setting
import Definitions.Def_InterdepSOS_KHL_Mechanisms

namespace InterdepSOS.KSS

/-- Random Bucket with index `ℓ`: the selector `rbSel` is fed with `ℓ` and the proxy profile
at threshold `2^{ℓ-1}`, so the allocation depends on the reports only through the proxy data. -/
def rbAlloc {n m : ℕ} (rbSel : ℕ → InterdepSOS.KHL.Signal n → InterdepSOS.KHL.Allocation n m) (ℓ : ℕ) : InterdepSOS.KHL.AllocRule n m :=
  fun s => rbSel ℓ (InterdepSOS.KHL.rtProfile s (2 ^ (ℓ - 1)))

/-- `rbSel` returns, for every grid profile and every bucket `ℓ ∈ {1, …, q}`, a feasible
allocation to the bucket-high agents maximizing their proxy InterdepSOS.KHL.welfare
`∑_{i ∈ N_{B_ℓ}} v_{i S_i}(s_{N_{¬B_ℓ}}, 2^{ℓ-1}_{N_{B_ℓ}})`. -/
def IsRBSelector {n m : ℕ} (q : ℕ) (v : InterdepSOS.KHL.Valuation n m)
    (rbSel : ℕ → InterdepSOS.KHL.Signal n → InterdepSOS.KHL.Allocation n m) : Prop :=
  ∀ ℓ ∈ Finset.Icc 1 q, ∀ s : InterdepSOS.KHL.Signal n, InterdepSOS.KHL.InGrid (2 ^ q) s →
    InterdepSOS.KHL.IsAllocOn (InterdepSOS.KHL.high s (2 ^ (ℓ - 1))) (rbAlloc rbSel ℓ s) ∧
    ∀ T : InterdepSOS.KHL.Allocation n m, InterdepSOS.KHL.IsAllocOn (InterdepSOS.KHL.high s (2 ^ (ℓ - 1))) T →
      ∑ i ∈ InterdepSOS.KHL.high s (2 ^ (ℓ - 1)), v i (T i) (InterdepSOS.KHL.rtProfile s (2 ^ (ℓ - 1))) ≤
        ∑ i ∈ InterdepSOS.KHL.high s (2 ^ (ℓ - 1)), v i (rbAlloc rbSel ℓ s i) (InterdepSOS.KHL.rtProfile s (2 ^ (ℓ - 1)))

/-- Random Bucket payment: agent `i` receiving `T̄_i` pays `v_{i T̄_i}(s_{-i}, s_i = 2^{ℓ-1} - 1)`
(which is `0` when `T̄_i = ∅`). -/
def rbPay {n m : ℕ} (v : InterdepSOS.KHL.Valuation n m) (rbSel : ℕ → InterdepSOS.KHL.Signal n → InterdepSOS.KHL.Allocation n m) (ℓ : ℕ) :
    InterdepSOS.KHL.Payment n :=
  fun s i => v i (rbAlloc rbSel ℓ s i) (Function.update s i (2 ^ (ℓ - 1) - 1))

/-- `p_RB = log₂ k / (log₂ k + 2)` with `k = 2^q`. -/
noncomputable def pRB (q : ℕ) : ℝ := (q : ℝ) / ((q : ℝ) + 2)

/-- Expected InterdepSOS.KHL.welfare of Random Bucket at the truthful profile `s`, `ℓ` uniform in `{1,…,q}`. -/
noncomputable def rbAvg {n m : ℕ} (q : ℕ) (v : InterdepSOS.KHL.Valuation n m)
    (rbSel : ℕ → InterdepSOS.KHL.Signal n → InterdepSOS.KHL.Allocation n m) (s : InterdepSOS.KHL.Signal n) : ℝ :=
  (q : ℝ)⁻¹ * ∑ ℓ ∈ Finset.Icc 1 q, InterdepSOS.KHL.welfare v (rbAlloc rbSel ℓ s) s

/-- Expected InterdepSOS.KHL.welfare of k-SS: Random Bucket with probability `p_RB`, Random Sampling with
probability `1 - p_RB`. -/
noncomputable def kssWelfare {n m : ℕ} (q : ℕ) (v : InterdepSOS.KHL.Valuation n m)
    (rbSel : ℕ → InterdepSOS.KHL.Signal n → InterdepSOS.KHL.Allocation n m)
    (rsSel : Finset (Fin n) → InterdepSOS.KHL.Signal n → InterdepSOS.KHL.Allocation n m) (s : InterdepSOS.KHL.Signal n) : ℝ :=
  pRB q * rbAvg q v rbSel s + (1 - pRB q) * InterdepSOS.KHL.rsAvg v rsSel s

end InterdepSOS.KSS


