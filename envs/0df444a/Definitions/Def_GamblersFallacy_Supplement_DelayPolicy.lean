-- Prove2me | Definitions.Def_GamblersFallacy_Supplement_DelayPolicy
-- name    : GamblersFallacy_Supplement_DelayPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:13:27.954066+00:00
-- url     : https://prove2.me/theorems/1b2c97fe-a6ea-5e1f-ba4c-63fc116ccc01
-- title:
--   The delay ordering policy $\pi_{adp}$ — its cycle cost, long-run cost per cycle and finite-horizon cost per cycle
-- statement:
--   Each demand is a single unit, the replenishment lead time is zero, and $h$ and $b$ are the unit holding and shortage costs. Under the **delay ordering policy** $\pi_{adp}$ with delay $W\in\{0,1,2,\dots\}$, after a demand at time $t$ the inventory is kept at $0$ from $t+1$ to $t+W$ and raised to $1$ at $t+W+1$. A cycle whose next demand comes $z$ periods later costs
--   $$
--   C_W(z)=b\,\chi(z\le W)+h\,(z-W-1)\,\chi(z\ge W+2).
--   $$
--
--   The **long-run cost per cycle** is its expectation under the inter-arrival law:
--   $$
--   L(W)=b\sum_{j\le W}p_j+h\,p_{W+2}+2h\,p_{W+3}+\cdots .
--   $$
--
--   The **finite-horizon cost per cycle** over $n$ periods, starting right after a demand at time $0$, is
--   $$
--   F_n(W)=\mathbb E\Big[\frac{C_1+\dots+C_\tau+C_{\mathrm{tail}}}{\tau+1}\Big],\qquad \tau=\max\{t: Z_1+\dots+Z_t\le n-1\}.
--   $$
--   Here $C_t=C_W(Z_t)$, and $C_{\mathrm{tail}}$ is the cost from period $Z_1+\dots+Z_\tau+1$ to $n$. If the next demand arrives exactly at $n$, $C_{\mathrm{tail}}$ is the full cycle cost $C_W(Z_{\tau+1})$. Otherwise it is the holding cost $h\max\{0,\,n-(Z_1+\dots+Z_\tau)-W\}$ of the truncated last cycle, which has no shortage.
--
--   The proof of Proposition 3 (p.16) charges $C_{\mathrm{tail}}$ only when the next demand arrives exactly at $n$. With that reading the truncated holding cost is dropped, and $F_n(W)$ becomes Proposition 3's formula $b\sum_{j\le W}p_j(n)+h\sum_{j=W+2}^n(j-W-1)p_j(n)$. This variant is also defined (`finiteHorizonCostClosed`).
--
--   These are the objective functions whose minimizers $W^*(n)$ and $W^*$ Theorem 3 compares.
--
--   **Formalization Note** $F_n(W)$ is a finite weighted sum over the $2^n$ arrival patterns under the renewal law. The denominator $\tau+1$ is the number of arrivals at the positions $0,\dots,n-1$. Each arrival at a position $t\in\{1,\dots,n\}$ contributes the cycle cost of its gap, and the truncated holding cost is added when no demand arrives at $n$. The natural-number subtraction $n-s_\tau-W$ truncates at $0$, which is the $\max\{0,\cdot\}$.
-- source:
--   Bi–He–Teo, Taming the Long Tail, MSOM (2023), doi:10.1287/msom.2023.1217, §4, p.14 (unit costs h, b, zero lead time) and §4.1.1, p.15 (π_adp, cycle cost, long-run and finite-horizon expected cost per cycle); W*(n), W*, p.16

import Mathlib
import Definitions.Def_GamblersFallacy_biasedEstimate
import Definitions.Def_GamblersFallacy_Supplement_RenewalLaw

namespace GamblersFallacy.Supplement

open GamblersFallacy

/-- **The cycle cost of the delay ordering policy `π_adp`** (§4.1.1, p.15).
S. Bi, L. He, C.-P. Teo, *Taming the Long Tail: The Gambler's Fallacy in Intermittent Demand
Management*, MSOM (2023), doi:10.1287/msom.2023.1217, p.15: unit demand, zero lead time; after a
demand at `t` the inventory is kept at `0` from `t + 1` to `t + W` and raised to `1` at
`t + W + 1`; "C(π_adp) = b × χ(Z ≤ W) + h × χ(Z = W + 2) + 2h × χ(Z = W + 3) + ⋯".

`delayCycleCost b h W z` is the cost of a cycle whose next demand arrives `z` periods later: the
shortage cost `b` if `z ≤ W`, and otherwise the holding cost `h (z − W − 1)` (zero for
`z = W + 1`). -/
noncomputable def delayCycleCost (b h : ℝ) (W z : ℕ) : ℝ :=
  if z ≤ W then b else h * ((z - W - 1 : ℕ) : ℝ)

/-- **The long-run expected cost per cycle** (p.15):
`E[C(π_adp)] = b Σ_{j=1}^{W} p_j + h p_{W+2} + 2h p_{W+3} + ⋯`, the expectation of the cycle cost
under the inter-arrival law. -/
noncomputable def longRunCost (L : InterArrivalLaw) (b h : ℝ) (W : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 L.J, L.p j * delayCycleCost b h W j

/-- **The finite-horizon expected cost per cycle** (p.15):
`E[C(π_adp)] = E[(C₁ + C₂ + ⋯ + C_τ + C_tail)/(τ + 1)]`, `τ = max{t : Z₁ + ⋯ + Z_t ≤ n − 1}`,
"assume the initial state is immediately after a demand epoch", where `C_t` is the cycle cost of
the `t`-th cycle and `C_tail` "is the cost from the last arrival period Σ_{t=1}^τ Z_t + 1 to the
end of horizon period n".

On a path with arrivals at `0 = s₀ < s₁ < ⋯`, the `τ + 1` arrivals at the positions `0, …, n − 1`
form the denominator. Every arrival at a position `t ∈ {1, …, n}` closes a cycle of length
`t − prevArrival t` and contributes its cycle cost; this covers `C₁, …, C_τ` and, when a demand
arrives at `n`, `C_tail` (the full cycle closing at `n`). When no demand arrives at `n`, the last
cycle is truncated: the inventory is `0` for `W` periods after `s_τ` and `1` afterwards, so
`C_tail = h · max(0, n − s_τ − W)` holding cost and no shortage.

**Formalization Note.** The expectation is the finite weighted sum over the `2ⁿ` arrival patterns
under the renewal law; `n − s_τ − W` is natural-number subtraction, whose truncation at `0` is the
`max(0, ·)`. -/
noncomputable def finiteHorizonCost (L : InterArrivalLaw) (b h : ℝ) (n W : ℕ) : ℝ :=
  ∑ ω : Fin n → Bool, L.renewalWeight ω *
    (((∑ t ∈ (Finset.Icc 1 n).filter (fun t => arrival ω t = true),
          delayCycleCost b h W (t - prevArrival ω t)) +
        (if arrival ω n = true then 0 else h * ((n - lastArrival ω n - W : ℕ) : ℝ))) /
      (((Finset.range n).filter fun t => arrival ω t = true).card : ℝ))

/-- **The finite-horizon expected cost per cycle with `C_tail` charged only on a closed last
cycle** (p.15, as read in the proof of Proposition 3, p.16).
The proof of Proposition 3 takes `C_tail(π_adp) = b E[Σ_{j≤W} χ(Σ_{s≤τ} Z_s = n − j) χ(Z_{τ+1} = j)]
+ h Σ_{j=W+2}^n (j − W − 1) E[χ(Σ_{s≤τ} Z_s = n − j) χ(Z_{τ+1} = j)]`, i.e. the cycle cost of the
last cycle when the next demand falls at `n` and `0` when the last cycle is truncated. With this
reading the finite-horizon cost per cycle is Proposition 3's formula
`b Σ_{j≤W} p_j(n) + h Σ_{j=W+2}^n (j − W − 1) p_j(n)` (every counted cycle closes by `n`, so its
length is at most `n`).

**Formalization Note.** Same encoding as `finiteHorizonCost`, without the truncated holding term. -/
noncomputable def finiteHorizonCostClosed (L : InterArrivalLaw) (b h : ℝ) (n W : ℕ) : ℝ :=
  ∑ ω : Fin n → Bool, L.renewalWeight ω *
    ((∑ t ∈ (Finset.Icc 1 n).filter (fun t => arrival ω t = true),
          delayCycleCost b h W (t - prevArrival ω t)) /
      (((Finset.range n).filter fun t => arrival ω t = true).card : ℝ))

end GamblersFallacy.Supplement


