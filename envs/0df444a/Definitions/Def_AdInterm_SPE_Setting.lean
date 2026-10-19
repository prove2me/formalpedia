-- Prove2me | Definitions.Def_AdInterm_SPE_Setting
-- name    : AdInterm_SPE_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:29.118308+00:00
-- url     : https://prove2.me/theorems/7abea168-74e9-4e20-bcbb-fc8320b2baf6
-- title:
--   §2, §3.3, Defs. A.1–A.3, pp. 9–19, 35, 41–44 — k-tree, mechanisms M, reports, allocation, minimum-winning-report payments, profits (3), anticipated reports W_t, SPE
-- statement:
--   This module sets up the multi-stage intermediation game of Balseiro, Candogan and Gurkan on a **symmetric tree**, built on the virtual-value module.
--
--   1. **Network.** Tiers are $t=n+1,\dots,0$: the seller is the root (tier $n+1$), intermediaries occupy tiers $n,\dots,1$, buyers are the leaves (tier $0$). Every tier-$t$ node has $k_t$ downstream agents, so tier $t$ has $\prod_{s=t+1}^{n+1}k_s$ nodes; the children of node $(t+1,j)$ are $(t,\,j k_{t+1}+c)$ for $c<k_{t+1}$.
--   2. **Mechanisms.** A mechanism $(r,Y)\in\mathcal M$ is a reserve $r\ge0$ and a nondecreasing reporting function $Y:\mathbb R_+\to\mathbb R_+$. A profile assigns a mechanism to every intermediary.
--   3. **Reports.** Buyers report their values. An intermediary whose highest downstream report $w$ satisfies $w\ge r$ reports $Y(w)$ upstream; otherwise it sends no report.
--   4. **Allocation.** The seller allocates to the highest report among its children if that report is at least its reserve $r_S\ge0$; a winning intermediary allocates to its highest-reporting child. Ties go to the child with the lowest index.
--   5. **Payments** (Definition A.1). A winning agent pays the **minimum winning report**, $\inf\Theta$, where $\Theta$ is the set of reports $b\ge0$ with which it would still win, all other agents' reports fixed and all its ancestors' reports recomputed.
--   6. **Profits** (display (3), Definition A.2). Intermediary $I_\ell$ earns $\sum_{c}\mathbb E[(P_c-P_\ell)\,\mathbf 1\{I_c\text{ wins}\}]$ over its children $c$; the seller earns the payment of its winning child. Buyer values are i.i.d. with law $\mu$.
--   7. **Anticipated reports** (Definition 3.3). $W_0=V$ and $W_t=\psi_{W_{t-1}}\big(W_{t-1}^{\mathrm{FH}(k_t)}\big)$, where $W_{t-1}^{\mathrm{FH}(k_t)}$ is the maximum of $k_t$ i.i.d. copies of $W_{t-1}$. The equilibrium mechanism of tier $t$ is $(z_{W_{t-1}},\psi_{W_{t-1}})$.
--   8. **Subgame perfect equilibrium** (Definition A.3). For a history-independent profile in which tier $t$ uses $\sigma_t$ and the seller uses $r^*$: after every tier-$t$ history (arbitrary mechanisms in $\mathcal M$ for tiers $t+1,\dots,n$ and any seller reserve $r_S\ge0$), no node of tier $t$ gains by switching to any mechanism in $\mathcal M$, the others keeping theirs; and the seller gains nothing from any reserve $r_S\ge0$ instead of $r^*\ge0$.
--   9. **One-stage model** (Figure 3, (5)–(6), p. 35). One intermediary with $m$ buyers faces a seller's reserve $r_S$ and an independent competing bid $D$; with mechanism $(r,Y)$ it wins iff $w\ge r$ and $Y(w)\ge\max(r_S,D)$, pays $\max(r_S,D)$ and charges $\max\big(r,Y^{-1}(\max(r_S,D)),V^{\mathrm{SH}(m)}\big)$.
--
--   The module is the shared language of Theorem 3.1 and its milestones.
--
--   **Formalization Note** Disclosed readings: (i) the page's "otherwise she reports zero" is no report, which is never allocated; (ii) ties go to the lowest index, and a report equal to a reserve wins; (iii) payments are Definition A.1's minimum winning report, not the closed forms (1)–(2), which with a deterministic tie rule can undercharge after a flat or jumping upstream reporting function; (iv) buyers report truthfully (Lemma 2.1(B)); (v) the seller's reserve ranges over $\mathbb R_+$ (p. 12); (vi) a history fixes one mechanism per upstream tier, as in Definition A.2's $\mathcal H_t$; (vii) expectations are single Bochner integrals of the realized profit, so a deviation whose profit is not integrable has value $0$, which never exceeds the equilibrium profit (nonnegative pointwise). A history-independent profile loses nothing in Definition A.3: after a history $H_t$, a strategy affects its owner's payoff only through the mechanism it selects at $H_t$, and the lower tiers do not react.
-- source:
--   Balseiro, Candogan & Gurkan, Multi-stage Intermediation in Display Advertising, SSRN 2661459 (manuscript of 2019-08-17; M&SOM doi:10.1287/msom.2019.0854), §2 pp. 9–14, display (3), §3.3 Definition 3.3 p. 19, Theorem 3.1 p. 20, proof of Lemma 3.1 (5)–(6) p. 35, e-companion A Definitions A.1–A.3 pp. 41–44

import Mathlib
import Definitions.Def_AdInterm_SPE_VirtualValue

open MeasureTheory Filter

namespace AdInterm.SPE

/-! The symmetric `k`-tree of Balseiro–Candogan–Gurkan (§2, pp. 9–14; e-companion A,
pp. 41–44): mechanisms, reports, allocation, payments, profits, anticipated reports and SPE. -/

/-- A mechanism `(r, Y)` of an intermediary: a reserve price and a reporting function. -/
abbrev Mechanism := ℝ × (ℝ → ℝ)

/-- §2, p. 12: `(r, Y) ∈ M` — a nonnegative reserve and a nondecreasing `Y : ℝ₊ → ℝ₊`. -/
def IsMech (m : Mechanism) : Prop :=
  0 ≤ m.1 ∧ MonotoneOn m.2 (Set.Ici 0) ∧ ∀ x, 0 ≤ x → 0 ≤ m.2 x

/-- Definition 3.3, p. 19: the law of the anticipated report, `W_0 = V` and
`W_t = ψ_{W_{t−1}}(max_{j ≤ k_t} W_{t−1,j})` for `k_t` i.i.d. copies of `W_{t−1}`. -/
noncomputable def annLaw (k : ℕ → ℕ) (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => μ
  | t + 1 =>
      (Measure.pi (fun _ : Fin (k (t + 1)) => annLaw k μ t)).map
        (fun x => psi (annLaw k μ t) (maxFin (k (t + 1)) x))

/-- Number of agents in tier `t` of the `k`-tree with tiers `n+1` (seller) … `0` (buyers):
`∏_{s = t+1}^{n+1} k_s`. The children of node `(t+1, j)` are `(t, j·k_{t+1} + c)`, `c < k_{t+1}`. -/
def nodes (k : ℕ → ℕ) (n t : ℕ) : ℕ :=
  ∏ s ∈ Finset.Icc (t + 1) (n + 1), k s

/-- The mechanism used by node `(t, j)`, for tiers `t = 1, …, n`. -/
abbrev Profile := ℕ → ℕ → Mechanism
/-- An optional replacement `(t, j, b)`: node `(t, j)` reports `b` instead of its own report. -/
abbrev BidOverride := Option (ℕ × ℕ × ℝ)

/-- Reports, bottom-up (§2, p. 12). Buyers report their values. An intermediary whose largest
downstream report `w` is at least its reserve `r` reports `Y(w)`; otherwise it sends no report (`⊥`,
the page's "reports zero"). An override replaces one node's report. -/
noncomputable def bidCore (k : ℕ → ℕ) (σ : Profile) (v : ℕ → ℝ)
    (override : BidOverride) : ℕ → ℕ → WithBot ℝ
  | 0, j =>
      match override with
        | some (0, i, b) => if i = j then (b : WithBot ℝ) else (v j : WithBot ℝ)
        | _ => (v j : WithBot ℝ)
  | t + 1, j =>
      match override with
      | some (s, i, b) =>
          if s = t + 1 ∧ i = j then (b : WithBot ℝ)
          else
            let w := (Finset.range (k (t + 1))).sup
              (fun c => bidCore k σ v override t (j * k (t + 1) + c))
            if (σ (t + 1) j).1 ≤ w then
              ((σ (t + 1) j).2 (w.getD 0) : WithBot ℝ) else ⊥
      | none =>
          let w := (Finset.range (k (t + 1))).sup
            (fun c => bidCore k σ v override t (j * k (t + 1) + c))
          if (σ (t + 1) j).1 ≤ w then
            ((σ (t + 1) j).2 (w.getD 0) : WithBot ℝ) else ⊥

/-- The report of node `(t, j)` under profile `σ` and buyer values `v`. -/
noncomputable def bid (k : ℕ → ℕ) (σ : Profile) (v : ℕ → ℝ)
    (t j : ℕ) : WithBot ℝ := bidCore k σ v none t j

/-- Child `c` of tier-`(t+1)` node `p` is allocated the impression by `p`: it reports, its report
is maximal among the siblings, strictly above every lower-indexed sibling (ties go to the lowest
index) and, if `p` is the seller, at least the seller's reserve `rS`. -/
def IsBestChild (k : ℕ → ℕ) (n : ℕ) (σ : Profile) (rS : ℝ)
    (v : ℕ → ℝ) (override : BidOverride) (t p c : ℕ) : Prop :=
  c < k (t + 1) ∧
  bidCore k σ v override t (p * k (t + 1) + c) ≠ ⊥ ∧
  (t = n → (rS : WithBot ℝ) ≤ bidCore k σ v override t (p * k (t + 1) + c)) ∧
  ∀ d < k (t + 1),
    if d < c then
      bidCore k σ v override t (p * k (t + 1) + d) <
        bidCore k σ v override t (p * k (t + 1) + c)
    else
      bidCore k σ v override t (p * k (t + 1) + d) ≤
        bidCore k σ v override t (p * k (t + 1) + c)

/-- The child to which tier-`(t+1)` node `p` allocates, if any. -/
noncomputable def chooseChild (k : ℕ → ℕ) (n : ℕ) (σ : Profile) (rS : ℝ)
    (v : ℕ → ℝ) (override : BidOverride) (t p : ℕ) : Option ℕ := by
  classical
  exact if h : ∃ c, IsBestChild k n σ rS v override t p c then
    some (p * k (t + 1) + Classical.choose h) else none

/-- The node allocated the impression at depth `d` below the seller, following the allocation
top-down. -/
noncomputable def winnerDepth (k : ℕ → ℕ) (n : ℕ) (σ : Profile) (rS : ℝ)
    (v : ℕ → ℝ) (override : BidOverride) : ℕ → Option ℕ
  | 0 => some 0
  | d + 1 =>
      (winnerDepth k n σ rS v override d).bind
        (chooseChild k n σ rS v override (n - d))

/-- The tier-`t` node that wins the impression, if any. -/
noncomputable def winnerAt (k : ℕ → ℕ) (n : ℕ) (σ : Profile) (rS : ℝ)
    (v : ℕ → ℝ) (override : BidOverride) (t : ℕ) : Option ℕ :=
  winnerDepth k n σ rS v override (n + 1 - t)

/-- Node `(t, j)` wins the impression. -/
def wins (k : ℕ → ℕ) (n : ℕ) (σ : Profile) (rS : ℝ)
    (v : ℕ → ℝ) (t j : ℕ) : Prop :=
  winnerAt k n σ rS v none t = some j

/-- Node `(t, j)` wins when its report is replaced by `b` (all ancestors' reports recomputed,
all other reports unchanged). -/
def winsWith (k : ℕ → ℕ) (n : ℕ) (σ : Profile) (rS : ℝ)
    (v : ℕ → ℝ) (t j : ℕ) (b : ℝ) : Prop :=
  winnerAt k n σ rS v (some (t, j, b)) t = some j

/-- Definition A.1, p. 41: the payment of node `(t, j)` is the minimum winning report
`inf Θ = inf {b ≥ 0 | (t, j) wins with report b}`. Read only on the event that `(t, j)` wins. -/
noncomputable def pay (k : ℕ → ℕ) (n : ℕ) (σ : Profile) (rS : ℝ)
    (v : ℕ → ℝ) (t j : ℕ) : ℝ :=
  sInf {b : ℝ | 0 ≤ b ∧ winsWith k n σ rS v t j b}

/-- Buyer values indexed by `ℕ` (zero beyond the last buyer). -/
def buyerValues (k : ℕ → ℕ) (n : ℕ)
    (v : Fin (nodes k n 0) → ℝ) : ℕ → ℝ :=
  fun i => if h : i < nodes k n 0 then v ⟨i, h⟩ else 0

/-- Definition A.2: the realized profit of intermediary `(t, j)`,
`Σ_c (P_c − P_{(t,j)}) 1{c wins}` over its children `c`. -/
noncomputable def interProfit (k : ℕ → ℕ) (n : ℕ) (σ : Profile) (rS : ℝ)
    (v : ℕ → ℝ) (t j : ℕ) : ℝ :=
  ∑ c ∈ Finset.range (k t), by
    classical
    exact
    if wins k n σ rS v (t - 1) (j * k t + c) then
      pay k n σ rS v (t - 1) (j * k t + c) - pay k n σ rS v t j
    else 0

/-- Definition A.2: the seller's realized revenue, the payment of the winning tier-`n` node. -/
noncomputable def sellerRev (k : ℕ → ℕ) (n : ℕ) (σ : Profile) (rS : ℝ)
    (v : ℕ → ℝ) : ℝ :=
  ∑ c ∈ Finset.range (k (n + 1)), by
    classical
    exact
    if wins k n σ rS v n c then pay k n σ rS v n c else 0

/-- Definition A.2 / (3): the expected profit of intermediary `(t, j)`, one Bochner integral
over i.i.d. buyer values. -/
noncomputable def Pi_int (k : ℕ → ℕ) (n : ℕ) (μ : Measure ℝ)
    (σ : Profile) (rS : ℝ) (t j : ℕ) : ℝ :=
  ∫ v, interProfit k n σ rS (buyerValues k n v) t j ∂
    (Measure.pi (fun _ : Fin (nodes k n 0) => μ))

/-- Definition A.2: the seller's expected revenue. -/
noncomputable def Pi_S (k : ℕ → ℕ) (n : ℕ) (μ : Measure ℝ)
    (σ : Profile) (rS : ℝ) : ℝ :=
  ∫ v, sellerRev k n σ rS (buyerValues k n v) ∂
    (Measure.pi (fun _ : Fin (nodes k n 0) => μ))

/-- Theorem 3.1: the tier-`t` mechanism `(r*_t, Y*_t) = (z_{W_{t−1}}, ψ_{W_{t−1}})`. -/
noncomputable def eqMech (k : ℕ → ℕ) (μ : Measure ℝ) (t : ℕ) : Mechanism :=
  (zproj (annLaw k μ (t - 1)), psi (annLaw k μ (t - 1)))

/-- The profile after tier-`t` history `h` (mechanisms of tiers `> t`) when node `(t, j)` uses
`m`; tier `t`'s other nodes and all lower tiers follow the history-independent profile `σ`. -/
def deviate (σ : ℕ → Mechanism) (h : ℕ → Mechanism)
    (t j : ℕ) (m : Mechanism) : Profile :=
  fun s i => if t < s then h s else if s = t ∧ i = j then m else σ s

/-- Definition A.3, p. 44, for the history-independent profile in which tier `t` uses `σ t` and
the seller uses reserve `rStar`: after every tier-`t` history (any mechanisms in `M` for tiers
`t+1, …, n`, any seller reserve `rS ≥ 0`), no tier-`t` node gains by any mechanism in `M`; and no
seller reserve `rS ≥ 0` beats `rStar`. -/
def IsSPE (k : ℕ → ℕ) (n : ℕ) (μ : Measure ℝ)
    (σ : ℕ → Mechanism) (rStar : ℝ) : Prop :=
  0 ≤ rStar ∧
  (∀ t, 1 ≤ t → t ≤ n →
    ∀ h : ℕ → Mechanism,
      (∀ s, t < s → s ≤ n → IsMech (h s)) →
      ∀ rS : ℝ, 0 ≤ rS →
        ∀ j, j < nodes k n t →
          ∀ m : Mechanism, IsMech m →
            Pi_int k n μ (deviate σ h t j m) rS t j ≤
              Pi_int k n μ (deviate σ h t j (σ t)) rS t j) ∧
  (∀ rS : ℝ, 0 ≤ rS →
    Pi_S k n μ (fun s _ => σ s) rS ≤
      Pi_S k n μ (fun s _ => σ s) rStar)

/-- Figure 3, (5)–(6), p. 35: expected profit of one intermediary with `m` i.i.d. buyers and mechanism
`(r, Y)`, facing a seller's reserve `rS` and an independent competing bid `D ∼ η`: it wins iff
`r ≤ w` and `Y(w) ≥ max(rS, D)` (`w` the highest buyer value), pays `P = max(rS, D)` and charges
`max(r, Y^{-1}(P), second highest value)`. -/
noncomputable def singleProfit (m : ℕ) (μ η : Measure ℝ) (rS : ℝ)
    (mech : Mechanism) : ℝ :=
  ∫ x, (let w := maxFin m x.1
    let upstreamPayment := max rS x.2
    if mech.1 ≤ w ∧ upstreamPayment ≤ mech.2 w then
      max (max mech.1 (ginv mech.2 upstreamPayment)) (secondMax m x.1) -
        upstreamPayment
    else 0) ∂((Measure.pi (fun _ : Fin m => μ)).prod η)

/-- Buyer `i` lies below node `(t, j)`. -/
def DescendantBuyer (k : ℕ → ℕ) (t j i : ℕ) : Prop :=
  i / (∏ s ∈ Finset.Icc 1 t, k s) = j

end AdInterm.SPE


