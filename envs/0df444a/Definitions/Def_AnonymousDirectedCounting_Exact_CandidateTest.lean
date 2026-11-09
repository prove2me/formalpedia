-- Prove2me | Definitions.Def_AnonymousDirectedCounting_Exact_CandidateTest
-- name    : AnonymousDirectedCounting_Exact_CandidateTest
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:30.152271+00:00
-- url     : https://prove2.me/theorems/73243435-48f0-441d-a2bb-72676d3d4129
-- title:
--   The five-step candidate test, credit and ratios
-- statement:
--   Fix a leader count $\ell$, a final level $k$, a candidate $m$ and a vista with bottom node $s$. The test rejects unless all of the following hold.
--
--   Step 1: $\mathcal L_0$ contains the leader node, each $\mathcal L_r$ with $0\le r\le k$ has at most $m$ nodes, and every node of $\mathcal L_r$ with $0\le r<k$ has a child in $\mathcal L_{r+1}$. Step 2: $h$ is the largest index in $1,\dots,k$ with $\mathcal L_h$ flat, and such an index exists. Step 3: the flow equations on $\mathcal L_h$ with the leader equation have a unique solution over $\mathbb Q$, all its values are positive integers, and they total $m$. Step 4: $b(u)=\sum_{v\text{ child of }u}b(v)$ for $u\in\mathcal L_r$, $0\le r<h$, and these values satisfy the visible flow equations at each level $1\le r<h$. Step 5: for each $v\in\mathcal L_h$, the number $q(v)$ of its descendants in $\mathcal L_k$, counting $v$ itself if $h=k$, is at most $b(v)$.
--
--   The core test is the case $k=m$; the sharp test is $k=m-1$. For the analysis, on a network, the credit of a node is $c(v)=\min\{a(v)-1,b(v)\}$, the total credit is $\Phi_r=\sum_{v\in\mathcal L_r}c(v)$, and the ratio is $\rho(v)=a(v)/b(v)$. The set $\mathcal D$ collects the nodes of a level with a given ratio and $\mathcal Q$ their parents.
--
--   **Formalization Note** The test is stated as a predicate on the vista: the anchor and the values of $b$ are existentially quantified, and Steps 2 and 3 determine them uniquely on visible nodes. Step 4's value at the root is omitted because no check reads it.
-- source:
--   Giuseppe A. Di Luna, Giovanni Viglietta, STOC 2027 submission #455 (October 2026), Section 3.1, printed pp. 6–7 (PDF pp. 8–9); Section 3.2, printed p. 9 (PDF p. 11)

import Mathlib
import Definitions.Def_AnonymousDirectedCounting_Exact_HistoryTree

set_option autoImplicit false

namespace AnonymousDirectedCounting.Exact

open scoped Classical

noncomputable section

/-- Steps 1-4 of the candidate test (printed pp. 6-7, PDF pp. 8-9) on the prefix of the vista `s`
ending at the final level `k`, for candidate `m` and leader count `ell`. The core test has
`k = m`, the sharp test `k = m - 1`. `h` is the anchor; `b r` holds the candidate anonymities at
level `r ≤ h`. Each field is a check the agent runs on its own vista; nothing here mentions a
network, a fiber or `n`. `h` and the visible values of `b` are determined by `s`: `h` is the
largest flat index, Step 3 is a unique solution, Step 4 propagates it. -/
structure PassesStepsOneToFour (ell k m : ℕ) {t : ℕ} (s : History t) (h : ℕ)
    (b : (r : ℕ) → History r → ℚ) : Prop where
  /-- Step 1: `L_0` contains the leader node. -/
  leader_visible : leaderRoot ∈ vistaLevel t s 0
  /-- Step 1: each `L_r`, `0 ≤ r ≤ k`, has at most `m` nodes. -/
  node_bound : ∀ r : ℕ, r ≤ k → (vistaLevel t s r).card ≤ m
  /-- Step 1: every node of `L_r`, `0 ≤ r < k`, has a child in `L_{r+1}`. -/
  has_child : ∀ r : ℕ, r < k → ∀ u ∈ vistaLevel t s r, (childrenIn s r u).Nonempty
  /-- Steps 1-2: `h` is the largest index in `1, ..., k` with `L_h` flat. -/
  anchor_pos : 1 ≤ h
  anchor_le : h ≤ k
  anchor_flat : IsFlatLevel s h
  anchor_last : ∀ r : ℕ, h < r → r ≤ k → ¬ IsFlatLevel s r
  /-- Step 3: `b h` solves the anchor system over `ℚ`. -/
  anchor_solves : FlowSystem ℚ ell s h (b h)
  /-- Step 3: the solution is unique (as a function on the unknowns, the nodes of `L_h`). -/
  anchor_unique : ∀ b' : History h → ℚ, FlowSystem ℚ ell s h b' →
    ∀ v ∈ vistaLevel t s h, b' v = b h v
  /-- Step 3: every candidate anonymity at the anchor is a positive integer. -/
  anchor_integral : ∀ v ∈ vistaLevel t s h, ∃ z : ℕ, 0 < z ∧ b h v = (z : ℚ)
  /-- Step 3: the candidate anonymities at the anchor total `m`. -/
  anchor_total : ∑ v ∈ vistaLevel t s h, b h v = (m : ℚ)
  /-- Step 4: backward propagation, `b(u) = ∑_{v child of u} b(v)`. -/
  propagated : ∀ r : ℕ, r < h → ∀ u ∈ vistaLevel t s r,
    b r u = ∑ v ∈ childrenIn s r u, b (r + 1) v
  /-- Step 4: the visible flow equations hold at every level `1 ≤ r < h`. -/
  earlier_flow : ∀ r : ℕ, 1 ≤ r → r < h → VisibleFlow ℚ s r (b r)

/-- `q(v)`: the descendants of `v ∈ L_h` in the final level `L_k`, counting `v` itself if `h = k`. -/
def descendantCount {t : ℕ} (s : History t) (k h : ℕ) (v : History h) : ℕ :=
  ((vistaLevel t s k).filter (fun w => blackAncestor k w h = some v)).card

/-- The whole test: Steps 1-4 and Step 5, `q(v) ≤ b(v)` for each anchor node. -/
def Accepts (ell k m : ℕ) {t : ℕ} (s : History t) : Prop :=
  ∃ (h : ℕ) (b : (r : ℕ) → History r → ℚ), PassesStepsOneToFour ell k m s h b ∧
    ∀ v ∈ vistaLevel t s h, (descendantCount s k h v : ℚ) ≤ b h v

/-- The credit `c(v) = min {a(v) - 1, b(v)}` (printed p. 7, PDF p. 9), used only in the analysis. -/
def credit {n : ℕ} (G : NetworkModel n) (b : (r : ℕ) → History r → ℚ) (r : ℕ)
    (v : History r) : ℚ :=
  min ((anonymity G r v : ℚ) - 1) (b r v)

/-- The total credit `Φ_r = ∑_{v ∈ L_r} c(v)` on a level of the round-`t` vista of `x`. -/
def totalCredit {n : ℕ} (G : NetworkModel n) (t : ℕ) (x : Fin n)
    (b : (r : ℕ) → History r → ℚ) (r : ℕ) : ℚ :=
  ∑ v ∈ agentLevel G t x r, credit G b r v

/-- The ratio `ρ(v) = a(v) / b(v)`. -/
def ratio {n : ℕ} (G : NetworkModel n) (b : (r : ℕ) → History r → ℚ) (r : ℕ)
    (v : History r) : ℚ :=
  (anonymity G r v : ℚ) / b r v

/-- `D = {v ∈ L_r : ρ(v) = α}`. -/
def minRatioNodes {n : ℕ} (G : NetworkModel n) (t : ℕ) (x : Fin n)
    (b : (r : ℕ) → History r → ℚ) (r : ℕ) (α : ℚ) : Finset (History r) :=
  (agentLevel G t x r).filter (fun v => ratio G b r v = α)

/-- `Q`, the set of parents of the nodes of a set `D ⊆ L_{i+1}`. -/
def parentsOf {i : ℕ} (D : Finset (History (i + 1))) : Finset (History i) :=
  D.image parent

end

end AnonymousDirectedCounting.Exact


