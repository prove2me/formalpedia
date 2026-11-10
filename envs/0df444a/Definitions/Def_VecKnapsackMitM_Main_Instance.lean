-- Prove2me | Definitions.Def_VecKnapsackMitM_Main_Instance
-- name    : VecKnapsackMitM_Main_Instance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:32:51.885317+00:00
-- url     : https://prove2.me/theorems/ae610e8f-da00-47fb-8326-59e6ad13fec3
-- title:
--   d-Knapsack instances, feasibility and $(1-\varepsilon)$-approximate solutions (§2)
-- statement:
--   A $d$-Knapsack instance $(I,\bar W)$ (§2): $n$ items, item $i$ with profit $p(i)$ and weight vector $\bar w(i)\in\mathbb R^d$, and a capacity vector $\bar W\in\mathbb R^d$. Items are `Fin n` (the paper's item $i+1$ is `i`) and dimensions are `Fin d` (the paper's dimension $t+1$ is `t`; $\bar w_1$ is `t = 0`, $\bar w_d$ is `t = d - 1`, the middle dimensions $2,\dots,d-1$ are the `t` with $1\le t$, $t+2\le d$).
--
--   * `Items d n` holds `p : Fin n → ℝ` and `w : Fin n → Fin d → ℝ`; `Instance d n` adds `W : Fin d → ℝ`.
--   * `Items.Nonneg`: $p(i)\ge0$ and $\bar w(i)\ge0$; `Instance.Nonneg` adds $\bar W\ge0$ — the paper's $\mathbb R_{\ge0}$ conventions. Zero values, duplicate items and $n=0$ are allowed.
--   * `profit S` $=p(S)=\sum_{i\in S}p(i)$, `weight S t` $=\bar w_{t+1}(S)$.
--   * `SortedByProfit`: $p(1)\ge p(2)\ge\dots\ge p(n)$.
--   * `suffix n i` is the paper's $\{i+1,\dots,n\}$ (the `j` with $i\le j$); `maxOver J f` is $\max_{j\in J}f(j)$ for nonempty $J$ (and $0$ for $J=\emptyset$, never used there).
--   * `Feasible S`: $\bar w(S)\le\bar W$ coordinatewise. `IsApprox ε S`: $S$ is feasible and $p(S)\ge(1-\varepsilon)\,p(S')$ for every feasible $S'$, i.e. $p(S)\ge(1-\varepsilon)\mathrm{OPT}$ ($\mathrm{OPT}$ is a maximum over finitely many feasible sets; $\emptyset$ is feasible when $\bar W\ge0$).
--   * `reindex σ` lists the items in the order $\sigma$: its item $j$ is the original item $\sigma(j)$.
--
--   The paper's simplifying assumptions "$\bar w(i)\le\bar W$" and "items sorted by profit" are proof conventions and are not built into these definitions; a statement that needs sortedness (Lemma 4.2) says so.
-- source:
--   Bringmann, Kulik, Węgrzycki (2026), Fine-Grained Complexity of Approximating Vector Knapsack: A Faster Algorithm and Equivalence with k-SUM in 2D, STOC 2027 submission, SHA-256 966f42f7…10ac98; §2 Preliminaries, printed pp. 7–8 (PDF 8–9)

import Mathlib

namespace VecKnapsackMitM.Main

/-! d-Knapsack (Bringmann, Kulik, Węgrzycki 2026, STOC 2027 submission, §2, printed p. 7,
PDF 8). Items are `Fin n` (the paper's item `i + 1` is `i`), dimensions are `Fin d` (the
paper's dimension `t + 1` is `t`; so the paper's first dimension is `t = 0`, its last
dimension `d` is `t = d - 1`, and its middle dimensions `2, …, d - 1` are the `t` with
`1 ≤ t` and `t + 2 ≤ d`). -/

/-- A list of `n` items in dimension `d`: item `i` has profit `p i` and weight vector `w i`. -/
structure Items (d n : ℕ) where
  /-- profit `p(i)` -/
  p : Fin n → ℝ
  /-- weight vector `w̄(i)`; `w i t` is the paper's `w̄_{t+1}(i)` -/
  w : Fin n → Fin d → ℝ

/-- A d-Knapsack instance `(I, W̄)`: items and a capacity vector `W`. -/
structure Instance (d n : ℕ) extends Items d n where
  /-- capacities `W̄`; `W t` is the paper's `W̄_{t+1}` -/
  W : Fin d → ℝ

namespace Items

variable {d n : ℕ} (I : Items d n)

/-- The paper's standing sign convention: `p(i) ∈ ℝ≥0` and `w̄(i) ∈ ℝ^d_{≥0}`. -/
def Nonneg : Prop := (∀ i, 0 ≤ I.p i) ∧ ∀ i t, 0 ≤ I.w i t

/-- `p(S) = ∑_{i ∈ S} p(i)`. -/
def profit (S : Finset (Fin n)) : ℝ := ∑ i ∈ S, I.p i

/-- `w̄_{t+1}(S) = ∑_{i ∈ S} w̄_{t+1}(i)`. -/
def weight (S : Finset (Fin n)) (t : Fin d) : ℝ := ∑ i ∈ S, I.w i t

/-- Items sorted by non-increasing profit: `p(1) ≥ p(2) ≥ … ≥ p(n)`. -/
def SortedByProfit : Prop := ∀ i j : Fin n, i ≤ j → I.p j ≤ I.p i

/-- The suffix `{i + 1, …, n}` of the paper (0-based: the items `j` with `i ≤ j`). -/
def suffix (n i : ℕ) : Finset (Fin n) := Finset.univ.filter fun j => i ≤ j.val

/-- `max_{j ∈ J} f(j)` for a nonempty `J`; `0` for `J = ∅` (never used on `∅`). -/
noncomputable def maxOver (J : Finset (Fin n)) (f : Fin n → ℝ) : ℝ :=
  if h : J.Nonempty then J.sup' h f else 0

end Items

namespace Instance

variable {d n : ℕ} (inst : Instance d n)

/-- Nonnegative profits, weights and capacities (§2: `W̄ ∈ ℝ^d_{≥0}`, `p(i) ∈ ℝ≥0`,
`w̄(i) ∈ ℝ^d_{≥0}`). Zero values, duplicates and `n = 0` are allowed. -/
def Nonneg : Prop := inst.toItems.Nonneg ∧ ∀ t, 0 ≤ inst.W t

/-- `S` is feasible: `w̄(S) ≤ W̄` in every coordinate. -/
def Feasible (S : Finset (Fin n)) : Prop := ∀ t, inst.toItems.weight S t ≤ inst.W t

/-- `S` is a `(1 − ε)`-approximate solution: feasible, with `p(S) ≥ (1 − ε) · p(S')` for every
feasible `S'`, i.e. `p(S) ≥ (1 − ε) · OPT` (`OPT` is the maximum of `p` over the finitely many
feasible sets, attained since `∅` is feasible when `W̄ ≥ 0`). -/
def IsApprox (ε : ℝ) (S : Finset (Fin n)) : Prop :=
  inst.Feasible S ∧ ∀ S' : Finset (Fin n), inst.Feasible S' → (1 - ε) * inst.toItems.profit S' ≤
    inst.toItems.profit S

/-- The instance with its items listed in the order `σ`: its item `j` is the original item
`σ j`. -/
def reindex (σ : Equiv.Perm (Fin n)) : Instance d n :=
  ⟨⟨fun j => inst.p (σ j), fun j => inst.w (σ j)⟩, inst.W⟩

end Instance

end VecKnapsackMitM.Main


