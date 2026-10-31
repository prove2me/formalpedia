-- Prove2me | Definitions.Def_ParallelLotteries_Model
-- name    : ParallelLotteries_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:07.458233+00:00
-- url     : https://prove2.me/theorems/e6734747-da03-478b-af4a-95f61fd90da9
-- title:
--   The $k$-ticket lottery: strategies, win probabilities $\chi$, equilibria, feasible allocations and trade reallocations
-- statement:
--   There are $n$ types of items with quantities $\mu=(\mu_1,\dots,\mu_n)\in\mathbb R^n_+$, a mass $M$ of agents, and agent types $v\in\mathbb R^n$ ($v_i$ is the value for item $i$; the outside option has value $0$) distributed according to a probability measure $\eta$. This module defines the $k$-ticket lottery model of §3.
--
--   1. **Strategies.** A strategy $s=(t,\succ)$ consists of a ticket vector $t\in\mathbb N^n$ ($t_i$ tickets in the lottery for item $i$) and a preference ranking $\succ$ over the items. $S_k$ is the set of strategies with at most $k$ tickets, $\sum_i t_i\le k$.
--   2. **Win probabilities** (1). For a vector $p\in[0,1]^n$ of per-ticket win probabilities,
--   $$\chi_i(s,p) := \bigl(1-(1-p_i)^{t_i}\bigr)\prod_{j\succ i}(1-p_j)^{t_j},$$
--   the probability that the agent wins item $i$: some ticket for $i$ is drawn and no ticket for a preferred item is drawn.
--   3. **Welfare** (2). $w(v,s,p) := v\cdot\chi(s,p)=\sum_i v_i\chi_i(s,p)$.
--   4. **Optimality** (Definition 1). A strategy profile $\Phi:\mathbb R^n\to S_k$ is optimal given $p$ if for every type $v$, $\Phi(v)$ maximizes $w(v,s,p)$ over $s\in S_k$.
--   5. **Consistency** (Definition 2, (4)). $p$ is consistent with $\Phi$ if for every item $i$
--   $$M\sum_{s\in S_k}\chi_i(s,p)\,\eta(\{v:\Phi(v)=s\})\le\mu_i,$$
--   with equality if $p_i<1$.
--   6. **Equilibrium** (Definition 3). A $k$-ticket equilibrium is a pair $(\Phi,p)$ with $\Phi$ optimal given $p$ and $p$ consistent with $\Phi$. Its allocation is $x(v)=\chi(\Phi(v),p)$.
--   7. **Feasible allocation** (§3.3). A map $x:\mathbb R^n\to[0,1]^n$ with (5) $M\int x_i\,d\eta\le\mu_i$ for every $i$ and (6) $\sum_i x_i(v)\le1$ for every $v$.
--   8. **Trade reallocation** (Definition 7). A feasible allocation $x'$ with $\int x\,d\eta=\int x'\,d\eta$, i.e. the same total quantity of every item.
--
--   These are the objects of Theorem 2 (every $k$-ticket equilibrium allocation is $(2-1/k)$-trade efficient).
--
--   **Formalization Note** Items are indexed by `Fin n` and types are vectors `Fin n → ℝ`. A preference ranking is encoded by the permutation sending each item to its position (position $0$ = most preferred), so $j\succ i$ means that $j$ has a smaller position; every strict total order arises from exactly one such permutation. Ticket counts are stored in $\{0,\dots,k\}$, so $S_k$ is a finite type; it carries the discrete σ-algebra. An equilibrium additionally requires $p\in[0,1]^n$ and $\Phi$ measurable, and a feasible allocation is required to be measurable: the paper's integrals and the measures $\eta(\{v:\Phi(v)=s\})$ presuppose this, and in Lean the integral of a non-integrable function is $0$. The equality of integrals in Definition 7 is read componentwise.
-- source:
--   Arnosti–Randolph, Alaskan Hunting License Lotteries Are Flexible and Approximately Efficient, SSRN 3370605 (preprint), §3, p.5 (model), §3.1, p.5 (strategies, S_k), (1)–(3) and Definition 1, p.6, Definition 2 (4) and Definition 3, p.7, §3.3 (5)–(6), p.8, Definition 7, p.10

import Mathlib

open MeasureTheory

namespace ParallelLotteries

/-- **Strategies with at most `k` tickets**, the set `S_k` of Arnosti–Randolph, *Alaskan Hunting
License Lotteries Are Flexible and Approximately Efficient*, SSRN 3370605 (preprint), §3.1, p.5:
"The agent's interaction with the k-ticket lottery is summarized by a strategy s = (t, ≻)
consisting of a ticket allocation vector t = (t₁, …, tₙ) and a preference ranking ≻ over the set
of items. […] Let S_k denote the set of all possible strategies with at most k tickets."

A strategy is a pair `(t, rank)`: `t i` is the number of tickets entered in lottery `i`, and
`rank : Equiv.Perm (Fin n)` gives each item its position in the ranking (position `0` is the most
preferred item), subject to `∑ i, t i ≤ k`.

**Formalization Note.** Items are `Fin n`. A strict total order `≻` on `Fin n` is encoded by the
unique bijection `rank` sending each item to its position, with `j ≻ i ↔ rank j < rank i`
(`Strategy.Prefers`); every strict total order arises from exactly one `rank`. Ticket counts are
stored in `Fin (k + 1)` (no count can exceed `k`), which makes `S_k` a finite type. It carries the
discrete σ-algebra, so a strategy profile `Φ : (Fin n → ℝ) → Strategy n k` is measurable exactly
when every set `{v | Φ v = s}` is measurable. -/
def Strategy (n k : ℕ) : Type :=
  {s : (Fin n → Fin (k + 1)) × Equiv.Perm (Fin n) // ∑ i, (s.1 i : ℕ) ≤ k}

instance (n k : ℕ) : Fintype (Strategy n k) := by unfold Strategy; infer_instance

instance (n k : ℕ) : DecidableEq (Strategy n k) := by unfold Strategy; infer_instance

/-- The discrete σ-algebra on the finite strategy set `S_k`. -/
instance (n k : ℕ) : MeasurableSpace (Strategy n k) := ⊤

instance (n k : ℕ) : DiscreteMeasurableSpace (Strategy n k) := ⟨fun _ => trivial⟩

/-- The number `t_i` of tickets a strategy enters in the lottery for item `i`. -/
def Strategy.tickets {n k : ℕ} (s : Strategy n k) (i : Fin n) : ℕ := (s.1.1 i : ℕ)

/-- The position of each item in the strategy's preference ranking (`0` = most preferred). -/
def Strategy.rank {n k : ℕ} (s : Strategy n k) : Equiv.Perm (Fin n) := s.1.2

/-- `s.Prefers j i` is the paper's `j ≻ i`: the strategy ranks item `j` above item `i`. -/
def Strategy.Prefers {n k : ℕ} (s : Strategy n k) (j i : Fin n) : Prop := s.rank j < s.rank i

/-- **Win probabilities of a strategy**, display (1), SSRN 3370605 (preprint), §3.1, p.6:
`χ_i(s, p) := (1 − (1 − p_i)^{t_i}) ∏_{j ≻ i} (1 − p_j)^{t_j}`, the probability that an agent
using strategy `s` receives item `i` when each ticket in lottery `j` is drawn with probability
`p_j`. The product runs over **all** items ranked above `i` (items with no tickets contribute the
factor `1`). -/
noncomputable def chi {n k : ℕ} (s : Strategy n k) (p : Fin n → ℝ) (i : Fin n) : ℝ :=
  (1 - (1 - p i) ^ s.tickets i) *
    ∏ j ∈ Finset.univ.filter (fun j => s.rank j < s.rank i), (1 - p j) ^ s.tickets j

/-- **Expected welfare**, display (2), SSRN 3370605 (preprint), §3.1, p.6:
`w(v, s, p) := v · χ(s, p) = ∑_i v_i χ_i(s, p)`; the outside option has value `0`. -/
noncomputable def welfare {n k : ℕ} (v : Fin n → ℝ) (s : Strategy n k) (p : Fin n → ℝ) : ℝ :=
  ∑ i, v i * chi s p i

/-- **Optimal strategy profile**, Definition 1, display (3), SSRN 3370605 (preprint), p.6:
`Φ` is optimal given `p` if `∀ v, Φ(v) ∈ argmax_{s ∈ S_k} w(v, s, p)`, i.e. for every type `v`
and every strategy `s ∈ S_k`, `w(v, s, p) ≤ w(v, Φ(v), p)`. -/
def IsOptimal {n k : ℕ} (p : Fin n → ℝ) (Φ : (Fin n → ℝ) → Strategy n k) : Prop :=
  ∀ (v : Fin n → ℝ) (s : Strategy n k), welfare v s p ≤ welfare v (Φ v) p

/-- **Consistency of win probabilities with supply**, Definition 2, display (4),
SSRN 3370605 (preprint), p.7: for every item `i`,
`M ∑_{s ∈ S_k} χ_i(s, p) η({v : Φ(v) = s}) ≤ μ_i`, with equality if `p_i < 1`.
Here `M` is the mass of agents, `μ_i` the quantity of item `i` and `η` the type distribution.

**Formalization Note.** `η({v : Φ v = s})` is taken as a real number (`ENNReal.toReal`); for a
probability measure it is finite, so nothing is lost. -/
def IsConsistent {n k : ℕ} (M : ℝ) (μ : Fin n → ℝ) (η : Measure (Fin n → ℝ))
    (Φ : (Fin n → ℝ) → Strategy n k) (p : Fin n → ℝ) : Prop :=
  ∀ i : Fin n,
    M * ∑ s : Strategy n k, chi s p i * (η {v | Φ v = s}).toReal ≤ μ i ∧
    (p i < 1 → M * ∑ s : Strategy n k, chi s p i * (η {v | Φ v = s}).toReal = μ i)

/-- **k-ticket equilibrium**, Definition 3, SSRN 3370605 (preprint), p.7: a pair `(Φ, p)` of a
strategy profile and a vector of win probabilities such that `Φ` is optimal given `p` and `p` is
consistent with `Φ`.

**Formalization Note.** Two conditions the paper uses implicitly are written out: each `p_i` is a
probability (`0 ≤ p_i ≤ 1`), and `Φ` is measurable (so that `η({v : Φ(v) = s})` in (4) is the
measure of a measurable set). -/
def IsEquilibrium {n k : ℕ} (M : ℝ) (μ : Fin n → ℝ) (η : Measure (Fin n → ℝ))
    (Φ : (Fin n → ℝ) → Strategy n k) (p : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ p i ∧ p i ≤ 1) ∧ Measurable Φ ∧ IsOptimal p Φ ∧ IsConsistent M μ η Φ p

/-- **The allocation of a k-ticket equilibrium**, SSRN 3370605 (preprint), §3.3, p.8:
"A k-ticket lottery equilibrium (Φ, p) corresponds to the allocation x such that
x(v) = χ(Φ(v), p)." -/
noncomputable def eqAllocation {n k : ℕ} (Φ : (Fin n → ℝ) → Strategy n k) (p : Fin n → ℝ) :
    (Fin n → ℝ) → Fin n → ℝ :=
  fun v i => chi (Φ v) p i

/-- **Feasible (probabilistic) allocation**, SSRN 3370605 (preprint), §3.3, p.8: a function
`x : ℝⁿ → [0, 1]ⁿ` such that
(5) `∀ i, M ∫ x_i(v) dη ≤ μ_i` (quantities are respected) and
(6) `∀ v, ∑_i x_i(v) ≤ 1` (each agent receives at most one item).

**Formalization Note.** `x` is required to be measurable. The paper's integrals presuppose it, and
in Lean the integral of a non-integrable function is `0`, which would make (5) and the trade
constraint of Definition 7 conditions on a junk value. A measurable `x` with values in `[0, 1]ⁿ`
is integrable for a probability measure. -/
def IsFeasibleAllocation {n : ℕ} (M : ℝ) (μ : Fin n → ℝ) (η : Measure (Fin n → ℝ))
    (x : (Fin n → ℝ) → Fin n → ℝ) : Prop :=
  Measurable x ∧ (∀ v i, 0 ≤ x v i ∧ x v i ≤ 1) ∧
    (∀ i, M * ∫ v, x v i ∂η ≤ μ i) ∧ (∀ v, ∑ i, x v i ≤ 1)

/-- **Trade reallocation**, Definition 7, SSRN 3370605 (preprint), p.10: "A trade reallocation of
x is a feasible allocation x′ such that ∫ x(v) dη = ∫ x′(v) dη." The vector integral is read
componentwise: `∀ i, ∫ x_i dη = ∫ x′_i dη`. -/
def IsTradeReallocation {n : ℕ} (M : ℝ) (μ : Fin n → ℝ) (η : Measure (Fin n → ℝ))
    (x x' : (Fin n → ℝ) → Fin n → ℝ) : Prop :=
  IsFeasibleAllocation M μ η x' ∧ ∀ i, ∫ v, x v i ∂η = ∫ v, x' v i ∂η

end ParallelLotteries


