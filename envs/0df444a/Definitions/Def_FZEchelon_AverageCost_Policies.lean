-- Prove2me | Definitions.Def_FZEchelon_AverageCost_Policies
-- name    : FZEchelon_AverageCost_Policies
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T11:23:15.802545+00:00
-- url     : https://prove2.me/theorems/9def69db-a9b9-40d7-92d6-dd8945a21f05
-- title:
--   Measurable history-dependent policies, the expected n-period costs B_n, the average costs B (lim sup), the optimal average costs and the policy π*
-- statement:
--   This file defines the policies and the average-cost criterion of Federgruen and Zipkin (1984), pp. 823–825.
--
--   **Policies.** A policy chooses the action of each period as a function of the initial state and of the demands observed so far; together with a demand realization $\tilde u = (u_0, u_1, \dots)$ it determines the sequences of states and actions. A policy is **measurable** if each of its decision rules is measurable, and **feasible** from an initial state if along every demand realization every action it takes satisfies the constraints of the current state. A **stationary** policy applies a fixed decision rule to the current state.
--
--   **Costs.** For an initial state $s$ and a policy $\pi$, let $c_k$ be the one-period cost incurred in period $k$ (counting forward from the initial period $k = 0$). The expected $n$-period cost is
--   $$B_n(s \mid \pi) = E \sum_{k=0}^{n-1} \alpha^k c_k,$$
--   the expectation being over i.i.d. demands with law $\nu$, and the **average cost** is
--   $$B(s \mid \pi) = \limsup_{n \to \infty} \frac{1}{n} B_n(s \mid \pi).$$
--   This is done for the system (problem IH, one-period cost $c^d(y) + D(v^d + y^L) + c^r z + R(x^r + z)$), for the depot problem IH$^d$ (one-period cost $c^d(y) + D(v^d + y^L) + P(v^d + y^L)$, orders $y \ge 0$) and for the outlet problem IH$^r$ (one-period cost $c^r z + R(x^r + z)$, shipments $z \ge 0$). The minimal average costs of the depot and the outlet problems are
--   $$B^d(\tilde y, v^d) = \inf_{\pi^d} B^d(\tilde y, v^d \mid \pi^d),\qquad B^r(x^r) = \inf_{\pi^r} B^r(x^r \mid \pi^r),$$
--   the infima being over measurable feasible policies.
--
--   **The policy $\pi^*$** is the stationary policy that orders by a stationary depot rule $\sigma^d$ and ships by the modified critical-number rule with critical number $x^{r*}$.
--
--   **Formalization Note.** The paper numbers periods backward ($n$ = periods remaining) and writes $B_n = \sum_{i=1}^n \alpha^{n-i}[\cdots]$ with the initial state at index $n$; the Lean sum runs forward over $k = 0, \dots, n-1$ with weight $\alpha^k$, which is the same sum. Policies are deterministic and history-dependent; a decision rule is a function of the initial state and the observed demands, which is equivalent to a function of the past states and actions. $B_n$ is an extended real: the expectation of the sum of the positive parts of $\alpha^k c_k$ minus the expectation of the sum of their negative parts. The average cost is a $\limsup$ in the extended reals and the optimal costs are infima in the extended reals. $1/n$ is the real number $1/n$, so the $n = 0$ term is $0$ and does not affect the $\limsup$.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, pp. 823-825: policies Π (p. 823), B_n and the average-cost problem IH (p. 824), the outlet problems IH^r (p. 824), the depot problem IH^d and the policy π* (p. 825)

import Mathlib
import Definitions.Def_FZEchelon_AverageCost_Model

namespace FZEchelon.AverageCost

open MeasureTheory Filter

/-- A deterministic history-dependent policy for a controlled process with state space `S`,
action space `A` and real demands: the action in period `k = 0, 1, …` is a function of the
initial state and of the demands `u_0, …, u_{k−1}` already observed (p. 823: "a policy `π ∈ Π`
and `ũ` determine the sequences of states and actions"). Time runs forward: Lean period `k` is
the paper's period with `n − k` periods remaining. -/
def Policy (S A : Type*) : Type _ := (k : ℕ) → S × (Fin k → ℝ) → A

namespace Policy

variable {S A : Type*}

/-- The action taken in period `k` along the demand sequence `ω`, from initial state `s₀`. -/
def action (π : Policy S A) (s₀ : S) (ω : ℕ → ℝ) (k : ℕ) : A := π k (s₀, fun j : Fin k => ω j)

/-- The state in period `k` along the demand sequence `ω = (u_0, u_1, …)`, from initial state
`s₀`, for dynamics `f : state → action → demand → next state`. -/
def path (f : S → A → ℝ → S) (π : Policy S A) (s₀ : S) (ω : ℕ → ℝ) : ℕ → S
  | 0 => s₀
  | k + 1 => f (path f π s₀ ω k) (π.action s₀ ω k) (ω k)

/-- A policy is measurable if each of its decision rules is a measurable map. -/
def IsMeasurable [MeasurableSpace S] [MeasurableSpace A] (π : Policy S A) : Prop :=
  ∀ k, Measurable (π k)

/-- A policy is feasible from `s₀` if, along every demand sequence and in every period, its
action belongs to the constraint set `F` of the current state. -/
def IsFeasibleFrom (f : S → A → ℝ → S) (F : S → A → Prop) (π : Policy S A) (s₀ : S) : Prop :=
  ∀ (ω : ℕ → ℝ) (k : ℕ), F (path f π s₀ ω k) (π.action s₀ ω k)

/-- The state after the demands `h = (u_0, …, u_{k−1})` under the stationary rule `σ`. -/
def stationaryState (f : S → A → ℝ → S) (σ : S → A) (s₀ : S) : (k : ℕ) → (Fin k → ℝ) → S
  | 0, _ => s₀
  | k + 1, h =>
      f (stationaryState f σ s₀ k (Fin.init h)) (σ (stationaryState f σ s₀ k (Fin.init h)))
        (h (Fin.last k))

/-- The stationary policy that applies the decision rule `σ : S → A` to the current state. -/
def ofStationary (f : S → A → ℝ → S) (σ : S → A) : Policy S A :=
  fun k p => σ (stationaryState f σ p.1 k p.2)

/-- The expected `n`-period cost `B_n(s₀ | π) = E Σ_{k<n} α^k c(s_k, a_k)` (p. 824), with the
demands i.i.d. with law `ν` (`ω ∼ ν^{⊗ℕ}`). It is computed in `EReal` as the expectation of the
sum of the positive parts minus the expectation of the sum of the negative parts of the
discounted one-period costs. The paper numbers periods backward, so its weight `α^{n−i}` for
the period with `i` periods remaining is the weight `α^k` of Lean period `k = n − i`. -/
noncomputable def costN (f : S → A → ℝ → S) (c : S → A → ℝ) (α : ℝ) (ν : Measure ℝ)
    (π : Policy S A) (s₀ : S) (n : ℕ) : EReal :=
  ((∫⁻ ω, ∑ k ∈ Finset.range n,
      ENNReal.ofReal (α ^ k * c (path f π s₀ ω k) (π.action s₀ ω k))
      ∂(Measure.infinitePi fun _ : ℕ => ν) : ENNReal) : EReal)
  - ((∫⁻ ω, ∑ k ∈ Finset.range n,
      ENNReal.ofReal (-(α ^ k * c (path f π s₀ ω k) (π.action s₀ ω k)))
      ∂(Measure.infinitePi fun _ : ℕ => ν) : ENNReal) : EReal)

/-- The average cost `B(s₀ | π) = limsup_{n→∞} (1/n) B_n(s₀ | π)` (p. 824), in `EReal`. -/
noncomputable def avgCost (f : S → A → ℝ → S) (c : S → A → ℝ) (α : ℝ) (ν : Measure ℝ)
    (π : Policy S A) (s₀ : S) : EReal :=
  limsup (fun n : ℕ => (((1 : ℝ) / n : ℝ) : EReal) * costN f c α ν π s₀ n) atTop

end Policy

/-- `π^r` is an admissible shipment policy of problem IH^r from `x`: measurable and `z ≥ 0`. -/
def OutletAdmissible (π : Policy ℝ ℝ) (x : ℝ) : Prop :=
  π.IsMeasurable ∧ π.IsFeasibleFrom outletNext OutletFeasible x

namespace Model

variable (m : Model)

/-- `B_n(ŷ, v^d, x^r | π)`, the expected `n`-period cost of the system (p. 824). -/
noncomputable def sysCostN (π : Policy (SysState m.L) (ℝ × ℝ)) (s : SysState m.L) (n : ℕ) :
    EReal :=
  Policy.costN m.sysNext m.sysCost m.α m.ν π s n

/-- `B(ŷ, v^d, x^r | π) = limsup_n (1/n) B_n(ŷ, v^d, x^r | π)`, the average cost of the system
under `π` (p. 824). -/
noncomputable def sysAvg (π : Policy (SysState m.L) (ℝ × ℝ)) (s : SysState m.L) : EReal :=
  Policy.avgCost m.sysNext m.sysCost m.α m.ν π s

/-- `π` is an admissible policy of problem IH from `s`: measurable and feasible from `s`. -/
def SysAdmissible (π : Policy (SysState m.L) (ℝ × ℝ)) (s : SysState m.L) : Prop :=
  π.IsMeasurable ∧ π.IsFeasibleFrom m.sysNext m.SysFeasible s

/-- `B^d_n(ŷ, v^d | π^d)`, the expected `n`-period cost of the depot problem (p. 825). -/
noncomputable def depotCostN (xstar : ℝ) (π : Policy (DepotState m.L) ℝ) (p : DepotState m.L)
    (n : ℕ) : EReal :=
  Policy.costN m.depotNext (m.depotCost xstar) m.α m.ν π p n

/-- `B^d(ŷ, v^d | π^d)`, the average cost of the depot problem IH^d under `π^d` (p. 825). -/
noncomputable def depotAvg (xstar : ℝ) (π : Policy (DepotState m.L) ℝ) (p : DepotState m.L) :
    EReal :=
  Policy.avgCost m.depotNext (m.depotCost xstar) m.α m.ν π p

/-- `π^d` is an admissible order policy of problem IH^d from `p`: measurable and feasible. -/
def DepotAdmissible (π : Policy (DepotState m.L) ℝ) (p : DepotState m.L) : Prop :=
  π.IsMeasurable ∧ π.IsFeasibleFrom m.depotNext m.DepotFeasible p

/-- `a^d = B^d(ŷ, v^d) = inf {B^d(ŷ, v^d | π^d) : π^d ∈ Π^d}`, the minimal average cost of the
depot problem IH^d (pp. 825, 828), an infimum in `EReal` over the admissible order policies. -/
noncomputable def depotOptAvg (xstar : ℝ) (p : DepotState m.L) : EReal :=
  ⨅ π : {π : Policy (DepotState m.L) ℝ // m.DepotAdmissible π p}, m.depotAvg xstar π.1 p

/-- `B^r(x^r | π^r)`, the average cost of the outlet problem IH^r under `π^r` (p. 824). -/
noncomputable def outletAvg (π : Policy ℝ ℝ) (x : ℝ) : EReal :=
  Policy.avgCost outletNext m.outletCost m.α m.ν π x

/-- `B^r(x^r) = inf {B^r(x^r | π^r) : π^r ∈ Π^r}`, the minimal average cost of the outlet
problem IH^r (p. 824), an infimum in `EReal`. -/
noncomputable def outletOptAvg (x : ℝ) : EReal :=
  ⨅ π : {π : Policy ℝ ℝ // OutletAdmissible π x}, m.outletAvg π.1 x

/-- The order policy of the depot problem that applies the stationary rule `σd`. -/
def depotStationary (σd : DepotState m.L → ℝ) : Policy (DepotState m.L) ℝ :=
  Policy.ofStationary m.depotNext σd

/-- The policy `π*` (p. 825): the stationary policy that orders according to the depot rule
`σd` and ships according to the modified critical-number rule with critical number `xstar`. -/
def piStar (σd : DepotState m.L → ℝ) (xstar : ℝ) : Policy (SysState m.L) (ℝ × ℝ) :=
  Policy.ofStationary m.sysNext (m.sigmaStar σd xstar)

end Model

end FZEchelon.AverageCost


