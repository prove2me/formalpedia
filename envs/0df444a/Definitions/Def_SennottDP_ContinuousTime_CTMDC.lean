-- Prove2me | Definitions.Def_SennottDP_ContinuousTime_CTMDC
-- name    : SennottDP_ContinuousTime_CTMDC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T10:51:35.660669+00:00
-- url     : https://prove2.me/theorems/49273c08-13fb-4e8f-9d12-185b166d35df
-- title:
--   Continuous time Markov decision chain, its average cost, Assumptions (CTB) and (CTAC), and the auxiliary MDC
-- statement:
--   A **continuous time Markov decision chain** (CTMDC) $\Psi$ has a countable state space $S$ and, for each $i\in S$, a finite nonempty action set $A_i$. Choosing $a\in A_i$ in state $i$ incurs an instantaneous cost $G(i,a)\ge0$ and a cost rate $g(i,a)\ge0$ in effect until the next transition; the time until the next transition is exponentially distributed with parameter $\nu(i,a)>0$, and the new state is $j$ with probability $P_{ij}(a)$, where $P_{ii}(a)=0$. The expected sojourn time is $\tau(i,a)=1/\nu(i,a)$.
--
--   A **policy** $\theta$ chooses, at each transition epoch, an action (possibly at random) as a function of the past states, past actions and past sojourn times. Let $E_\theta[C_n\mid X_0=i]$ be the total expected cost and $E_\theta[T_n\mid X_0=i]$ the total expected time of the first $n$ transition periods. The **average cost** of $\theta$ and the **minimum average cost** are
--
--   $$J^\Psi_\theta(i)=\limsup_{n\to\infty}\frac{E_\theta[C_n\mid X_0=i]}{E_\theta[T_n\mid X_0=i]},\qquad J^\Psi(i)=\inf_\theta J^\Psi_\theta(i),\qquad i\in S.$$
--
--   **Assumption (CTB)** holds for constants $\tau$ and $B$ if $0<\tau<\inf_{i,a}\tau(i,a)\le\sup_{i,a}\tau(i,a)\le B<\infty$.
--
--   The **auxiliary MDC** $\Delta$ built with $\tau$ has the same states and actions, costs $C(i,a)=G(i,a)\nu(i,a)+g(i,a)$, and transition probabilities
--   $$P^*_{ij}(a)=\begin{cases}\tau\,\nu(i,a)\,P_{ij}(a), & j\ne i,\\ 1-\tau\,\nu(i,a), & j=i.\end{cases}$$
--   **Assumption (CTAC)** is $J^\Delta(\cdot)\le J^\Psi(\cdot)$, $J^\Delta$ the minimum average cost of $\Delta$.
--
--   For a stationary policy $e$, a constant $Z$ and a function $z$, **inequality (10.15)** is
--   $$Z\tau(i,e)+z(i)\ge G(i,e)+g(i,e)\tau(i,e)+\sum_j P_{ij}(e)z(j),\qquad i\in S,$$
--   and, for a function $w$, **inequality (10.20)** is $Z+w(i)\ge C(i,e)+\sum_j P^*_{ij}(e)w(j)$, $i\in S$.
--
--   These definitions set up the reduction of average cost optimization of a CTMDC to that of a discrete time MDC.
--
--   **Formalization Note** Data and axioms are separated (`CTMDC.IsValid`); nonnegativity of $G$ and $g$ is the book's standing convention that costs are nonnegative. The expected sums over $n$ transition periods are computed by a recursion in which the sojourn time is integrated against Mathlib's `expMeasure (ν i a)` and the next state is drawn independently from $P_{i\cdot}(a)$; policies are required to be measurable in the past sojourn times; all expectations and $J^\Psi$ are $[0,\infty]$-valued. The strict inequality $\tau<\inf\tau(i,a)$ of (CTB) is stated as the existence of $\varepsilon>0$ with $\tau+\varepsilon\le\tau(i,a)$ for all $i$, $a\in A_i$. In (10.15) and (10.20) the convergence of the series is part of the inequality, as its finiteness is implicit in the book.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 241–246, Section 10.2, eq. (10.13), Assumption (CTB) (10.14), (10.15), (10.19), (10.20), Assumption (CTAC)

import Mathlib
import Definitions.Def_SennottDP_ContinuousTime_MDC

open scoped ENNReal NNReal
open Classical Filter MeasureTheory ProbabilityTheory

namespace SennottDP.ContinuousTime

/-- A continuous time Markov decision chain (CTMDC) `Ψ` (Sennott, §10.2, pp. 241–242): a state
space `S`, for each state `i` a finite action set `A i`; choosing `a ∈ A i` in `i` incurs an
instantaneous cost `G i a` and a cost rate `g i a` in effect until the next transition; the time
until the next transition is exponentially distributed with parameter `ν i a`, and the new state
is chosen according to the distribution `(P i a j)_j`. The structure holds the data only; the
axioms are `CTMDC.IsValid`. -/
structure CTMDC (S : Type) (Act : Type) where
  A : S → Finset Act
  G : S → Act → ℝ
  g : S → Act → ℝ
  ν : S → Act → ℝ
  P : S → Act → S → ℝ≥0∞

namespace CTMDC

variable {S Act : Type} (Ψ : CTMDC S Act)

/-- The axioms of a CTMDC (§10.2): every `A i` is nonempty; for `a ∈ A i` the costs `G(i,a)`,
`g(i,a)` are nonnegative (the book's standing convention that costs are nonnegative, Ch. 2), the
rate `ν(i,a)` is positive, `(P_{ij}(a))_j` is a probability distribution, and `P_{ii}(a) = 0`
(every transition is a real change of state, p. 242). -/
def IsValid : Prop :=
  (∀ i, (Ψ.A i).Nonempty) ∧
    (∀ i, ∀ a ∈ Ψ.A i, 0 ≤ Ψ.G i a ∧ 0 ≤ Ψ.g i a ∧ 0 < Ψ.ν i a) ∧
    (∀ i, ∀ a ∈ Ψ.A i, ∑' j, Ψ.P i a j = 1) ∧
    ∀ i, ∀ a ∈ Ψ.A i, Ψ.P i a i = 0

/-- The expected time until a change of state, `τ(i,a) = 1/ν(i,a)` (p. 244). -/
noncomputable def meanSojourn (i : S) (a : Act) : ℝ := 1 / Ψ.ν i a

/-- Assumption (CTB), (10.14), p. 244, for the constants `τ` (here `tau`) and `B`:
`0 < τ < inf_{i,a} τ(i,a) ≤ sup_{i,a} τ(i,a) ≤ B < ∞`. The strict inequality
`τ < inf_{i,a} τ(i,a)` (infimum over `i ∈ S`, `a ∈ A_i`) is written as the existence of a
margin `ε > 0` with `τ + ε ≤ τ(i,a)` for all `i`, `a ∈ A_i`, which is equivalent and avoids the
junk value of a real infimum. -/
def CTB (tau B : ℝ) : Prop :=
  0 < tau ∧ (∃ ε > 0, ∀ i, ∀ a ∈ Ψ.A i, tau + ε ≤ Ψ.meanSojourn i a) ∧
    ∀ i, ∀ a ∈ Ψ.A i, Ψ.meanSojourn i a ≤ B

/-- A policy for `Ψ` (§10.3, p. 243): a nonanticipatory, possibly randomized rule choosing an
action at each transition epoch from the history of past states, past actions and past sojourn
times. After `k` transitions the history is `(sa, t, i)`: `sa m = (X_m, Y_m)` the state and action
of the `m`-th sojourn, `t m` its length, and `i` the current state. `σ k sa t i a` is the
probability of choosing `a`; it is a probability distribution on `A i`, and it is measurable in
the past sojourn times. -/
structure Policy where
  σ : (k : ℕ) → (Fin k → S × Act) → (Fin k → ℝ) → S → Act → ℝ≥0∞
  σ_sum : ∀ k sa t i, ∑ a ∈ Ψ.A i, σ k sa t i a = 1
  σ_supp : ∀ k sa t i a, a ∉ Ψ.A i → σ k sa t i a = 0
  σ_meas : ∀ k sa i a, Measurable (fun t : Fin k → ℝ => σ k sa t i a)

variable {Ψ}

/-- `expectedSum θ f n k sa t i`: the expected value of `Σ f(X_m, Y_m, σ_m)` over the next `n`
transition periods, when `k` transitions have occurred with history `(sa, t)` and the current
state is `i`. In state `i` the action `a` is drawn from `θ`, the sojourn time `s` is exponential
with parameter `ν(i,a)` (`ProbabilityTheory.expMeasure`), and the next state `j` is drawn from
`P_{i·}(a)` independently of `s` (§10.2). -/
noncomputable def expectedSum (θ : Ψ.Policy) (f : S → Act → ℝ → ℝ≥0∞) :
    ℕ → (k : ℕ) → (Fin k → S × Act) → (Fin k → ℝ) → S → ℝ≥0∞
  | 0, _, _, _, _ => 0
  | n + 1, k, sa, t, i =>
      ∑ a ∈ Ψ.A i, θ.σ k sa t i a *
        ∫⁻ s, (f i a s + ∑' j, Ψ.P i a j *
            expectedSum θ f n (k + 1) (Fin.snoc (α := fun _ => S × Act) sa (i, a))
              (Fin.snoc (α := fun _ => ℝ) t s) j) ∂(expMeasure (Ψ.ν i a))

variable (Ψ)

/-- The cost of one transition period in state `i` under action `a` with sojourn time `s`:
`G(i,a) + g(i,a) s`. -/
noncomputable def periodCost (i : S) (a : Act) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Ψ.G i a) + ENNReal.ofReal (Ψ.g i a) * ENNReal.ofReal s

variable {Ψ}

/-- `E_θ[C_n | X_0 = i]`, the total expected cost incurred under `θ` during the first `n`
transition periods (§10.3, p. 243). -/
noncomputable def expCostN (θ : Ψ.Policy) (n : ℕ) (i : S) : ℝ≥0∞ :=
  expectedSum θ Ψ.periodCost n 0 Fin.elim0 Fin.elim0 i

/-- `E_θ[T_n | X_0 = i]`, the total expected time taken up under `θ` by the first `n` transition
periods (§10.3, p. 243). -/
noncomputable def expTimeN (θ : Ψ.Policy) (n : ℕ) (i : S) : ℝ≥0∞ :=
  expectedSum θ (fun _ _ s => ENNReal.ofReal s) n 0 Fin.elim0 Fin.elim0 i

/-- The average cost of `θ` in `Ψ`, first line of (10.13), p. 243:
`J^Ψ_θ(i) = limsup_{n→∞} E_θ[C_n | X_0 = i] / E_θ[T_n | X_0 = i]`, in `[0, ∞]`. -/
noncomputable def avgCost (θ : Ψ.Policy) (i : S) : ℝ≥0∞ :=
  limsup (fun n : ℕ => expCostN θ n i / expTimeN θ n i) atTop

variable (Ψ)

/-- The minimum average cost `J^Ψ(i) = inf_θ J^Ψ_θ(i)`, second line of (10.13), p. 243. -/
noncomputable def avgValue (i : S) : ℝ≥0∞ :=
  ⨅ θ : Ψ.Policy, avgCost θ i

/-- The stationary policy `e` (with `e i ∈ A i`) as a policy for `Ψ`: in state `i` it chooses
`e i`, whatever the history. -/
noncomputable def ofStationary (e : S → Act) (he : ∀ i, e i ∈ Ψ.A i) : Ψ.Policy where
  σ _ _ _ i a := if a = e i then 1 else 0
  σ_sum _ _ _ i := by simp [he i]
  σ_supp _ _ _ i a ha := by
    have : a ≠ e i := fun h => ha (h ▸ he i)
    simp [this]
  σ_meas _ _ _ _ := measurable_const

/-- The auxiliary (discrete time) MDC `Δ` of (10.19), p. 245, built with the constant `τ`
(here `tau`) of Assumption (CTB): same states and actions, costs
`C(i,a) = G(i,a) ν(i,a) + g(i,a)`, and transition probabilities
`P*_{ij}(a) = τ ν(i,a) P_{ij}(a)` for `j ≠ i`, `P*_{ii}(a) = 1 - τ ν(i,a)`. -/
noncomputable def aux (tau : ℝ) : MDC S Act where
  A := Ψ.A
  C i a := Ψ.G i a * Ψ.ν i a + Ψ.g i a
  P i a j := if j = i then ENNReal.ofReal (1 - tau * Ψ.ν i a)
    else ENNReal.ofReal (tau * Ψ.ν i a) * Ψ.P i a j

/-- Assumption (CTAC), p. 246: `J^Δ(·) ≤ J^Ψ(·)`, where `J^Δ` is the minimum average cost in the
auxiliary MDC `Δ` built with the constant `τ`. -/
def CTAC (tau : ℝ) : Prop :=
  ∀ i, (Ψ.aux tau).avgValue i ≤ Ψ.avgValue i

/-- Inequality (10.15), p. 244, for the stationary policy `e`, the constant `Z` and the function
`z`: for every `i ∈ S`, the series `Σ_j P_{ij}(e) z(j)` converges and
`Z τ(i,e) + z(i) ≥ G(i,e) + g(i,e) τ(i,e) + Σ_j P_{ij}(e) z(j)`. -/
def Ineq1015 (e : S → Act) (Z : ℝ) (z : S → ℝ) : Prop :=
  ∀ i, Summable (fun j => (Ψ.P i (e i) j).toReal * z j) ∧
    Ψ.G i (e i) + Ψ.g i (e i) * Ψ.meanSojourn i (e i) +
        ∑' j, (Ψ.P i (e i) j).toReal * z j ≤
      Z * Ψ.meanSojourn i (e i) + z i

/-- Inequality (10.20), p. 246, in the auxiliary MDC `Δ` built with `τ`, for the stationary
policy `e`, the constant `Z` and the function `w`: for every `i ∈ S`, the series
`Σ_j P*_{ij}(e) w(j)` converges and `Z + w(i) ≥ C(i,e) + Σ_j P*_{ij}(e) w(j)`. -/
def Ineq1020 (tau : ℝ) (e : S → Act) (Z : ℝ) (w : S → ℝ) : Prop :=
  ∀ i, Summable (fun j => ((Ψ.aux tau).P i (e i) j).toReal * w j) ∧
    (Ψ.aux tau).C i (e i) + ∑' j, ((Ψ.aux tau).P i (e i) j).toReal * w j ≤ Z + w i

end CTMDC

end SennottDP.ContinuousTime


