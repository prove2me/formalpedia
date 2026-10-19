-- Prove2me | Definitions.Def_DelayDep_Equiv_Model
-- name    : DelayDep_Equiv_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:24.761756+00:00
-- url     : https://prove2.me/theorems/831789ec-4308-4d80-a202-cf74e7918679
-- title:
--   §2–§3, pp. 3347–3349 — n-server FCFS queue with abandonment: recursion (2), the state X = (Y, Q, U, V, B), exogenous and endogenous dependence, formula (1), Definition 1
-- statement:
--   This file sets up the model of Wu, Bassamboo and Perry (2022): an $n$-server, first-come-first-served service system in which waiting customers abandon once their wait exceeds their patience, with two ways in which service times can depend on delays.
--
--   **Queue mechanics.** Customers are numbered $i = 0, 1, 2, \dots$ (customer $i$ is the paper's customer $i+1$). The data of one sample path are the interarrival times $\alpha_i$ (with $\alpha_0$ the first arrival time), the residual service times $u \in \mathbb R^n_+$ of the jobs in service at time $0$ (the queue is empty at time $0$; $u_k = 0$ means server $k$ is idle), the patience times $T_i$, and the virtual service-time maps $z \mapsto S_i(z)$ (the service time customer $i$ requires if its offered wait is $z$). The arrival times are $\kappa_i = \alpha_0 + \dots + \alpha_i$. With $\mathcal R$ the operator sorting a vector of $\mathbb R^n$ increasingly, $e_1 = (1,0,\dots,0)$ and $\mathbf 1 = (1,\dots,1)$, the offered-wait vectors follow recursion (2):
--   $$Z_{i+1} = \mathcal R\Big(\big[Z_i + \mathbb I_{\{Z_i(1) \le T_i\}}\, S_i(Z_i(1))\, e_1 - \alpha_{i+1}\mathbf 1\big]^+\Big), \qquad Z_0 = \mathcal R\big([u - \alpha_0 \mathbf 1]^+\big).$$
--   The offered wait of customer $i$ is $Z_i(1)$, the smallest coordinate; the customer is served iff $Z_i(1) \le T_i$. At time $\tau \ge 0$, customer $i$ is in queue iff it has arrived and $\tau - \kappa_i < \min(T_i, Z_i(1))$, and in service iff it has arrived, is served and $\kappa_i + Z_i(1) \le \tau < \kappa_i + Z_i(1) + S_i(Z_i(1))$; an initial job $k$ is in service iff $\tau < u_k$.
--
--   **The state.** $X(\tau) = (Y(\tau), Q(\tau), U(\tau), V(\tau), B(\tau))$ where $Y$ and $Q$ are the numbers of customers in service and in queue; $U \in \mathbb R^n_+$ lists $n - Y$ zeros (idle servers) followed by the remaining service times in increasing order; $V \in \mathbb R^\infty_+$ lists the elapsed waiting times of the customers in queue in decreasing order, padded with zeros; and $B(\tau) = \kappa_{A(\tau)+1} - \tau$ is the forward recurrence time of the arrivals, $A(\tau)$ being the number of arrivals in $[0,\tau]$.
--
--   **Densities.** A pdf is a measurable nonnegative $g$ with $\int_0^\infty g = 1$; a joint pdf is a measurable nonnegative $f(x, y)$ (service $x$, patience $y$) with $\int_0^\infty\int_0^\infty f = 1$. The patience marginal and tail are $f^{ex}_T(y) = \int_0^\infty f(x,y)\,dx$ and $\bar F^{ex}_T(z) = \int_z^\infty f^{ex}_T(y)\,dy$, and formula (1) is
--   $$\psi^{en}(x,z) = \frac{\int_z^\infty f(x,y)\,dy}{\int_z^\infty f^{ex}_T(y)\,dy}.$$
--
--   **The two systems.** Both live on a probability space and share the inputs: measurable interarrival times $\alpha_i > 0$ whose partial sums tend to infinity on every path, and measurable initial residual service times $u \ge 0$ (jointly distributed in any way). In a system with **exogenous dependence** $f$, customer $i$ brings a pair $(S_i, T_i)$ with joint pdf $f$; the pairs are independent across customers and independent of the inputs; the service time does not depend on the wait. In a system with **endogenous dependence** $(f_T, \psi)$, customer $i$ has a patience $T_i$ with pdf $f_T$ and a virtual service-time process $z \mapsto S_i(z)$, jointly measurable in $(\omega, z)$, such that $S_i(z)$ has pdf $\psi(\cdot, z)$ at every $z \ge 0$ with $\int_z^\infty f_T > 0$; $T_i$ and $S_i$ are independent, the pairs $(T_i, S_i)$ are independent across customers and independent of the inputs.
--
--   **Equivalence (Definition 1).** $f$ is equivalent to $(f_T, \psi)$ if for every $n \ge 1$, every exogenous system with $f$ and every endogenous system with $(f_T,\psi)$, on any probability spaces, whose inputs have the same joint law, the laws of the processes $(X^{ex}(t))_{t\ge0}$ and $(X^{en}(t))_{t\ge0}$ coincide (both paths being almost-everywhere measurable).
--
--   These objects are what Theorem 1 and its proof are about; the coupling kernel of the proof is a separate file.
--
--   **Formalization Note** Customers are 0-based. Time is `NNReal`; the law of $X$ is the image measure on `NNReal → State n` with the product σ-algebra, which is the σ-algebra of the finite-dimensional distributions. Densities are `ℝ`-valued and enter measures through `ENNReal.ofReal` and `withDensity` on $[0,\infty)$ (or $[0,\infty)^2$). The paper's "any arrival process $A$ … whenever $X^{ex}(0) \overset{d}{=} X^{en}(0)$" becomes "any joint law of the interarrival sequence and the initial residual service times, the same in both systems". Added relative to the page: the queue is empty at time $0$ (the paper never specifies the primitives of customers already waiting); the law of $S_i(z)$ is prescribed only where the patience tail is positive (elsewhere the customer abandons a.s., and $\psi^{en}$ of (1) is a $0/0$); Assumption 1 (differentiability of $\Psi^{en}$) is not imposed, since Theorem 1 does not use it and the $\psi^{en}$ of (1) need not satisfy it. Ties follow (2) (served iff wait $\le$ patience); they are null events. The sorting operator duplicates `PalmQueueing.Loynes.order` of another (unpublished) mission.
-- source:
--   Wu, Bassamboo & Perry, When service times depend on customers’ delays, Operations Research 70(6) (2022), pp. 3347–3349 (PDF 4–6), §2, §2.1, §2.2, §3, Definition 1 (typeset "Remark 1"), (1), (2)

import Mathlib

namespace DelayDep.Equiv

open MeasureTheory ProbabilityTheory Filter
open scoped Classical

/-! ### Queue mechanics (deterministic, §2.2 and recursion (2), pp. 3347–3349) -/

/-- The sorting operator `R : ℝⁿ → ℝⁿ` of p. 3348: `R(x) = (x_(1), …, x_(n))`, the components of
`x` in increasing order. -/
noncomputable def sortR {n : ℕ} (v : Fin n → ℝ) : Fin n → ℝ := v ∘ Tuple.sort v

/-- The unit vector `e₁ = (1, 0, …, 0)`; coordinate `0 : Fin n` is the paper's first coordinate. -/
noncomputable def e1 {n : ℕ} [NeZero n] : Fin n → ℝ := fun k => if k = 0 then 1 else 0

/-- Arrival time of customer `i` (0-based): `κ_i = α_0 + ⋯ + α_i`, where `α i` is the time between
the arrivals of customers `i - 1` and `i` (`α 0` is the first arrival time). -/
def kappa (α : ℕ → ℝ) (i : ℕ) : ℝ := ∑ j ∈ Finset.range (i + 1), α j

/-- The auxiliary offered-wait vectors `Z_i` of recursion (2), p. 3349, for interarrival times `α`,
initial residual service times `u` (empty queue at time 0), patience times `tp` and virtual
service-time maps `sv` (`sv i z` is the service time customer `i` requires if its offered wait is
`z`):
`Z_{i+1} = R([Z_i + 1{Z_i(1) ≤ T_i} S_i(Z_i(1)) e₁ − α_{i+1} 1]⁺)`, with
`Z_0 = R([u − α_0 1]⁺)`. -/
noncomputable def Zvec {n : ℕ} [NeZero n] (α : ℕ → ℝ) (u : Fin n → ℝ) (tp : ℕ → ℝ)
    (sv : ℕ → ℝ → ℝ) : ℕ → Fin n → ℝ
  | 0 => sortR (fun k => max (u k - α 0) 0)
  | i + 1 =>
      sortR (fun k => max (Zvec α u tp sv i k
        + (if Zvec α u tp sv i 0 ≤ tp i then sv i (Zvec α u tp sv i 0) else 0) * e1 k
        - α (i + 1)) 0)

/-- The offered wait of customer `i`: `Z_i(1)`, the smallest coordinate of `Z_i`. -/
noncomputable def wait {n : ℕ} [NeZero n] (α : ℕ → ℝ) (u : Fin n → ℝ) (tp : ℕ → ℝ)
    (sv : ℕ → ℝ → ℝ) (i : ℕ) : ℝ := Zvec α u tp sv i 0

/-- Customer `i` is served iff its offered wait does not exceed its patience (the convention of
(2)). -/
def served {n : ℕ} [NeZero n] (α : ℕ → ℝ) (u : Fin n → ℝ) (tp : ℕ → ℝ) (sv : ℕ → ℝ → ℝ)
    (i : ℕ) : Prop := wait α u tp sv i ≤ tp i

/-- The state space of `X(t) = (Y(t), Q(t), U(t), V(t), B(t))`: number in service, number in
queue, sorted remaining service times (`ℝⁿ`), sorted elapsed waiting times (`ℝ^∞`), forward
recurrence time of the arrival process. -/
abbrev State (n : ℕ) := ℕ × ℕ × (Fin n → ℝ) × (ℕ → ℝ) × ℝ

/-- `A(τ)`: the number of arrivals in `[0, τ]` (the index of the next customer to arrive). -/
noncomputable def nextArr (α : ℕ → ℝ) (τ : ℝ) : ℕ := sInf {i | τ < kappa α i}

/-- Customer `i` is in queue at time `τ`: it has arrived and
`τ − κ_i < min(T_i, Z_i(1))` (p. 3349). -/
def inQueue {n : ℕ} [NeZero n] (α : ℕ → ℝ) (u : Fin n → ℝ) (tp : ℕ → ℝ) (sv : ℕ → ℝ → ℝ)
    (τ : ℝ) (i : ℕ) : Prop :=
  i < nextArr α τ ∧ τ - kappa α i < min (tp i) (wait α u tp sv i)

/-- Customer `i` is in service at time `τ`: it has arrived, is served, and
`κ_i + Z_i(1) ≤ τ < κ_i + Z_i(1) + S_i(Z_i(1))`. -/
def inService {n : ℕ} [NeZero n] (α : ℕ → ℝ) (u : Fin n → ℝ) (tp : ℕ → ℝ) (sv : ℕ → ℝ → ℝ)
    (τ : ℝ) (i : ℕ) : Prop :=
  i < nextArr α τ ∧ served α u tp sv i ∧
    kappa α i + wait α u tp sv i ≤ τ ∧
    τ < kappa α i + wait α u tp sv i + sv i (wait α u tp sv i)

/-- The remaining service times at time `τ` of all jobs in service: the initial jobs (`τ < u k`,
remaining `u k − τ`) followed by the customers in service. -/
noncomputable def remainingList {n : ℕ} [NeZero n] (α : ℕ → ℝ) (u : Fin n → ℝ) (tp : ℕ → ℝ)
    (sv : ℕ → ℝ → ℝ) (τ : ℝ) : List ℝ :=
  ((List.ofFn u).filter (fun r => decide (τ < r))).map (fun r => r - τ) ++
    ((List.range (nextArr α τ)).filter (fun i => decide (inService α u tp sv τ i))).map
      (fun i => kappa α i + wait α u tp sv i + sv i (wait α u tp sv i) - τ)

/-- The elapsed waiting times at time `τ` of the customers in queue, in increasing order of
arrival (that is, in decreasing order of elapsed wait). -/
noncomputable def waitingList {n : ℕ} [NeZero n] (α : ℕ → ℝ) (u : Fin n → ℝ) (tp : ℕ → ℝ)
    (sv : ℕ → ℝ → ℝ) (τ : ℝ) : List ℝ :=
  ((List.range (nextArr α τ)).filter (fun i => decide (inQueue α u tp sv τ i))).map
    (fun i => τ - kappa α i)

/-- The state `X(τ) = (Y(τ), Q(τ), U(τ), V(τ), B(τ))` of §2.2, pp. 3347–3348:
* `Y` the number of customers in service;
* `Q` the number of customers in queue;
* `U ∈ ℝⁿ₊`: first `n − Y` zeros (idle servers), then the remaining service times in increasing
  order;
* `V ∈ ℝ^∞₊`: the elapsed waiting times in decreasing order, padded with zeros;
* `B = κ_{A(τ)+1} − τ`, the forward recurrence time of the arrivals. -/
noncomputable def pathX {n : ℕ} [NeZero n] (α : ℕ → ℝ) (u : Fin n → ℝ) (tp : ℕ → ℝ)
    (sv : ℕ → ℝ → ℝ) (τ : NNReal) : State n :=
  let L := remainingList α u tp sv τ
  let W := waitingList α u tp sv τ
  (L.length, W.length,
    (fun j : Fin n => (List.replicate (n - L.length) 0 ++ L.mergeSort (fun a b => decide (a ≤ b))).getD j 0),
    (fun j : ℕ => W.getD j 0),
    kappa α (nextArr α τ) - τ)

/-! ### Densities, the marginal `f^ex_T` and formula (1) -/

/-- `g` is a probability density on `[0, ∞)`. -/
def IsPdf (g : ℝ → ℝ) : Prop :=
  Measurable g ∧ (∀ x, 0 ≤ g x) ∧ ∫⁻ x in Set.Ici (0 : ℝ), ENNReal.ofReal (g x) = 1

/-- `f` is a joint probability density on `ℝ²₊`, with `f x y` the density at service time `x` and
patience time `y`. -/
def IsJointPdf (f : ℝ → ℝ → ℝ) : Prop :=
  Measurable (Function.uncurry f) ∧ (∀ x y, 0 ≤ f x y) ∧
    ∫⁻ p in Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ), ENNReal.ofReal (f p.1 p.2) = 1

/-- The law on `ℝ` with density `g` on `[0, ∞)`. -/
noncomputable def pdfLaw (g : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ici (0 : ℝ))).withDensity (fun x => ENNReal.ofReal (g x))

/-- The law on `ℝ × ℝ` with density `f` on `ℝ²₊`. -/
noncomputable def jointLaw (f : ℝ → ℝ → ℝ) : Measure (ℝ × ℝ) :=
  (volume.restrict (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ))).withDensity
    (fun p => ENNReal.ofReal (f p.1 p.2))

/-- The patience marginal `f^ex_T(y) = ∫₀^∞ f^ex(x, y) dx`. -/
noncomputable def fTex (f : ℝ → ℝ → ℝ) (y : ℝ) : ℝ := ∫ x in Set.Ici (0 : ℝ), f x y

/-- The patience tail `F̄^ex_T(z) = ∫_z^∞ f^ex_T(y) dy`. -/
noncomputable def tailT (f : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := ∫ y in Set.Ioi z, fTex f y

/-- Formula (1): `ψ^en(x, z) = ∫_z^∞ f^ex(x, y) dy / ∫_z^∞ f^ex_T(y) dy`. (Lean's `· / 0 = 0` makes
it `0` where the patience tail vanishes.) -/
noncomputable def psiEn (f : ℝ → ℝ → ℝ) (x z : ℝ) : ℝ :=
  (∫ y in Set.Ioi z, f x y) / tailT f z

/-! ### The two systems (§2.1) -/

/-- The arrival process and the initial state, common to both systems: measurable positive
interarrival times `α i` (customer `i` is the paper's customer `i + 1`) whose partial sums
`κ_i` tend to infinity on every sample path, and nonnegative initial residual service times
`u k` of the `n` servers (empty queue at time 0; `u k = 0` is an idle server). -/
structure Inputs (n : ℕ) (Ω : Type) [MeasurableSpace Ω] where
  α : ℕ → Ω → ℝ
  u : Ω → Fin n → ℝ
  measurable_α : ∀ i, Measurable (α i)
  measurable_u : Measurable u
  α_pos : ∀ i ω, 0 < α i ω
  kappa_tendsto : ∀ ω, Tendsto (fun i => kappa (fun j => α j ω) i) atTop atTop
  u_nonneg : ∀ ω k, 0 ≤ u ω k

/-- The joint law of the interarrival sequence and the initial residual service times. -/
noncomputable def Inputs.inputLaw {n : ℕ} {Ω : Type} [MeasurableSpace Ω] (I : Inputs n Ω)
    (P : Measure Ω) : Measure ((ℕ → ℝ) × (Fin n → ℝ)) :=
  P.map (fun ω => ((fun i => I.α i ω), I.u ω))

/-- A system with **exogenous dependence** (§2.1, p. 3347): customer `i` brings a service time
`S i` and a patience time `T i`; the pairs `(S i, T i)` have joint pdf `f`, are independent across
customers, and are independent of the arrivals and the initial state. -/
structure ExoSystem (n : ℕ) (f : ℝ → ℝ → ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    extends Inputs n Ω where
  S : ℕ → Ω → ℝ
  T : ℕ → Ω → ℝ
  measurable_S : ∀ i, Measurable (S i)
  measurable_T : ∀ i, Measurable (T i)
  law_ST : ∀ i, P.map (fun ω => (S i ω, T i ω)) = jointLaw f
  indep_customers : iIndepFun (fun i ω => (S i ω, T i ω)) P
  indep_inputs : IndepFun (fun ω => ((fun i => α i ω), u ω)) (fun ω i => (S i ω, T i ω)) P

/-- A system with **endogenous dependence** (§2.1, p. 3347): customer `i` has patience `T i` with
pdf `fT` and a virtual service-time process `z ↦ S i ω z`, whose value at offered wait `z` has pdf
`ψ(·, z)` (required where the patience tail `∫_z^∞ fT` is positive); `T i` and `S i` are
independent, the pairs are independent across customers and independent of the arrivals and the
initial state. -/
structure EndoSystem (n : ℕ) (fT : ℝ → ℝ) (ψ : ℝ → ℝ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) extends Inputs n Ω where
  T : ℕ → Ω → ℝ
  S : ℕ → Ω → ℝ → ℝ
  measurable_T : ∀ i, Measurable (T i)
  measurable_S : ∀ i, Measurable (fun p : Ω × ℝ => S i p.1 p.2)
  law_T : ∀ i, P.map (T i) = pdfLaw fT
  law_S : ∀ i z, 0 ≤ z → 0 < ∫ y in Set.Ioi z, fT y →
    P.map (fun ω => S i ω z) = pdfLaw (fun x => ψ x z)
  indep_customers : iIndepFun (fun i ω => (T i ω, S i ω)) P
  indep_TS : ∀ i, IndepFun (T i) (S i) P
  indep_inputs : IndepFun (fun ω => ((fun i => α i ω), u ω)) (fun ω i => (T i ω, S i ω)) P

/-- The sample path `t ↦ X^ex(t)` of an exogenous system (service time constant in the wait). -/
noncomputable def ExoSystem.path {n : ℕ} [NeZero n] {f : ℝ → ℝ → ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} (E : ExoSystem n f P) : Ω → NNReal → State n :=
  fun ω => pathX (fun i => E.α i ω) (E.u ω) (fun i => E.T i ω) (fun i _ => E.S i ω)

/-- The sample path `t ↦ X^en(t)` of an endogenous system. -/
noncomputable def EndoSystem.path {n : ℕ} [NeZero n] {fT : ℝ → ℝ} {ψ : ℝ → ℝ → ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} (N : EndoSystem n fT ψ P) : Ω → NNReal → State n :=
  fun ω => pathX (fun i => N.α i ω) (N.u ω) (fun i => N.T i ω) (fun i => N.S i ω)

/-- Definition 1 (typeset "Remark 1"), p. 3348: the exogenous dependence `f` is **equivalent** to
the endogenous dependence `(fT, ψ)` if, for every number of servers `n ≥ 1`, every exogenous system
and every endogenous system (on any probability spaces) whose arrival sequences and initial states
have the same joint law, the laws of the processes `X^ex` and `X^en` coincide. -/
def IsEquivalent (f : ℝ → ℝ → ℝ) (fT : ℝ → ℝ) (ψ : ℝ → ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) [NeZero n] (Ω Ω' : Type) [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (E : ExoSystem n f P) (N : EndoSystem n fT ψ P'),
    E.inputLaw P = N.inputLaw P' →
      AEMeasurable E.path P ∧ AEMeasurable N.path P' ∧ P.map E.path = P'.map N.path

end DelayDep.Equiv


