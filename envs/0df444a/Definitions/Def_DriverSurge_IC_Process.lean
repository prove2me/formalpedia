-- Prove2me | Definitions.Def_DriverSurge_IC_Process
-- name    : DriverSurge_IC_Process
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:21.955648+00:00
-- url     : https://prove2.me/theorems/f28333f0-e91b-4abc-a0eb-b9b020b779ba
-- title:
--   §2.1–2.2, pp. 5–6 — the stochastic two-state driver model: world CTMC, thinned Poisson requests, accepted trips, earnings R(w, σ, t) and earnings rate liminf R(w, σ, t)/t
-- statement:
--   The stochastic dynamic model of Garg and Nazerzadeh (§2.1.1–§2.2, pp. 5–6), built pathwise from three independent families of random variables.
--
--   1. **The world.** It starts in a state $i_0$ and spends its $k$-th sojourn in state $i_0$ ($k$ even) or in the other state ($k$ odd). The sojourn lengths $H_0,H_1,\dots$ are independent and exponential with the switching rate $\lambda_{i\to j}$ of the current state, so the world is the two-state continuous-time Markov chain of §2.1.2. `worldState` is the state at time $t\ge0$.
--   2. **Requests.** For each state $i$, $E_{i,0},E_{i,1},\dots$ are i.i.d. exponential with rate $\lambda_i$ (a Poisson stream of rate $\lambda_i$, with arrival times $E_{i,0}+\dots+E_{i,k}$), and $L_{i,0},L_{i,1},\dots$ are i.i.d. with law $F_i$, the trip lengths carried by these requests. A request of stream $i$ reaches the driver exactly when the world is in state $i$ at its arrival; by memorylessness, a driver who is open in state $i$ therefore receives requests at rate $\lambda_i$ with lengths $\tau\sim F_i$.
--   3. **The driver.** The driver is open at time $0$ and follows a policy $\sigma=\{\sigma_1,\sigma_2\}$: the next trip is the earliest request, arriving while the driver is open, that reaches the driver in a state $i$ and whose length lies in $\sigma_i$. The trip occupies $[\text{start},\text{start}+\tau)$, after which the driver is open again; requests arriving during a trip are lost.
--   4. **Earnings.** A trip started in state $i$ with length $\tau$ pays $w_i(\tau)$, whatever the world does during the trip. $R(w,\sigma,t)$ is the total pay of the trips accepted in $[0,t]$, and the driver's **lifetime earnings rate** is
--   $$R(w,\sigma)=\liminf_{t\to\infty}\frac{R(w,\sigma,t)}{t}.$$
--   5. **Occupation.** The time in $[0,t]$ the driver spends either open while the world is in state $i$, or on a trip started in state $i$ (Lemma 3).
--
--   `IsDriverModel P μ i₀ X` says that the random path $X$ on $(\Omega,\mu)$ has exactly these laws, with all coordinates independent.
--
--   This is the object of the mission's goal: incentive compatibility is a statement about this stochastic earnings rate, and Lemmas 1 and 3 reduce it to the closed form.
--
--   **Formalization Note** The liminf is taken in `EReal`, so it is the true lower limit even when $R(w,\sigma,t)/t$ is unbounded. On null events (infinitely many state changes or requests in bounded time, ties between arrival times) the pathwise definitions take arbitrary junk values (`Nat.card` of an infinite set is $0$, `tsum` of a non-summable family is $0$, `nextTrip` returns `none` when no earliest eligible request exists); every statement about the model is almost sure. Lean state `0` is the paper's state 1.
-- source:
--   Garg, Nazerzadeh, Driver Surge Pricing, arXiv:1905.07544v4, pp. 5–6, §2.1.1, §2.1.2, §2.2; p. 12, Lemma 3

import Mathlib
import Definitions.Def_DriverSurge_IC_Model

namespace DriverSurge.IC

open MeasureTheory Set Filter ProbabilityTheory

/-! Garg–Nazerzadeh, *Driver Surge Pricing* (arXiv:1905.07544v4), §2.1.1–§2.2 (pp. 5–7): the
stochastic dynamic model, its driver process, the total earnings `R(w, σ, t)` and the lifetime
earnings rate `R(w, σ) = liminf_{t→∞} R(w, σ, t)/t`.

The model is built from three independent families of random variables:
* `H k`, the length of the `k`-th sojourn of the world (the world starts in state `i₀`, sojourn `k` is
  spent in state `i₀` for even `k` and in the other state for odd `k`, and lasts an exponential time
  with rate `λ_{i→j}` of its state: "a fixed exponential clock that ticks at rate `λ_{i→j}`");
* `E i k`, the `k`-th inter-arrival time of a Poisson stream of rate `λ_i` (request stream `i`);
* `L i k`, the trip length carried by the `k`-th request of stream `i`, with law `F_i`.
A request of stream `i` reaches the driver iff the world is in state `i` when it arrives (thinning);
by memorylessness, while the world is in state `i` the driver who is open receives requests at rate
`λ_i` with lengths `∼ F_i`, as in §2.1.2. State labels: Lean `0` is the paper's state 1, Lean `1` is
state 2. -/

/-- One realization of the model's driving randomness. -/
structure Path where
  /-- `H k`: the length of the world's `k`-th sojourn. -/
  H : ℕ → ℝ
  /-- `E i k`: the `k`-th inter-arrival time of request stream `i`. -/
  E : Fin 2 → ℕ → ℝ
  /-- `L i k`: the trip length of the `k`-th request of stream `i`. -/
  L : Fin 2 → ℕ → ℝ

/-- Index set of the coordinates of a `Path`. -/
inductive Coord
  | hold (k : ℕ)
  | gap (i : Fin 2) (k : ℕ)
  | len (i : Fin 2) (k : ℕ)

/-- The coordinate of a path with index `c`. -/
def Path.coord (x : Path) : Coord → ℝ
  | .hold k => x.H k
  | .gap i k => x.E i k
  | .len i k => x.L i k

/-- The state of the world during its `k`-th sojourn when it starts in `i₀`. -/
def stateAt (i₀ : Fin 2) (k : ℕ) : Fin 2 := if Even k then i₀ else other i₀

/-- The time of the `n`-th change of the world state: `H 0 + ⋯ + H (n-1)`. -/
noncomputable def jumpTime (x : Path) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, x.H k

/-- The world state at time `t ≥ 0`: `stateAt i₀ n` with `n` the number of state changes in
`(0, t]`. (On the null event that infinitely many changes occur by time `t`, the count is the junk
value `0`.) -/
noncomputable def worldState (i₀ : Fin 2) (x : Path) (t : ℝ) : Fin 2 :=
  stateAt i₀ (Nat.card {n : ℕ // 0 < n ∧ jumpTime x n ≤ t})

/-- The arrival time of the `k`-th request of stream `i`: `E i 0 + ⋯ + E i k`. -/
noncomputable def arrival (x : Path) (i : Fin 2) (k : ℕ) : ℝ := ∑ m ∈ Finset.range (k + 1), x.E i m

/-- The requests the driver would accept if open from time `b` on: request `(i, k)` arrives at or after
`b`, the world is in state `i` at its arrival (so it reaches the driver), and its length lies in
`σ i`. -/
def eligible (i₀ : Fin 2) (x : Path) (σ : Fin 2 → Set ℝ) (b : ℝ) : Set (Fin 2 × ℕ) :=
  {p | b ≤ arrival x p.1 p.2 ∧ worldState i₀ x (arrival x p.1 p.2) = p.1 ∧ x.L p.1 p.2 ∈ σ p.1}

/-- The first request the driver accepts when open from time `b` on: the eligible request with the
earliest arrival time, or `none` if there is none (or no earliest one, a null event). -/
noncomputable def nextTrip (i₀ : Fin 2) (x : Path) (σ : Fin 2 → Set ℝ) (b : ℝ) :
    Option (Fin 2 × ℕ) :=
  haveI := Classical.propDecidable
  if h : ∃ p ∈ eligible i₀ x σ b, ∀ p' ∈ eligible i₀ x σ b, arrival x p.1 p.2 ≤ arrival x p'.1 p'.2
  then some (Classical.choose h) else none

/-- The accepted trips of a driver following policy `σ`, in order: the driver is open at time `0`;
trip `n + 1` is the first request accepted after trip `n` ends (at its start time plus its length).
A trip is a request `(i, k)`: it starts in state `i` at time `arrival x i k` and has length `L i k`. -/
noncomputable def trip (i₀ : Fin 2) (x : Path) (σ : Fin 2 → Set ℝ) : ℕ → Option (Fin 2 × ℕ)
  | 0 => nextTrip i₀ x σ 0
  | n + 1 =>
    match trip i₀ x σ n with
    | none => none
    | some p => nextTrip i₀ x σ (arrival x p.1 p.2 + x.L p.1 p.2)

/-- `R(w, σ, t)` (§2.2, p. 6): the total earnings from jobs accepted from time `0` up to time `t`. A
trip started in state `i` with length `τ` pays `w i τ` (payment by the state at the trip's start,
§2.1.2). The sum is finite except on a null event (where `tsum` takes the junk value `0`). -/
noncomputable def earnings (w : Fin 2 → ℝ → ℝ) (σ : Fin 2 → Set ℝ) (i₀ : Fin 2) (x : Path)
    (t : ℝ) : ℝ :=
  haveI := Classical.propDecidable
  ∑' n : ℕ,
    match trip i₀ x σ n with
    | none => 0
    | some p => if arrival x p.1 p.2 ≤ t then w p.1 (x.L p.1 p.2) else 0

/-- The driver's lifetime earnings rate (§2.2, p. 6): `R(w, σ) = liminf_{t→∞} R(w, σ, t)/t`, taken in
`EReal` so that it is the true lower limit even when `R(w, σ, t)/t` is unbounded. -/
noncomputable def earningsRate (w : Fin 2 → ℝ → ℝ) (σ : Fin 2 → Set ℝ) (i₀ : Fin 2) (x : Path) :
    EReal :=
  liminf (fun t : ℝ => ((earnings w σ i₀ x t / t : ℝ) : EReal)) atTop

/-- The driver is on a trip started in state `i` at time `s`. -/
def onTripAt (i₀ : Fin 2) (x : Path) (σ : Fin 2 → Set ℝ) (i : Fin 2) (s : ℝ) : Prop :=
  ∃ n p, trip i₀ x σ n = some p ∧ p.1 = i ∧ arrival x p.1 p.2 ≤ s ∧ s < arrival x p.1 p.2 + x.L p.1 p.2

/-- Lemma 3 (p. 12): the time in `[0, t]` the driver spends either open in state `i` or on a trip
started in state `i`. -/
noncomputable def occupation (i₀ : Fin 2) (x : Path) (σ : Fin 2 → Set ℝ) (i : Fin 2) (t : ℝ) : ℝ :=
  (volume {s ∈ Icc 0 t | ((¬ ∃ k, onTripAt i₀ x σ k s) ∧ worldState i₀ x s = i) ∨
    onTripAt i₀ x σ i s}).toReal

/-- `X : Ω → Path` on the probability space `(Ω, μ)` is the paper's dynamic model with primitives `P`
and initial world state `i₀`: all coordinates are measurable and mutually independent, the sojourn
`H k` is exponential with the switching rate of its state, the inter-arrival times of stream `i` are
exponential with rate `λ_i`, and the trip lengths of stream `i` have law `F_i`. -/
structure IsDriverModel (P : Primitives) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (i₀ : Fin 2) (X : Ω → Path) : Prop where
  isProb : IsProbabilityMeasure μ
  measurable : ∀ c : Coord, Measurable (fun ω => (X ω).coord c)
  indep : iIndepFun (fun (c : Coord) (ω : Ω) => (X ω).coord c) μ
  law_H : ∀ k, μ.map (fun ω => (X ω).H k) = expMeasure (P.sw (stateAt i₀ k))
  law_E : ∀ i k, μ.map (fun ω => (X ω).E i k) = expMeasure (P.lam i)
  law_L : ∀ i k, μ.map (fun ω => (X ω).L i k) = P.F i

end DriverSurge.IC


