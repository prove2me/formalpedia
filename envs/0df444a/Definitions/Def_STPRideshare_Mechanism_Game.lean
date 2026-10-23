-- Prove2me | Definitions.Def_STPRideshare_Mechanism_Game
-- name    : STPRideshare_Mechanism_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:25.833708+00:00
-- url     : https://prove2.me/theorems/8bdec297-1c97-48c7-b560-c1f996550699
-- title:
--   §4.1, pp. 17–20 — the dynamic ridesharing game: driver states and actions, histories, dynamic mechanisms, the time-shifted economy E^(t)(s_t), and Definitions 6–11
-- statement:
--   This file defines the finite-horizon extensive-form game that a dynamic ridesharing mechanism induces (Section 4.1), and the properties of Theorem 2.
--
--   **States and actions.** At time $t$ a driver is *waiting* in state $(\beta,a,\tau)$ (not yet able to act if $\tau>t$, *available* at $(a,t)$ if $\tau=t$), *en route* on a trip $(a,b,t')$ or $(a,b,t',j)$, or *gone* ($\varphi$, exited or never entered). An available driver may relocate to $b$ (trip $(a,b,t)$ with $t+\delta(a,b)\le T$), pick up rider $j$ (trip $(a,d_j,t,j)$), or exit / not enter; any other driver has the single action of continuing. A trip that ends at $t+1$ makes the driver available at its destination at $t+1$.
--
--   **Mechanisms.** A dynamic mechanism (Definition 5) is given for every economy and consists of a dispatch rule $\alpha^*_{i,t}(h_t)$, a driver payment rule $r^*_{i,t}(h_t)$ and a rider payment rule $q^*_j(h_t)$, as functions of the history $h_t=(s_0,\alpha_0,\dots,\alpha_{t-1},s_t)$. An available driver's action set is
--   $$A_{i,t}(h_t)=\{\alpha^*_{i,t}(h_t)\}\cup\{(a,b,t): t+\delta(a,b)\le T\}\cup\{\varphi\}.$$
--   The driver is paid $\hat r_{i,t}=r^*_{i,t}(h_t)\,\mathbf 1\{\alpha_{i,t}=\alpha^*_{i,t}(h_t)\}$, and rider $j$ pays $\hat q_j=q^*_j(h_{\tau_j})\sum_{i\in\mathcal D_{\tau_j}}\mathbf 1\{\alpha_{i,\tau_j}=(o_j,d_j,\tau_j,j)\}$. A driver's per-period utility $\hat\pi_{i,t}$ is her payment minus $c_{a,b,t}$ on a trip, minus $\kappa_{T-t}$ when she exits from state $(1,a,t)$.
--
--   **Time-shifted economy.** $E^{(t)}(s_t)$ has horizon $T-t$, the same locations and travel times, the riders with $\tau_j\ge t$ (request time $\tau_j-t$), and one driver for each driver not gone: an available driver in state $(\beta,a,t)$ becomes $(\beta,a,0)$, an en-route driver on $(a,b,t')$ becomes $(1,b,t'+\delta(a,b)-t)$, a future driver $(\beta_i,\ell_i,\tau_i)$ becomes $(\beta_i,\ell_i,\tau_i-t)$.
--
--   **Properties.** For every valid economy:
--   1. *strict budget balance*: $\sum_j\hat q_j(\sigma)=\sum_i\hat r_i(\sigma)$ for every admissible strategy profile (Definition 6 with equality);
--   2. *rider IR* (24): $\hat x_j(\sigma)v_j\ge\hat q_j(\sigma)$ for every admissible profile;
--   3. *SPIC* (23): from every reachable history $h_t$, $t\le T-1$, no driver gains by any admissible strategy against $\sigma^*_{-i}$;
--   4. *driver IR from any history*: under $\sigma^*$ every driver who has not entered gets non-negative continuation utility;
--   5. *envy-freeness* (25), (26): equal continuation utility for drivers in the same state; no rider envies another with the same trip, from every $h_{\tau_j}$;
--   6. *core-selecting*, *welfare-optimal from any history*: the $\sigma^*$ outcome from every $h_t$, read as a plan of $E^{(t)}(s_t)$, is in the core, resp. welfare-optimal;
--   7. *temporal consistency* (Definition 11): after a deviation at $t-1$, the updated plan equals the mechanism's own time-0 plan of the economy $E^{(t)}(s_t)$.
--
--   **Formalization Note.** Histories are lists of action profiles (most recent first); states are computed from them. "Reachable" histories are those in which every driver always took an available action. Definitions 8–10 bundle SPIC as their condition (i); the properties here hold only condition (ii), and SPIC is its own property. Definition 8 (ii) is read "from any history onward", as Theorem 2 states it. (24) prints "$\forall i\in\mathcal R$" for "$\forall j\in\mathcal R$". (26) is read for the $\sigma^*$ outcome continuing from $h_{\tau_j}$. **Corrected printed slip, p. 20:** the page gives the type $(1,a,0,\bar\tau_i-t)$ to an available driver in state $(0,a,t)$; here she keeps $\beta=0$, so she keeps the zero-cost option not to enter, as the proof of Theorem 2 uses ("$\max\{\Phi^{(t')}_{a,t}(s_{t'}),0\}$", p. 54). Trip costs of $E^{(t)}$ are read at the original time.
-- source:
--   Ma, Fang, Parkes, Spatio-Temporal Pricing for Ridesharing Platforms, arXiv:1801.04015v5, pp. 17–20, Definitions 5–11, (22)–(26)

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_Model

namespace STPRideshare.Mechanism

open scoped Classical

noncomputable section

/-- §4.1, p. 17: the state `s_{i,t}` of a driver. `wait β a τ` is a driver who has not yet
become available (`τ > t`, the paper's `(β_i, ℓ_i, τ_i)`) or who is available now (`τ = t`, the
paper's `(1, a, t)` or `(0, a, t)`); `enroute a b t′ j` is a driver finishing the trip `(a, b, t′)`
without a rider (`j = none`) or with rider `j`; `gone` (the paper's `φ`) is a driver who has
exited or decided not to enter. -/
inductive DState (L κ : Type)
  | wait (β : Bool) (a : L) (τ : ℕ)
  | enroute (a b : L) (t' : ℕ) (j : Option κ)
  | gone

/-- §4.1, p. 17: actions of a driver. An available driver at `(a, t)` may relocate (`move b`,
the trip `(a, b, t)`), pick up rider `j` (`pick j`, the trip `(a, d_j, t, j)`), or exit / not enter
(`quit`, the paper's `φ`); every other driver has the single action `cont` (continue the current
trip, wait, or stay out). -/
inductive DAction (L κ : Type)
  | move (b : L)
  | pick (j : κ)
  | quit
  | cont

/-- p. 18: a history `h_t`, recorded as the list of action profiles `α_{t−1}, …, α_0`, most recent
first (the states `s_0, …, s_t` are determined by the initial state and the actions); its length
is the current time `t`. -/
abbrev Hist (L ι κ : Type) := List (ι → DAction L κ)

variable {L ι κ : Type}

/-- A driver in state `s` is available at time `t`: `s = (β, a, t)`. -/
def IsAvailAt (t : ℕ) : DState L κ → Prop
  | .wait _ _ τ => τ = t
  | _ => False

/-- The state at `t + 1` of a driver starting the trip `(a, b, t)` (with rider tag `j`): available
at `(b, t + 1)` if the trip ends at `t + 1`, en route otherwise. -/
def arrive (P : Params L) (t : ℕ) (a b : L) (j : Option κ) : DState L κ :=
  if t + P.δ a b ≤ t + 1 then .wait true b (t + 1) else .enroute a b t j

/-- pp. 17–18: the transition `s_{i,t+1}` from the state `s_{i,t}` and the action `α_{i,t}`. -/
def step (P : Params L) (R : κ → Rider L) (t : ℕ) : DState L κ → DAction L κ → DState L κ
  | .wait β a τ, α =>
      if τ = t then
        (match α with
         | .move b => arrive P t a b none
         | .pick j => arrive P t a (R j).d (some j)
         | .quit => .gone
         | .cont => .gone)
      else .wait β a τ
  | .enroute a b t' j, _ =>
      if t' + P.δ a b ≤ t + 1 then .wait true b (t + 1) else .enroute a b t' j
  | .gone, _ => .gone

/-- p. 17: the state profile `s_t` after history `h_t`, from `s_0 = ((β_i, ℓ_i, τ_i))_i`. -/
def stateAt (e : Econ L ι κ) : Hist L ι κ → ι → DState L κ
  | [] => fun i => .wait (e.D i).β (e.D i).ℓ (e.D i).τ
  | α :: h => fun i => step e.P e.R h.length (stateAt e h i) (α i)

/-- p. 20: the type `θ^{(t)}_i` in the time-shifted economy `E^{(t)}(s_t)` of a driver in state
`s ≠ φ`: `(β, a, τ − t)` for `s = (β, a, τ)` (available drivers keep their `β`: the page prints
`(1, a, 0)` for both `(1, a, t)` and `(0, a, t)`, corrected here to `(0, a, 0)` for the latter),
and `(1, b, t′ + δ(a, b) − t)` for an en-route driver on `(a, b, t′)`. -/
def shiftType (P : Params L) (t : ℕ) : (s : DState L κ) → s ≠ .gone → DType L
  | .wait β a τ, _ => ⟨β, a, τ - t⟩
  | .enroute a b t' _, _ => ⟨true, b, t' + P.δ a b - t⟩
  | .gone, hs => absurd rfl hs

/-- p. 20: parameters of `E^{(t)}`: horizon `T − t`, the same `δ` and `κ`, and trip costs read
at the original time (`c^{(t)}_{a,b,u} = c_{a,b,u+t}`). -/
def shiftParams (P : Params L) (t : ℕ) : Params L :=
  ⟨P.T - t, P.δ, fun a b u => P.c a b (u + t), P.κ⟩

/-- p. 20: the time-shifted economy `E^{(t)}(s)` starting at time `t` in state profile `s`:
drivers who have not exited (types `shiftType`), and the riders with `τ_j ≥ t`, with request
times `τ_j − t`. -/
def econAt (e : Econ L ι κ) (t : ℕ) (s : ι → DState L κ) :
    Econ L {i : ι // s i ≠ .gone} {j : κ // t ≤ (e.R j).τ} :=
  ⟨shiftParams e.P t, fun i => shiftType e.P t (s i.1) i.2,
    fun j => ⟨(e.R j.1).o, (e.R j.1).d, (e.R j.1).τ - t, (e.R j.1).v⟩⟩

/-- p. 20: `E^{(t)}(s_t)` for the state reached by history `h_t`. -/
def shiftEcon (e : Econ L ι κ) (h : Hist L ι κ) :=
  econAt e h.length (stateAt e h)

/-- Definition 5, p. 18: a dynamic ridesharing mechanism, given for every economy: the dispatch
rule `α*_{i,t}(h_t)`, the driver payment rule `r*_{i,t}(h_t)` and the rider payment rule
`q*_j(h_t)`. -/
structure DynMech (L : Type) : Type 1 where
  disp : ∀ {ι κ : Type} [Fintype ι] [Fintype κ], Econ L ι κ → Hist L ι κ → ι → DAction L κ
  pay : ∀ {ι κ : Type} [Fintype ι] [Fintype κ], Econ L ι κ → Hist L ι κ → ι → ℝ
  charge : ∀ {ι κ : Type} [Fintype ι] [Fintype κ], Econ L ι κ → Hist L ι κ → κ → ℝ

/-- A strategy profile: `σ i h_t` is the action of driver `i` at history `h_t`. -/
abbrev Strategy (L ι κ : Type) := ι → Hist L ι κ → DAction L κ

/-- The action of driver `i` at time `t` (her trip `(a, b, t)` and rider tag), if she starts one. -/
def stepTrip (R : κ → Rider L) (t : ℕ) : DState L κ → DAction L κ → Option (Trip L × Option κ)
  | .wait _ a τ, .move b => if τ = t then some ((a, b, t), none) else none
  | .wait _ a τ, .pick j => if τ = t then some ((a, (R j).d, t), some j) else none
  | _, _ => none

/-- The history reached `k` periods after `h` when drivers play `σ`. -/
def playFrom (σ : Strategy L ι κ) (h : Hist L ι κ) : ℕ → Hist L ι κ
  | 0 => h
  | k + 1 => (fun i => σ i (playFrom σ h k)) :: playFrom σ h k

/-- The history of time `t ≥ |h|` reached from `h` under `σ`. -/
def histAt (σ : Strategy L ι κ) (h : Hist L ι κ) (t : ℕ) : Hist L ι κ :=
  playFrom σ h (t - h.length)

/-- p. 18: the number `Σ_{i ∈ D_t} 1{α_{i,t} = (o_j, d_j, t, j)}` of available drivers picking up
rider `j` under the action profile `α` at history `h_t`. -/
def pickCount [Fintype ι] (e : Econ L ι κ) (h : Hist L ι κ) (α : ι → DAction L κ) (j : κ) : ℕ :=
  (Finset.univ.filter fun i => IsAvailAt h.length (stateAt e h i) ∧ α i = .pick j).card

/-- p. 19: `x̂_j`, whether rider `j` is picked up (at time `τ_j ≥ |h|`) when `σ` is played from
`h`. -/
def riderPicked [Fintype ι] (e : Econ L ι κ) (σ : Strategy L ι κ) (h : Hist L ι κ) (j : κ) : ℕ :=
  pickCount e (histAt σ h (e.R j).τ) (fun i => σ i (histAt σ h (e.R j).τ)) j

/-- The trips driver `i` starts at times `t ≥ |h|` when `σ` is played from `h` (original times). -/
def outTrips (e : Econ L ι κ) (σ : Strategy L ι κ) (h : Hist L ι κ) (i : ι) :
    List (Trip L × Option κ) :=
  (List.range (e.P.T - h.length)).filterMap fun k =>
    stepTrip e.R (playFrom σ h k).length (stateAt e (playFrom σ h k) i) (σ i (playFrom σ h k))

/-- Shift a trip started at original time `u ≥ t` to the time-shifted economy `E^{(t)}`. -/
def shiftTrip (e : Econ L ι κ) (t : ℕ) (st : Trip L × Option κ) :
    Trip L × Option {j : κ // t ≤ (e.R j).τ} :=
  ((st.1.1, st.1.2.1, st.1.2.2 - t),
    st.2.bind fun j => if hj : t ≤ (e.R j).τ then some ⟨j, hj⟩ else none)

/-- p. 19: the cost incurred at time `t`: `c_{a,b,t}` on a trip `(a, b, t)` or `(a, b, t, j)`,
`κ_{T−t}` when a driver in state `(1, a, t)` exits, and `0` otherwise. -/
def costNow (e : Econ L ι κ) (h : Hist L ι κ) (i : ι) (α : DAction L κ) : ℝ :=
  match stateAt e h i, α with
  | .wait _ a τ, .move b => if τ = h.length then e.P.c a b h.length else 0
  | .wait _ a τ, .pick j => if τ = h.length then e.P.c a (e.R j).d h.length else 0
  | .wait β _ τ, .quit => if τ = h.length ∧ β = true then e.P.κ (e.P.T - h.length) else 0
  | _, _ => 0

namespace DynMech

variable (M : DynMech L) [Fintype ι] [Fintype κ] (e : Econ L ι κ)

/-- Definition 5, p. 18: the dispatched action `α*_{i,t}(h_t)`: the mechanism's dispatch for an
available driver, and `s_{i,t}` (here `cont`) for every other driver. -/
def dispatch (h : Hist L ι κ) (i : ι) : DAction L κ :=
  if IsAvailAt h.length (stateAt e h i) then M.disp e h i else .cont

/-- p. 18: the available actions `A_{i,t}(h_t)`: for an available driver at `(a, t)`, the
dispatched action, any relocation `(a, b, t)` with `t + δ(a, b) ≤ T`, and `φ`; for every other
driver, the single action `cont`. -/
def actions (h : Hist L ι κ) (i : ι) : Set (DAction L κ) :=
  match stateAt e h i with
  | .wait _ a τ =>
      if τ = h.length then
        {M.disp e h i} ∪ {α | ∃ b, α = .move b ∧ h.length + e.P.δ a b ≤ e.P.T} ∪ {.quit}
      else {.cont}
  | _ => {.cont}

/-- The histories `h_t ∈ H_t` that can arise: at each time `t′ < t ≤ T`, every driver took an
available action. -/
def Reachable : Hist L ι κ → Prop
  | [] => True
  | α :: h => Reachable h ∧ h.length < e.P.T ∧ ∀ i, α i ∈ M.actions e h i

/-- p. 18: a strategy of driver `i` chooses an available action at every history of a time
`t ∈ [T − 1]`. -/
def Admissible (σi : Hist L ι κ → DAction L κ) (i : ι) : Prop :=
  ∀ h : Hist L ι κ, h.length < e.P.T → σi h ∈ M.actions e h i

/-- Every driver's strategy is admissible. -/
def AdmissibleProfile (σ : Strategy L ι κ) : Prop := ∀ i, M.Admissible e (σ i) i

/-- p. 18: the straightforward strategy profile `σ*`: always follow the dispatch. -/
def sigmaStar : Strategy L ι κ := fun i h => M.dispatch e h i

/-- p. 18: the actual payment `r̂_{i,t}(α, h_t) = r*_{i,t}(h_t) 1{α = α*_{i,t}(h_t)}` to an
available driver (and `0` to every other driver, Definition 5). -/
def payNow (h : Hist L ι κ) (i : ι) (α : DAction L κ) : ℝ :=
  if IsAvailAt h.length (stateAt e h i) ∧ α = M.dispatch e h i then M.pay e h i else 0

/-- p. 19: the per-period utility `π̂_{i,t}(α, h_t) = r̂_{i,t}(α, h_t) − (cost at t)`. -/
def utilNow (h : Hist L ι κ) (i : ι) (α : DAction L κ) : ℝ :=
  M.payNow e h i α - costNow e h i α

/-- (23), p. 19: driver `i`'s continuation utility `Σ_{t′=t}^{T−1} π̂_{i,t′}` from history `h_t`
when drivers play `σ` from `h_t` on. -/
def contUtil (σ : Strategy L ι κ) (h : Hist L ι κ) (i : ι) : ℝ :=
  ∑ k ∈ Finset.range (e.P.T - h.length),
    M.utilNow e (playFrom σ h k) i (σ i (playFrom σ h k))

/-- p. 19: `r̂_i(σ) = Σ_{t=0}^{T−1} r̂_{i,t}`, the total payment to driver `i` under `σ`. -/
def totalPay (σ : Strategy L ι κ) (i : ι) : ℝ :=
  ∑ k ∈ Finset.range e.P.T, M.payNow e (playFrom σ [] k) i (σ i (playFrom σ [] k))

/-- p. 18: `q̂_j = q*_j(h_{τ_j}) Σ_{i ∈ D_{τ_j}} 1{α_{i,τ_j} = (o_j, d_j, τ_j, j)}`, rider `j`'s
actual payment when `σ` is played from `h`. -/
def riderCharge (σ : Strategy L ι κ) (h : Hist L ι κ) (j : κ) : ℝ :=
  M.charge e (histAt σ h (e.R j).τ) j * (riderPicked e σ h j : ℝ)

/-- The time-0 plan of the mechanism (p. 12, p. 20): the outcome of `σ*` from `h_0`, as a
static plan `(x, z̃, q, r)` of `e`. -/
def plan0 : Plan e where
  x := fun j => riderPicked e (M.sigmaStar e) [] j
  z := fun i => outTrips e (M.sigmaStar e) [] i
  q := fun j => M.riderCharge e (M.sigmaStar e) [] j
  r := fun i u => if u < e.P.T then
      M.payNow e (playFrom (M.sigmaStar e) [] u) i (M.dispatch e (playFrom (M.sigmaStar e) [] u) i)
    else 0

/-- pp. 19–20: the updated time-`t` plan: the outcome of `σ*` from `h_t` onward, as a static plan
of `E^{(t)}(s_t)` (trips and payments from time `t` on, with times shifted by `t`). -/
def contPlan (h : Hist L ι κ) : Plan (shiftEcon e h) where
  x := fun j => riderPicked e (M.sigmaStar e) h j.1
  z := fun i => (outTrips e (M.sigmaStar e) h i.1).map (shiftTrip e h.length)
  q := fun j => M.riderCharge e (M.sigmaStar e) h j.1
  r := fun i u => if u < e.P.T - h.length then
      M.payNow e (playFrom (M.sigmaStar e) h u) i.1
        (M.dispatch e (playFrom (M.sigmaStar e) h u) i.1)
    else 0

end DynMech

/-- Definition 6, p. 19, with equality: strict budget balance for every economy and every
admissible strategy profile, `Σ_j q̂_j(σ) = Σ_i r̂_i(σ)`. -/
def StrictBB (M : DynMech L) : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ), e.Valid →
    ∀ σ : Strategy L ι κ, M.AdmissibleProfile e σ →
      ∑ j, M.riderCharge e σ [] j = ∑ i, M.totalPay e σ i

/-- (24), p. 19: individual rationality for riders, `x̂_j(σ) v_j ≥ q̂_j(σ)` for every economy,
every admissible strategy profile and every rider. -/
def RiderIR (M : DynMech L) : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ), e.Valid →
    ∀ σ : Strategy L ι κ, M.AdmissibleProfile e σ →
      ∀ j, M.riderCharge e σ [] j ≤ (riderPicked e σ [] j : ℝ) * (e.R j).v

/-- Definition 7, (23), p. 19: subgame-perfect incentive compatibility: for every economy, every
history `h_t` with `t ∈ [T − 1]`, every driver `i` and every admissible strategy `σ_i`,
following the dispatches from `h_t` gives `i` at least the continuation utility of `(σ_i, σ*_{−i})`. -/
def SPIC (M : DynMech L) : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ), e.Valid →
    ∀ h : Hist L ι κ, M.Reachable e h → h.length < e.P.T →
      ∀ (i : ι) (σi : Hist L ι κ → DAction L κ), M.Admissible e σi i →
        M.contUtil e (Function.update (M.sigmaStar e) i σi) h i ≤
          M.contUtil e (M.sigmaStar e) h i

/-- Definition 8 (ii), p. 19, from any history: under `σ*`, every driver who has not yet entered
(state `(0, ℓ_i, τ_i)`) gets non-negative continuation utility, from every history `h_t`,
`t ∈ [T − 1]`. (Condition (i) of Definition 8, SPIC, is the separate property `SPIC`.) -/
def DriverIRFromAnyHistory (M : DynMech L) : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ), e.Valid →
    ∀ h : Hist L ι κ, M.Reachable e h → h.length < e.P.T →
      ∀ (i : ι) (a : L) (τ : ℕ), stateAt e h i = .wait false a τ →
        0 ≤ M.contUtil e (M.sigmaStar e) h i

/-- Definition 9 (ii), (25), p. 20: envy-freeness for drivers: from every history `h_t`,
`t ∈ [T − 1]`, drivers in the same state get the same continuation utility under `σ*`. -/
def EnvyFreeDrivers (M : DynMech L) : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ), e.Valid →
    ∀ h : Hist L ι κ, M.Reachable e h → h.length < e.P.T →
      ∀ i i' : ι, stateAt e h i = stateAt e h i' →
        M.contUtil e (M.sigmaStar e) h i = M.contUtil e (M.sigmaStar e) h i'

/-- Definition 9 (ii), (26), p. 20: envy-freeness for riders: for every rider `j`, every history
`h_{τ_j}` and every rider `j′` requesting the same trip, under `σ*` from `h_{τ_j}`,
`x̂_j v_j − q̂_j ≥ x̂_{j′} v_j − q̂_{j′}`. -/
def EnvyFreeRiders (M : DynMech L) : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ), e.Valid →
    ∀ j j' : κ, riderTrip (e.R j) = riderTrip (e.R j') →
      ∀ h : Hist L ι κ, M.Reachable e h → h.length = (e.R j).τ →
        (riderPicked e (M.sigmaStar e) h j' : ℝ) * (e.R j).v - M.riderCharge e (M.sigmaStar e) h j' ≤
          (riderPicked e (M.sigmaStar e) h j : ℝ) * (e.R j).v - M.riderCharge e (M.sigmaStar e) h j

/-- Definition 10 (ii), p. 20: core-selecting: from every history `h_t`, `t ∈ [T − 1]`, the
outcome of `σ*` (as a plan of `E^{(t)}(s_t)`) is in the core. -/
def CoreSelecting (M : DynMech L) : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ), e.Valid →
    ∀ h : Hist L ι κ, M.Reachable e h → h.length < e.P.T → (M.contPlan e h).InCore

/-- Theorem 2, p. 21, "from any history onward, the equilibrium outcome is welfare optimal":
from every history `h_t`, `t ∈ [T − 1]`, the outcome of `σ*` is a welfare-optimal dispatching of
`E^{(t)}(s_t)`. -/
def WelfareOptimalFromAnyHistory (M : DynMech L) : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ), e.Valid →
    ∀ h : Hist L ι κ, M.Reachable e h → h.length < e.P.T →
      (M.contPlan e h).toDispatch.IsWelfareOptimal

/-- Definition 11, p. 20: temporal consistency: after a deviation at time `t − 1` (some driver's
action differs from her dispatch), the updated plan from `h_t` is identical to the mechanism's
time-0 plan of the economy `E^{(t)}(s_t)`. -/
def TemporallyConsistent (M : DynMech L) : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ), e.Valid →
    ∀ (α : ι → DAction L κ) (h : Hist L ι κ), M.Reachable e (α :: h) →
      (∃ i, α i ≠ M.dispatch e h i) →
        M.contPlan e (α :: h) = M.plan0 (shiftEcon e (α :: h))

end

end STPRideshare.Mechanism


