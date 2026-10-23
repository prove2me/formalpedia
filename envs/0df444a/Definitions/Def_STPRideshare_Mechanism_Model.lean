-- Prove2me | Definitions.Def_STPRideshare_Mechanism_Model
-- name    : STPRideshare_Mechanism_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:30:42.509764+00:00
-- url     : https://prove2.me/theorems/e01a2317-915c-46e9-a855-158cefd6fd1d
-- title:
--   §2–§3, pp. 7–15 — the ridesharing economy, paths and their costs, dispatchings, plans, anonymous trip prices, CE, core, welfare W, replica gains, the LPs (9), (15), (41)
-- statement:
--   This file fixes the static ridesharing economy of Ma, Fang and Parkes and every object of their Section 3.
--
--   **Economy.** A finite set $\mathcal L$ of locations, a horizon $T$, travel times $\delta(a,b)\in\mathbb N$, trip costs $c_{a,b,t}$ and early-exit costs $\kappa_\Delta$. A *trip* $(a,b,t)$ starts at $a$ at time $t$ and ends at $b$ at time $t+\delta(a,b)$; the set of trips is $\mathcal T=\{(a,b,t) : t+\delta(a,b)\le T\}$. Drivers $i\in\mathcal D$ have types $\theta_i=(\beta_i,\ell_i,\tau_i)$ (entrance status, entry location, entry time) and riders $j\in\mathcal R$ have types $(o_j,d_j,\tau_j,v_j)$. An economy is *valid* when the paper's standing assumptions hold:
--   $$\delta(a,b)\ge 1,\quad \delta(a,a)=1,\quad c_{a,b,t}\ge 0 \text{ on } \mathcal T,\quad \kappa_\Delta\ge 0,\quad \kappa_0=0,\quad \tau_i\le T,\quad v_j\ge 0,\quad (o_j,d_j,\tau_j)\in\mathcal T.$$
--
--   **Paths.** A path of driver $i$ is a sequence of trips starting at $(\ell_i,\tau_i)$, each starting where and when the previous one ended. Its cost $\lambda$ is $0$ for the empty path of a driver with $\beta_i=0$ (not entering), and otherwise the sum of its trip costs plus $\kappa_{T-t'}$, where $t'$ is the time the path ends.
--
--   **Dispatchings and plans.** A dispatching $(x,\tilde z)$ gives each driver an *action path* (each trip tagged as a relocation or as the trip of a rider $j$, which must equal $(o_j,d_j,\tau_j)$) and pick-ups $x_j=\sum_i \mathbf 1\{(o_j,d_j,\tau_j,j)\in\tilde z_i\}\in\{0,1\}$. Its welfare is $\sum_j x_jv_j-\sum_i\lambda_i$, and $W(\mathcal D,\mathcal R)$ is the largest welfare of a feasible dispatching. A plan $(x,\tilde z,q,r)$ adds rider payments $q_j$ and driver payments $r_{i,t}$; driver utility is $\pi_i=\sum_{t=0}^T r_{i,t}-\lambda_i$, rider utility $x_jv_j-q_j$. Budget balance (1), individual rationality, envy-freeness (2)–(3), anonymous trip prices (Definition 2), competitive equilibrium (Definition 3) and the core (p. 15) are defined as on the page.
--
--   **Welfare gains.** With $W$ as above,
--   $$\Phi_{D_i}=W(\mathcal D\cup\{i'\},\mathcal R)-W(\mathcal D,\mathcal R),\qquad \Psi_{D_i}=W(\mathcal D,\mathcal R)-W(\mathcal D\setminus\{i\},\mathcal R),\qquad \Phi_{a,t}=W(\mathcal D\cup\{(1,a,t)\})-W(\mathcal D),$$
--   and the STP prices are $p_{a,b,t}=\Phi_{a,t}-\Phi_{b,t+\delta(a,b)}+c_{a,b,t}$ (28).
--
--   **Linear programs.** The LP relaxation (9)–(14), its dual (15)–(19), and the dual (41)–(47) of the flow LP, each as a feasible set with optimality.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note.** Drivers and riders are indexed by finite types; the replica is the index `none` of `Option ι`, removal is the subtype `{k // k ≠ i}`, a coalition is a pair of subsets. The exit time $\bar\tau_i$ is dropped: under (S1) every driver stays until $T$, so the replica of (27) is the type $(1,a,t)$. The printed "for $k>1$" in the path cost (p. 8) is read as $k\ge1$. $W$ is the supremum of the welfares of feasible integral dispatchings (a finite nonempty set for a valid economy), i.e. the optimum of the ILP (4); Lemma 2 states that it equals the optimum of (9). "Every requested trip lies in $\mathcal T$" is an added reading: (5) and (10) are indexed by $\mathcal T$ only. A blocking coalition must use a budget-balanced plan among its members (otherwise every coalition blocks by paying itself). Prices are functions on all triples; only their values on $\mathcal T$ matter.
-- source:
--   Ma, Fang, Parkes, Spatio-Temporal Pricing for Ridesharing Platforms, arXiv:1801.04015v5, pp. 7–15, (1)–(21), (27)–(28), (41)–(47), Definitions 2–3

import Mathlib

namespace STPRideshare.Mechanism

open scoped Classical

noncomputable section

/-- §2, p. 7: a trip `(a, b, t)`: origin `a`, destination `b`, start time `t`. -/
abbrev Trip (L : Type) := L × L × ℕ

/-- §2, pp. 7–8: the horizon `T`, travel times `δ(a, b)`, trip costs `c_{a,b,t}` and the
early-exit costs `κ_Δ` (exiting `Δ` periods before `T`). -/
structure Params (L : Type) where
  T : ℕ
  δ : L → L → ℕ
  c : L → L → ℕ → ℝ
  κ : ℕ → ℝ

/-- §2, p. 7: a driver type `(β, ℓ, τ)` (entrance status, entry location, entry time). The exit
time `τ̄` is dropped: under (S1) every driver stays until the end of the horizon. -/
structure DType (L : Type) where
  β : Bool
  ℓ : L
  τ : ℕ

/-- §2, p. 8: a rider type `(o, d, τ, v)`. -/
structure Rider (L : Type) where
  o : L
  d : L
  τ : ℕ
  v : ℝ

/-- The trip `(o_j, d_j, τ_j)` requested by a rider. -/
def riderTrip {L : Type} (r : Rider L) : Trip L := (r.o, r.d, r.τ)

namespace Params

variable {L : Type} (P : Params L)

/-- p. 7: `(a, b, t) ∈ 𝒯`, i.e. the trip ends by `T`: `t + δ(a, b) ≤ T`. -/
def IsTrip (z : Trip L) : Prop := z.2.2 + P.δ z.1 z.2.1 ≤ P.T

/-- §2, pp. 7–8, standing assumptions: `δ(a, b) ≥ 1`, `δ(a, a) = 1`, `c_{a,b,t} ≥ 0` on `𝒯`,
`κ_Δ ≥ 0` for `Δ ≤ T`, and `κ_0 = 0`. -/
def Valid : Prop :=
  (∀ a b, 1 ≤ P.δ a b) ∧ (∀ a, P.δ a a = 1) ∧
  (∀ a b t, t + P.δ a b ≤ P.T → 0 ≤ P.c a b t) ∧
  (∀ n, n ≤ P.T → 0 ≤ P.κ n) ∧ P.κ 0 = 0

/-- p. 8: `z` is a feasible path starting at location `a` and time `t`: the first trip starts at
`(a, t)`, each next trip starts where and when the previous one ended, and every trip ends by `T`. -/
def IsPathFrom : L → ℕ → List (Trip L) → Prop
  | _, _, [] => True
  | a, t, z :: zs =>
      z.1 = a ∧ z.2.2 = t ∧ t + P.δ a z.2.1 ≤ P.T ∧ IsPathFrom z.2.1 (t + P.δ a z.2.1) zs

/-- The location and time at which a path started at `(a, t)` ends (`(a, t)` for the empty
path); trip `(a, b, t)` ends at `(b, t + δ(a, b))`. -/
def pathEnd : L → ℕ → List (Trip L) → L × ℕ
  | a, t, [] => (a, t)
  | _, _, z :: zs => pathEnd z.2.1 (z.2.2 + P.δ z.1 z.2.1) zs

/-- p. 8: the cost `λ` of a path for a driver of type `θ`: `0` for the empty path of a driver with
`β = 0` (not entering); otherwise the sum of the trip costs plus `κ_{T − t′}`, where `t′` is the
time at which the path ends (for the empty path of a driver with `β = 1`, `κ_{T − τ}`). -/
def pathCost (θ : DType L) (z : List (Trip L)) : ℝ :=
  if θ.β = false ∧ z = [] then 0
  else (z.map fun e => P.c e.1 e.2.1 e.2.2).sum + P.κ (P.T - (P.pathEnd θ.ℓ θ.τ z).2)

end Params

/-- An economy: parameters, drivers indexed by a finite type `ι`, riders indexed by a finite
type `κ`. -/
structure Econ (L ι κ : Type) where
  P : Params L
  D : ι → DType L
  R : κ → Rider L

namespace Econ

variable {L ι κ : Type} (e : Econ L ι κ)

/-- §2, pp. 7–8: the standing assumptions on an economy: valid parameters, every entry time
`τ_i ≤ T`, every rider value `v_j ≥ 0`, and every requested trip in `𝒯`. -/
def Valid : Prop :=
  e.P.Valid ∧ (∀ i, (e.D i).τ ≤ e.P.T) ∧ (∀ j, 0 ≤ (e.R j).v) ∧
  (∀ j, e.P.IsTrip (riderTrip (e.R j)))

/-- The economy with one additional driver of type `θ` (indexed by `none`). -/
def addDriver (θ : DType L) : Econ L (Option ι) κ :=
  ⟨e.P, fun o => o.elim θ e.D, e.R⟩

/-- The economy without driver `i`. -/
def removeDriver (i : ι) : Econ L {k : ι // k ≠ i} κ :=
  ⟨e.P, fun k => e.D k.1, e.R⟩

/-- The sub-economy of a coalition of drivers `S` and riders `U`. -/
def restrict (S : Set ι) (U : Set κ) : Econ L S U :=
  ⟨e.P, fun i => e.D i.1, fun j => e.R j.1⟩

end Econ

/-- §3.1, p. 11: a dispatching `(x, z̃)`: rider pick-ups `x_j` and an action path `z̃_i` for
every driver. An action path is a list of trips, each tagged with the rider it carries (`some j`,
a rider trip `(a, b, t, j)`) or untagged (`none`, a relocation `(a, b, t)`). -/
structure Dispatch {L ι κ : Type} (e : Econ L ι κ) where
  x : κ → ℕ
  z : ι → List (Trip L × Option κ)

namespace Dispatch

variable {L ι κ : Type} [Fintype ι] [Fintype κ] {e : Econ L ι κ} (d : Dispatch e)

/-- The path (movement in space and time) underlying driver `i`'s action path. -/
def path (i : ι) : List (Trip L) := (d.z i).map Prod.fst

/-- §2 p. 8 and §3.1 p. 11: feasibility: each action path follows a feasible path from the
driver's `(ℓ_i, τ_i)`; a rider trip `(a, b, t, j)` has `(a, b, t) = (o_j, d_j, τ_j)`; and
`x_j = Σ_i 1{(o_j, d_j, τ_j, j) ∈ z̃_i} ∈ {0, 1}`. -/
def Feasible : Prop :=
  (∀ i, e.P.IsPathFrom (e.D i).ℓ (e.D i).τ (d.path i)) ∧
  (∀ i st, st ∈ d.z i → ∀ j, st.2 = some j → st.1 = riderTrip (e.R j)) ∧
  (∀ j, d.x j = (Finset.univ.filter fun i => (riderTrip (e.R j), some j) ∈ d.z i).card) ∧
  (∀ j, d.x j ≤ 1)

/-- The cost `λ` of driver `i`'s path. -/
def cost (i : ι) : ℝ := e.P.pathCost (e.D i) (d.path i)

/-- (4), p. 13: welfare `Σ_j x_j v_j − Σ_i λ_i`. -/
def welfare : ℝ := ∑ j, (d.x j : ℝ) * (e.R j).v - ∑ i, d.cost i

/-- A welfare-optimal dispatching: feasible, with welfare at least that of every feasible
dispatching (an optimal solution of the ILP (4)–(8), p. 13). -/
def IsWelfareOptimal : Prop :=
  d.Feasible ∧ ∀ d' : Dispatch e, d'.Feasible → d'.welfare ≤ d.welfare

end Dispatch

/-- p. 14: `W(D, R)`, the highest welfare achievable by the drivers and riders of `e`: the
supremum of the welfares of feasible (integral) dispatchings. (The set is finite and nonempty for
a valid economy, so this is a maximum; by Lemma 2 it equals the optimum of the LP (9).) -/
def W {L ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ) : ℝ :=
  sSup {w : ℝ | ∃ d : Dispatch e, d.Feasible ∧ d.welfare = w}

/-- (20), p. 14: `Φ_{D_i} = W(D ∪ {i′}, R) − W(D, R)`, the welfare gain from a replica of
driver `i`. -/
def PhiD {L ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ) (i : ι) : ℝ :=
  W (e.addDriver (e.D i)) - W e

/-- (21), p. 14: `Ψ_{D_i} = W(D, R) − W(D \ {i}, R)`, the welfare loss from losing driver `i`. -/
def PsiD {L ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ) (i : ι) : ℝ :=
  W e - W (e.removeDriver i)

/-- (27), p. 20: `Φ_{a,t} = W(D ∪ {(1, a, t)}) − W(D)`, the welfare gain from an additional
driver already in the platform at `(a, t)` who stays until `T`. -/
def PhiAt {L ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ) (a : L) (t : ℕ) : ℝ :=
  W (e.addDriver ⟨true, a, t⟩) - W e

/-- §3.1, p. 11: a plan `(x, z̃, q, r)`: a dispatching with rider payments `q_j` and payments
`r_{i,t}` to driver `i` at time `t`. -/
structure Plan {L ι κ : Type} (e : Econ L ι κ) extends Dispatch e where
  q : κ → ℝ
  r : ι → ℕ → ℝ

namespace Plan

variable {L ι κ : Type} [Fintype ι] [Fintype κ] {e : Econ L ι κ} (pl : Plan e)

/-- p. 11: `r_i = Σ_{t=0}^{T} r_{i,t}`. -/
def payTotal (i : ι) : ℝ := ∑ t ∈ Finset.range (e.P.T + 1), pl.r i t

/-- p. 11: driver utility `π_i = r_i − λ_i`. -/
def driverUtil (i : ι) : ℝ := pl.payTotal i - pl.cost i

/-- Rider utility `x_j v_j − q_j`. -/
def riderUtil (j : κ) : ℝ := (pl.x j : ℝ) * (e.R j).v - pl.q j

/-- (1), p. 11: budget balance `Σ_j q_j ≥ Σ_i r_i`. -/
def BB : Prop := ∑ i, pl.payTotal i ≤ ∑ j, pl.q j

/-- p. 11: strict budget balance, (1) with equality. -/
def StrictBB : Prop := ∑ j, pl.q j = ∑ i, pl.payTotal i

/-- p. 11: individual rationality for riders, `x_j v_j ≥ q_j`. -/
def RiderIR : Prop := ∀ j, pl.q j ≤ (pl.x j : ℝ) * (e.R j).v

/-- p. 11: individual rationality for drivers, `π_i ≥ 0` whenever `β_i = 0`. -/
def DriverIR : Prop := ∀ i, (e.D i).β = false → 0 ≤ pl.driverUtil i

/-- (2), p. 12: envy-freeness for riders requesting the same trip. -/
def EFRiders : Prop :=
  ∀ j j', riderTrip (e.R j) = riderTrip (e.R j') →
    (pl.x j' : ℝ) * (e.R j).v - pl.q j' ≤ (pl.x j : ℝ) * (e.R j).v - pl.q j

/-- (3), p. 12: envy-freeness for drivers: drivers with the same `(β, ℓ, τ)` have equal utility. -/
def EFDrivers : Prop := ∀ i i', e.D i = e.D i' → pl.driverUtil i = pl.driverUtil i'

/-- p. 15: the plan is in the core: it is feasible, and no coalition of drivers `S` and riders `U`
has a feasible, budget-balanced plan among themselves (a plan of the sub-economy `(S, U)`) in which
every member gets at least its utility under `pl` and some member gets strictly more. -/
def InCore : Prop :=
  pl.Feasible ∧
  ¬ ∃ (S : Set ι) (U : Set κ) (pl' : Plan (e.restrict S U)),
      pl'.Feasible ∧ pl'.BB ∧
      (∀ i : S, pl.driverUtil i.1 ≤ pl'.driverUtil i) ∧
      (∀ j : U, pl.riderUtil j.1 ≤ pl'.riderUtil j) ∧
      ((∃ i : S, pl.driverUtil i.1 < pl'.driverUtil i) ∨
        (∃ j : U, pl.riderUtil j.1 < pl'.riderUtil j))

end Plan

/-- Anonymous trip prices `p_{a,b,t}` (only their values on `𝒯` matter). -/
abbrev Price (L : Type) := Trip L → ℝ

/-- p. 12: `p⁺_{a,b,t} = max{p_{a,b,t}, 0}`. -/
def posPart {L : Type} (p : Price L) : Price L := fun tr => max (p tr) 0

namespace Dispatch

variable {L ι κ : Type} [Fintype ι] [Fintype κ] {e : Econ L ι κ} (d : Dispatch e)

/-- Definition 2, p. 12: the plan `(x, z̃, p)` with anonymous trip prices: rider `j` pays
`q_j = x_j p_{o_j,d_j,τ_j}`, and driver `i` is paid `p_{o_j,d_j,τ_j}` at time `τ_j` for every
rider trip `(o_j, d_j, τ_j, j)` on her action path, and nothing else. -/
def withPrices (p : Price L) : Plan e :=
  { d with
    q := fun j => (d.x j : ℝ) * p (riderTrip (e.R j))
    r := fun i t => ∑ j, if (riderTrip (e.R j), some j) ∈ d.z i ∧ (e.R j).τ = t
      then p (riderTrip (e.R j)) else 0 }

/-- Definition 3, p. 12: the plan `(x, z̃, p)` (with `(x, z̃)` feasible) forms a competitive
equilibrium: (i) `v_j > p_{o_j,d_j,τ_j} ⇒ x_j = 1` and `x_j = 1 ⇒ v_j ≥ p_{o_j,d_j,τ_j}`;
(ii) every driver's utility is the maximum, over her feasible paths `z`, of
`Σ_{(a,b,t) ∈ z} max{p_{a,b,t}, 0} − λ(z)`. -/
def IsCE (p : Price L) : Prop :=
  d.Feasible ∧
  (∀ j, (p (riderTrip (e.R j)) < (e.R j).v → d.x j = 1) ∧
        (d.x j = 1 → p (riderTrip (e.R j)) ≤ (e.R j).v)) ∧
  (∀ i, IsGreatest {w : ℝ | ∃ z, e.P.IsPathFrom (e.D i).ℓ (e.D i).τ z ∧ w = (z.map fun tr => max (p tr) 0).sum - e.P.pathCost (e.D i) z}
    ((d.withPrices p).driverUtil i))

end Dispatch

/-- The set of driver utility profiles `π` of CE plans of `e` (Lemma 4, p. 14). -/
def ceUtilities {L ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ) : Set (ι → ℝ) :=
  {π | ∃ (d : Dispatch e) (p : Price L), d.IsCE p ∧ π = fun i => (d.withPrices p).driverUtil i}

namespace Econ

variable {L ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ)

/-- (9)–(14), p. 13: `(x, y)` is feasible for the LP relaxation (9). `y i` puts weight `y_{i,k}`
on paths of driver `i` (finitely supported, on feasible paths only); (10) covering of each trip
`(a, b, t) ∈ 𝒯`, (11) `Σ_k y_{i,k} = 1`, (12)–(13) `0 ≤ x_j ≤ 1`, (14) `y_{i,k} ≥ 0`. -/
def LPFeasible (x : κ → ℝ) (y : ι → List (Trip L) →₀ ℝ) : Prop :=
  (∀ i, ∀ k ∈ (y i).support, e.P.IsPathFrom (e.D i).ℓ (e.D i).τ k) ∧
  (∀ tr, e.P.IsTrip tr →
    ∑ j, (if riderTrip (e.R j) = tr then x j else 0) ≤
      ∑ i, (y i).sum fun k w => if tr ∈ k then w else 0) ∧
  (∀ i, ((y i).sum fun _ w => w) = 1) ∧
  (∀ j, x j ≤ 1) ∧ (∀ j, 0 ≤ x j) ∧ (∀ i k, 0 ≤ y i k)

/-- (9), p. 13: the LP objective `Σ_j x_j v_j − Σ_i Σ_k y_{i,k} λ_{i,k}`. -/
def lpObj (x : κ → ℝ) (y : ι → List (Trip L) →₀ ℝ) : ℝ :=
  ∑ j, x j * (e.R j).v - ∑ i, (y i).sum fun k w => w * e.P.pathCost (e.D i) k

/-- (15)–(19), p. 14: `(p, π, u)` is feasible for the dual LP (15): (16) `π_i ≥ Σ_{(a,b,t)∈Z}
p_{a,b,t} − λ_i(Z)` for every feasible path `Z` of driver `i`, (17) `u_j ≥ v_j − p_{o_j,d_j,τ_j}`,
(18) `p ≥ 0` on `𝒯`, (19) `u ≥ 0`. -/
def DualFeasible (p : Price L) (π : ι → ℝ) (u : κ → ℝ) : Prop :=
  (∀ i z, e.P.IsPathFrom (e.D i).ℓ (e.D i).τ z →
    (z.map p).sum - e.P.pathCost (e.D i) z ≤ π i) ∧
  (∀ j, (e.R j).v - p (riderTrip (e.R j)) ≤ u j) ∧
  (∀ tr, e.P.IsTrip tr → 0 ≤ p tr) ∧ (∀ j, 0 ≤ u j)

/-- (15), p. 14: `(p, π, u)` is an optimal solution of the dual LP: feasible and minimizing
`Σ_i π_i + Σ_j u_j` among feasible solutions. -/
def DualOptimal (p : Price L) (π : ι → ℝ) (u : κ → ℝ) : Prop :=
  e.DualFeasible p π u ∧
  ∀ p' π' u', e.DualFeasible p' π' u' → ∑ i, π i + ∑ j, u j ≤ ∑ i, π' i + ∑ j, u' j

/-- (41)–(47), p. 42: `(ϕ, ϕ_D, μ)` is feasible for the dual (41) of the flow LP: node potentials
`ϕ_{a,t}` (`t ≤ T`), driver potentials `ϕ_{D_i}`, rider variables `μ_j`. -/
def FlowDualFeasible (ϕ : L → ℕ → ℝ) (ϕD : ι → ℝ) (μ : κ → ℝ) : Prop :=
  (∀ j, (e.R j).v - e.P.c (e.R j).o (e.R j).d (e.R j).τ ≤
    ϕ (e.R j).o (e.R j).τ - ϕ (e.R j).d ((e.R j).τ + e.P.δ (e.R j).o (e.R j).d) + μ j) ∧
  (∀ a b t, t + e.P.δ a b ≤ e.P.T → -e.P.c a b t ≤ ϕ a t - ϕ b (t + e.P.δ a b)) ∧
  (∀ a t, t ≤ e.P.T → -e.P.κ (e.P.T - t) ≤ ϕ a t) ∧
  (∀ i, ϕ (e.D i).ℓ (e.D i).τ ≤ ϕD i) ∧
  (∀ i, (e.D i).β = false → 0 ≤ ϕD i) ∧
  (∀ j, 0 ≤ μ j)

/-- (41), p. 42: an optimal solution of the flow dual: feasible and minimizing
`Σ_i ϕ_{D_i} + Σ_j μ_j`. -/
def FlowDualOptimal (ϕ : L → ℕ → ℝ) (ϕD : ι → ℝ) (μ : κ → ℝ) : Prop :=
  e.FlowDualFeasible ϕ ϕD μ ∧
  ∀ ϕ' ϕD' μ', e.FlowDualFeasible ϕ' ϕD' μ' → ∑ i, ϕD i + ∑ j, μ j ≤ ∑ i, ϕD' i + ∑ j, μ' j

/-- (28), p. 21: the STP trip prices of a (static) economy,
`p_{a,b,t} = Φ_{a,t} − Φ_{b,t+δ(a,b)} + c_{a,b,t}`. -/
def stpPrice : Price L := fun tr =>
  PhiAt e tr.1 tr.2.2 - PhiAt e tr.2.1 (tr.2.2 + e.P.δ tr.1 tr.2.1) + e.P.c tr.1 tr.2.1 tr.2.2

end Econ

end

end STPRideshare.Mechanism


