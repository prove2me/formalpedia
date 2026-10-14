-- Prove2me | Definitions.Def_UnknownLoads_Coxian_Construction
-- name    : UnknownLoads_Coxian_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:05.633229+00:00
-- url     : https://prove2.me/theorems/fb3dae34-05b6-422e-86f9-65f677224422
-- title:
--   §6.1.1 — the coupled construction: stochastic primitives, dispatching indicators r_ij(s, ℓ), counting processes and equations (21a)–(21b)
-- statement:
--   This file builds the coupled sequence of systems of Section 6.1.1, indexed by the number $n \ge 1$ of server pools, on one probability space $(\Omega,\mathcal F,\mathbb P)$.
--
--   **Primitives.**
--   1. Independent unit-rate Poisson processes $\{\mathcal N_{(\nu,i,j)} : \nu \in \mathbb N^r,\ i \in \{0,\dots,r\},\ j \in \{0,1\}\}$.
--   2. Selection variables $\{U_j : j \ge 1\}$, i.i.d. uniform with values in $[0,1)$.
--   3. Initial occupancy states $\{s_n(0) : n \ge 1\}$. Almost surely, every $s_n(0)$ lies in $S$, $n\,s_n(0,\nu)$ is an integer, $q_n(0, B+1) = 0$ for a fixed $B \in \mathbb N$, and $s_n(0) \to s(0) \in S$ coordinatewise (assumption (2)).
--   4. The three families are mutually independent.
--
--   **Dispatching.** For a state $s$, the intervals $I_i(s)$, $i \ge 0$, partition $[0,1)$ with $|I_i(s)| = s(\nu_i)$, and, if $q(j) < 1$, the intervals $J_i(s,j)$ partition $[0,1)$ with $|J_i(s,j)| = s(\nu_i)\mathbb 1\{\Sigma_i < j\}/(1-q(j))$ ($J_i(s,j) = \emptyset$ if $q(j)=1$). With $h = \ell + \Delta$,
--   $$r_{ij}(s,\ell) = \begin{cases} \mathbb 1\{U_j \in J_i(s,\ell)\} & \Sigma_i < \ell,\\ \mathbb 1\{q(\ell) = 1,\ U_j \in J_i(s,h)\} & \ell \le \Sigma_i < h,\\ \mathbb 1\{q(h) = 1,\ U_j \in I_i(s)\} & \Sigma_i \ge h,\end{cases}$$
--   and the $j$-th task is sent to a pool with profile $\nu_i$ iff $r_{ij} = 1$.
--
--   **Equations.** $\mathcal N^\lambda_n(t) := \mathcal N_{(0,0,0)}(n\lambda t)$ counts the arrivals, with jump times $\tau_{n,k}$ ($\tau_{n,0} = 0$). The occupancy process $s_n$ and the threshold $\ell_n$ solve, for all $t \ge 0$,
--   $$s_n(t) = s_n(0) + \bar{\mathcal A}_n(t) + \bar{\mathcal P}_n(t) + \bar{\mathcal D}_n(t), \qquad \ell_n(t) = \lfloor u_n(t) \rfloor_\Delta, \tag{21}$$
--   where $\bar{\mathcal A}_n(t,\nu) = \mathcal A_n(t,\nu-e_1) - \mathcal A_n(t,\nu)$, $\bar{\mathcal P}_n(t,\nu) = \sum_{m=1}^{r-1}[\mathcal P_n(t,\nu+e_m-e_{m+1},m) - \mathcal P_n(t,\nu,m)]$, $\bar{\mathcal D}_n(t,\nu) = \sum_{m=1}^{r}[\mathcal D_n(t,\nu+e_m,m) - \mathcal D_n(t,\nu,m)]$, and
--   $$\mathcal A_n(t,\nu_i) = \frac1n\sum_{j=1}^{\mathcal N^\lambda_n(t)} r_{ij}\big(s_n(\tau_{n,j}^-),\ell_n(\tau_{n,j}^-)\big),\quad \mathcal P_n(t,\nu,m) = \frac1n\mathcal N_{(\nu,m,0)}\Big(n\!\int_0^t p_m\mu_m\nu(m)s_n(\tau,\nu)\,d\tau\Big),$$
--   $$\mathcal D_n(t,\nu,m) = \frac1n\mathcal N_{(\nu,m,1)}\Big(n\!\int_0^t (1-p_m)\mu_m\nu(m)s_n(\tau,\nu)\,d\tau\Big);$$
--   $\mathcal A_n(t,\nu)$ and $\mathcal P_n(t,\nu,m)$ are zero when $\nu$ has a negative component.
--
--   A **system** consists of the primitives together with processes $s_n(\omega,t)$, $\ell_n(\omega,t)$ that, almost surely, solve these equations for every $n \ge 1$, are càdlàg, take values in $S$ and have finitely many tasks at every time. The paper asserts the solution is unique on a set of probability one, so this pins down the paper's processes almost surely.
--
--   **Formalization Note** The equations are imposed for all $t \ge 0$ (horizon-free), which Theorem 3 needs because its constants must not depend on $T$. The Poisson processes are `BesbesZeevi.Parametric.PoissonProcess`; their mutual independence is `iIndepFun` of the path maps over the index type $\mathbb N^r \times \{0,\dots,r\} \times \{0,1\}$, and the independence of the three families is `iIndep` of the three generated σ-algebras (the completion of the product space is immaterial for almost-sure statements). The paper defines $r_{ij}$ "for all $i, j \ge 1$"; since the enumeration starts at $i = 0$, it is defined here for all $i \ge 0$. The interval endpoints are written with the finite partial sums $\sum_{k<i}$, which agree with the paper's $1 - \sum_{k\ge i}$ on $S$; for $J_i$ the paper's printed endpoints $(1-\sum_{k\ge i} s(\nu_k)\mathbb 1\{\Sigma_k<j\})/(1-q(j))$ are shifted by $q(j)/(1-q(j))$ and do not partition $[0,1)$, so the corrected endpoints $\sum_{k<i} s(\nu_k)\mathbb 1\{\Sigma_k<j\}/(1-q(j))$ are used. Left limits are `Function.leftLim`; $\nu - e_1$ and $\nu + e_m - e_{m+1}$ are guarded by `if`, never by truncated subtraction; $n s_n(0,\nu) \in \mathbb N$ is added (fractions of $n$ pools); $\ell_n(0) \le B$ is not stated because it follows from (21b).
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, p. 14 (§3, assumption (2) and the bound B), pp. 38–40 (§6.1.1: primitives, I_i, J_i, r_ij, 𝒩^λ_n, equations (21a)–(21b))

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_PoissonProcess
import Definitions.Def_UnknownLoads_Coxian_Model

namespace UnknownLoads.Coxian

/-! Goldsztajn, Borst & van Leeuwaarden, arXiv:2012.10142v3, §3 (pp. 13–14) and §6.1.1
(pp. 38–40): the stochastic primitives, the dispatching indicators `r_ij(s, ℓ)`, the counting
processes `𝒜_n`, `𝒫_n`, `𝒟_n` and the equations (21a)–(21b) of the coupled construction.
The system is horizon-free: the equations are imposed for all `t ≥ 0`. -/

open MeasureTheory ProbabilityTheory Filter Topology

open scoped Classical

/-- Index set `ℕ^r × {0,…,r} × {0,1}` of the driving Poisson processes `𝒩_(ν,i,j)` (p. 38).
The paper's phase `m ∈ {1,…,r}` is `i = m`, i.e. `(Fin.succ (m - 1) : Fin (r+1))`. -/
abbrev PoissonIndex (r : ℕ) := Profile r × Fin (r + 1) × Fin 2

/-- The stochastic primitives of §6.1.1 (p. 38) on one probability space, with the standing
assumptions of §3 (p. 14) on the initial conditions.
* `N`: independent unit-rate Poisson processes `𝒩_(ν,i,j)`;
* `U j`, `j ≥ 1`: i.i.d. uniform selection variables with values in `[0, 1)` (`U 0` is unused);
* `s0 n`, `n ≥ 1`: the random initial occupancy states `s_n(0)`;
* the three families are mutually independent;
* (2): `s_n(0) → sLim ∈ S` coordinatewise almost surely;
* `q_n(0, B + 1) = 0` for all `n` almost surely; `s_n(0) ∈ S` and `n s_n(0, ν) ∈ ℕ`. -/
structure Primitives (P : Params) (Ω : Type*) [MeasurableSpace Ω] (μP : Measure Ω) where
  prob : IsProbabilityMeasure μP
  N : PoissonIndex P.r → BesbesZeevi.Parametric.PoissonProcess Ω μP
  N_indep : iIndepFun (fun (i : PoissonIndex P.r) (ω : Ω) (t : ℝ) => (N i).count t ω) μP
  U : ℕ → Ω → ℝ
  U_meas : ∀ j, Measurable (U j)
  U_mem : ∀ j ω, U (j + 1) ω ∈ Set.Ico (0 : ℝ) 1
  U_law : ∀ j, μP.map (U (j + 1)) = volume.restrict (Set.Ico (0 : ℝ) 1)
  U_indep : iIndepFun (fun j : ℕ => U (j + 1)) μP
  s0 : ℕ → Ω → Profile P.r → ℝ
  s0_meas : ∀ n ν, Measurable (fun ω => s0 n ω ν)
  families_indep : iIndep
    (![⨆ i : PoissonIndex P.r,
          MeasurableSpace.comap (fun (ω : Ω) (t : ℝ) => (N i).count t ω) inferInstance,
        ⨆ j : ℕ, MeasurableSpace.comap (U (j + 1)) inferInstance,
        ⨆ n : ℕ, ⨆ ν : Profile P.r, MeasurableSpace.comap (fun ω => s0 n ω ν) inferInstance] :
      Fin 3 → MeasurableSpace Ω) μP
  sLim : Profile P.r → ℝ
  sLim_mem : InS sLim
  s0_tendsto : ∀ᵐ ω ∂μP, ∀ ν, Tendsto (fun n => s0 n ω ν) atTop (𝓝 (sLim ν))
  B : ℕ
  s0_good : ∀ᵐ ω ∂μP, ∀ n : ℕ, 1 ≤ n →
    InS (s0 n ω) ∧ (∀ ν, ∃ k : ℕ, (n : ℝ) * s0 n ω ν = k) ∧ qOf (s0 n ω) (B + 1) = 0

variable {P : Params} {Ω : Type*} [MeasurableSpace Ω] {μP : Measure Ω}

/-- `Σ_{k < i} s(ν_k)`, the left endpoint of `I_i(s)`; on `S` it equals `1 - Σ_{k ≥ i} s(ν_k)`. -/
noncomputable def partialMass (P : Params) (s : Profile P.r → ℝ) (i : ℕ) : ℝ :=
  ∑ k ∈ Finset.range i, s (P.enum k)

/-- `I_i(s) = [1 - Σ_{j ≥ i} s(ν_j), 1 - Σ_{j ≥ i+1} s(ν_j))` (p. 38), written with the
equivalent finite partial sums. -/
noncomputable def intervalI (P : Params) (s : Profile P.r → ℝ) (i : ℕ) : Set ℝ :=
  Set.Ico (partialMass P s i) (partialMass P s (i + 1))

/-- `Σ_{k < i} s(ν_k) 𝟙{Σ_k < j}`. -/
noncomputable def partialMassBelow (P : Params) (s : Profile P.r → ℝ) (j i : ℕ) : ℝ :=
  ∑ k ∈ Finset.range i, if total (P.enum k) < j then s (P.enum k) else 0

/-- `J_i(s, j)` (p. 38): if `q(j) < 1`, the interval of length `s(ν_i) 𝟙{Σ_i < j}/(1 - q(j))`
whose left endpoint is `Σ_{k<i} s(ν_k) 𝟙{Σ_k<j}/(1 - q(j))`; empty if `q(j) = 1`.
(Corrected: the printed endpoints `(1 - Σ_{k≥i} …)/(1 - q(j))` are shifted by
`q(j)/(1 - q(j))` and do not partition `[0, 1)`, contrary to the text.) -/
noncomputable def intervalJ (P : Params) (s : Profile P.r → ℝ) (j i : ℕ) : Set ℝ :=
  if qOf s j < 1 then
    Set.Ico (partialMassBelow P s j i / (1 - qOf s j)) (partialMassBelow P s j (i + 1) / (1 - qOf s j))
  else ∅

/-- The dispatching indicator `r_ij(s, ℓ)` (p. 39), with `u = U_j` and `h = ℓ + Δ`, defined for
all `i ≥ 0`: `1{U_j ∈ J_i(s,ℓ)}` if `Σ_i < ℓ`; `1{q(ℓ)=1, U_j ∈ J_i(s,h)}` if `ℓ ≤ Σ_i < h`;
`1{q(h)=1, U_j ∈ I_i(s)}` if `Σ_i ≥ h`. -/
noncomputable def routeInd (P : Params) (u : ℝ) (s : Profile P.r → ℝ) (ℓ : ℕ) (i : ℕ) : ℝ :=
  if total (P.enum i) < ℓ then (if u ∈ intervalJ P s ℓ i then 1 else 0)
  else if total (P.enum i) < ℓ + P.Δ then
    (if qOf s ℓ = 1 ∧ u ∈ intervalJ P s (ℓ + P.Δ) i then 1 else 0)
  else (if qOf s (ℓ + P.Δ) = 1 ∧ u ∈ intervalI P s i then 1 else 0)

/-- The arrival process `𝒩^λ_n(t) := 𝒩_(0,0,0)(nλt)` (p. 39). -/
def arrivalCount (prim : Primitives P Ω μP) (n : ℕ) (ω : Ω) (t : ℝ) : ℕ :=
  (prim.N (0, 0, 0)).count ((n : ℝ) * P.lam * t) ω

/-- The `k`-th jump time `τ_{n,k}` of `𝒩^λ_n`, with `τ_{n,0} = 0`. -/
noncomputable def arrivalTime (prim : Primitives P Ω μP) (n : ℕ) (ω : Ω) (k : ℕ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ k ≤ arrivalCount prim n ω t}

/-- The coordinatewise left limit `s(τ⁻)` of an occupancy path. -/
noncomputable def leftLimState {r : ℕ} (s : ℝ → Profile r → ℝ) (τ : ℝ) : Profile r → ℝ :=
  fun ν => Function.leftLim (fun t => s t ν) τ

/-- `𝒜_n(t, ν_i) = (1/n) Σ_{j=1}^{𝒩^λ_n(t)} r_ij(s(τ⁻_{n,j}), ℓ(τ⁻_{n,j}))` (p. 40), for paths
`s`, `ℓ`; arrivals to pools with profile `ν = ν_i`. -/
noncomputable def arrivalsA (prim : Primitives P Ω μP) (n : ℕ) (ω : Ω)
    (s : ℝ → Profile P.r → ℝ) (ℓ : ℝ → ℕ) (t : ℝ) (ν : Profile P.r) : ℝ :=
  (1 / (n : ℝ)) * ∑ j ∈ Finset.Icc 1 (arrivalCount prim n ω t),
    routeInd P (prim.U j ω) (leftLimState s (arrivalTime prim n ω j))
      (Function.leftLim ℓ (arrivalTime prim n ω j)) (P.enum.symm ν)

/-- `𝒫_n(t, ν, m) = (1/n) 𝒩_(ν,m,0)(n ∫_0^t p_m μ_m ν(m) s(τ, ν) dτ)` (p. 40): phase-`m` to
phase-`m+1` transitions in pools with profile `ν`. -/
noncomputable def transP (prim : Primitives P Ω μP) (n : ℕ) (ω : Ω) (s : ℝ → Profile P.r → ℝ)
    (t : ℝ) (ν : Profile P.r) (m : Fin P.r) : ℝ :=
  (1 / (n : ℝ)) * ((prim.N (ν, m.succ, 0)).count
    ((n : ℝ) * ∫ τ in (0 : ℝ)..t, P.p m * P.μ m * (ν m : ℝ) * s τ ν) ω : ℝ)

/-- `𝒟_n(t, ν, m) = (1/n) 𝒩_(ν,m,1)(n ∫_0^t (1 - p_m) μ_m ν(m) s(τ, ν) dτ)` (p. 40): departures
of phase-`m` tasks from pools with profile `ν`. -/
noncomputable def depD (prim : Primitives P Ω μP) (n : ℕ) (ω : Ω) (s : ℝ → Profile P.r → ℝ)
    (t : ℝ) (ν : Profile P.r) (m : Fin P.r) : ℝ :=
  (1 / (n : ℝ)) * ((prim.N (ν, m.succ, 1)).count
    ((n : ℝ) * ∫ τ in (0 : ℝ)..t, (1 - P.p m) * P.μ m * (ν m : ℝ) * s τ ν) ω : ℝ)

/-- `Ā_n(t, ν) = 𝒜_n(t, ν - e_1) - 𝒜_n(t, ν)`, with `𝒜_n(t, ν - e_1) := 0` if `ν(1) = 0`. -/
noncomputable def arrivalsBar (prim : Primitives P Ω μP) (n : ℕ) (ω : Ω)
    (s : ℝ → Profile P.r → ℝ) (ℓ : ℝ → ℕ) (t : ℝ) (ν : Profile P.r) : ℝ :=
  (if 0 < ν (firstPhase P) then
      arrivalsA prim n ω s ℓ t (Function.update ν (firstPhase P) (ν (firstPhase P) - 1))
    else 0) - arrivalsA prim n ω s ℓ t ν

/-- `P̄_n(t, ν) = Σ_{m=1}^{r-1} [𝒫_n(t, ν + e_m - e_{m+1}, m) - 𝒫_n(t, ν, m)]`, with the first
term `0` if `ν(m+1) = 0`. -/
noncomputable def transBar (prim : Primitives P Ω μP) (n : ℕ) (ω : Ω)
    (s : ℝ → Profile P.r → ℝ) (t : ℝ) (ν : Profile P.r) : ℝ :=
  ∑ m : Fin P.r,
    if h : m.val + 1 < P.r then
      (if 0 < ν ⟨m.val + 1, h⟩ then
          transP prim n ω s t
            (Function.update (Function.update ν m (ν m + 1)) ⟨m.val + 1, h⟩ (ν ⟨m.val + 1, h⟩ - 1)) m
        else 0) - transP prim n ω s t ν m
    else 0

/-- `D̄_n(t, ν) = Σ_{m=1}^{r} [𝒟_n(t, ν + e_m, m) - 𝒟_n(t, ν, m)]`. -/
noncomputable def depBar (prim : Primitives P Ω μP) (n : ℕ) (ω : Ω)
    (s : ℝ → Profile P.r → ℝ) (t : ℝ) (ν : Profile P.r) : ℝ :=
  ∑ m : Fin P.r, (depD prim n ω s t (Function.update ν m (ν m + 1)) m - depD prim n ω s t ν m)

/-- `(s, ℓ)` is a solution, at the sample point `ω`, of the equations of the `n`-th system
(pp. 39–40), for all `t ≥ 0`: `S`-valued with finitely many tasks, càdlàg, and
(21a) `s(t) = s_n(0) + Ā_n(t) + P̄_n(t) + D̄_n(t)`, (21b) `ℓ(t) = ⌊u(t)⌋_Δ`. -/
def Solves (prim : Primitives P Ω μP) (n : ℕ) (ω : Ω) (s : ℝ → Profile P.r → ℝ) (ℓ : ℝ → ℕ) :
    Prop :=
  (∀ t : ℝ, 0 ≤ t → InS (s t)) ∧
  (∀ t : ℝ, 0 ≤ t → ∃ K : ℕ, ∀ ν, K < total ν → s t ν = 0) ∧
  (∀ ν, IsCadlagOn (fun t => s t ν)) ∧
  IsCadlagOn (fun t => (ℓ t : ℝ)) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ ν, s t ν = prim.s0 n ω ν + arrivalsBar prim n ω s ℓ t ν +
      transBar prim n ω s t ν + depBar prim n ω s t ν) ∧
  (∀ t : ℝ, 0 ≤ t → (ℓ t : ℤ) = floorDelta P.Δ (uMass (s t)))

/-- The coupled sequence of §6.1.1: primitives together with occupancy processes `s n ω t ν`
and thresholds `ℓ n ω t` that, almost surely, solve the equations of every system `n ≥ 1`. -/
structure System (P : Params) (Ω : Type*) [MeasurableSpace Ω] (μP : Measure Ω)
    extends Primitives P Ω μP where
  s : ℕ → Ω → ℝ → Profile P.r → ℝ
  ℓ : ℕ → Ω → ℝ → ℕ
  solves : ∀ᵐ ω ∂μP, ∀ n : ℕ, 1 ≤ n → Solves toPrimitives n ω (s n ω) (ℓ n ω)

/-- `q_n(ω, t, i)` of the system, via (1). -/
noncomputable def System.q (sys : System P Ω μP) (n : ℕ) (ω : Ω) (t : ℝ) (i : ℕ) : ℝ :=
  qOf (sys.s n ω t) i

/-- `𝒜_n(ω, t, ν)` of the system. -/
noncomputable def System.A (sys : System P Ω μP) (n : ℕ) (ω : Ω) (t : ℝ) (ν : Profile P.r) : ℝ :=
  arrivalsA sys.toPrimitives n ω (sys.s n ω) (sys.ℓ n ω) t ν

/-- `𝒫_n(ω, t, ν, m)` of the system. -/
noncomputable def System.Ptr (sys : System P Ω μP) (n : ℕ) (ω : Ω) (t : ℝ) (ν : Profile P.r)
    (m : Fin P.r) : ℝ :=
  transP sys.toPrimitives n ω (sys.s n ω) t ν m

/-- `𝒟_n(ω, t, ν, m)` of the system. -/
noncomputable def System.D (sys : System P Ω μP) (n : ℕ) (ω : Ω) (t : ℝ) (ν : Profile P.r)
    (m : Fin P.r) : ℝ :=
  depD sys.toPrimitives n ω (sys.s n ω) t ν m

end UnknownLoads.Coxian


