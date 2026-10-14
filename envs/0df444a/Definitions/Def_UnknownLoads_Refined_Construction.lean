-- Prove2me | Definitions.Def_UnknownLoads_Refined_Construction
-- name    : UnknownLoads_Refined_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:15.13672+00:00
-- url     : https://prove2.me/theorems/8d66493e-2138-4e9f-afa3-324a2ab9147b
-- title:
--   Coupled construction of §5.1.1: primitives, routing indicators r_ij, arrival and departure processes, and the equations (9a)–(9b)
-- statement:
--   This module sets up the coupled construction of the sample paths of §5.1.1, on one probability space $(\Omega,\mathcal F,\mathbb P)$.
--
--   1. **Primitives.** Independent unit-rate Poisson processes $\{\mathcal N_i:i\ge0\}$; i.i.d. selection variables $\{U_j:j\ge1\}$, uniform on $[0,1)$; and initial conditions $\{q_n(0):n\ge1\}$, $\{\ell_n(0):n\ge1\}$. The three families are mutually independent. The initial conditions satisfy the assumptions of §3: almost surely, for all $n\ge1$, $q_n(0)\in Q$, $nq_n(0,i)\in\mathbb N$ for every $i$, $\ell_n(0)$ is a multiple of $\Delta$, $q_n(0,B+1)=0$ and $\ell_n(0)\le B$ for a constant $B\in\mathbb N$; and $q_n(0)\to q(0)$ coordinatewise almost surely for a constant $q(0)$ ((2) with $r=1$).
--   2. **Routing.** For $q\in Q$, $I_i(q):=[1-q(i-1),1-q(i))$ for $i\ge1$; $J_i(q,j):=\big[\frac{1-q(i-1)}{1-q(j)},\frac{1-q(i)}{1-q(j)}\big)$ if $q(j)<1$ and $J_i(q,j):=\emptyset$ if $q(j)=1$, for $1\le i\le j$. With $h:=\ell+\Delta$,
--   $$
--   r_{ij}(q,\ell):=\begin{cases}\mathbb 1_{\{U_j\in J_i(q,\ell)\}}&\text{if } i-1<\ell,\\ \mathbb 1_{\{q(\ell)=1,\,U_j\in J_i(q,h)\}}&\text{if } \ell\le i-1<h,\\ \mathbb 1_{\{q(h)=1,\,U_j\in I_i(q)\}}&\text{if } i-1\ge h,\end{cases}\qquad i,j\ge1 .
--   $$
--   3. **Arrivals and departures.** $\mathcal N^\lambda_n(t):=\mathcal N_0\big(n\int_0^t\lambda(s)ds\big)$ with jump times $\tau_{n,k}$, $k\ge1$, and $\tau_{n,0}:=0$. For paths $q:[0,T]\to Q$ and $\ell:[0,T]\to\mathbb N$, and $i\ge1$,
--   $$
--   \mathcal A_n(q,\ell,t,i):=\frac1n\sum_{j=1}^{\mathcal N^\lambda_n(t)}r_{ij}\big(q(\tau^-_{n,j}),\ell(\tau^-_{n,j})\big),\qquad \mathcal D_n(q,t,i):=\frac1n\mathcal N_i\Big(n\int_0^t\mu i\,[q(s,i)-q(s,i+1)]\,ds\Big),
--   $$
--   and the $i=0$ coordinates are $0$.
--   4. **The equations** (9a)–(9b). A pair $(q,\ell)$ solves the equations of the $n$-th system at $\omega$, with control parameter $\alpha_n$, if both are càdlàg on $[0,T]$, $q$ is $Q$-valued, and for all $t\in[0,T]$
--   $$
--   q(t)=q_n(0)+\mathcal A_n(q,\ell,t)-\mathcal D_n(q,t),
--   $$
--   $$
--   \ell(t)=\ell_n(0)+\sum_{k=1}^{\mathcal N^\lambda_n(t)}\Delta\Big[\mathbb 1_{\{q(\tau^-_{n,k},\ell(\tau^-_{n,k}))=1,\ nq(\tau^-_{n,k},\ell(\tau^-_{n,k})+\Delta)\ge n-1\}}-\mathbb 1_{\{q(\tau^-_{n,k},\ell(\tau^-_{n,k}))\le\alpha_n\}}\Big].
--   $$
--
--   The first equation is the threshold dispatching rule of §2.1 and the second the refined learning scheme of §2.2.2; the occupancy states and thresholds of the paper are the solutions of these equations.
--
--   **Formalization Note** The probability space is any space carrying primitives with these laws and this independence; the paper's completed product space is one instance, and completion does not affect almost-sure statements. Each $\mathcal N_i$ is the published `BesbesZeevi.Parametric.PoissonProcess`; the family is independent as a family of path maps. The initial-condition assumptions are imposed almost surely; $nq_n(0,i)\in\mathbb N$ and $\ell_n(0)\in\Delta\mathbb N$ are implicit in the paper (fractions of $n$ pools; thresholds are nonnegative multiples of $\Delta$). Time is real; the equations are imposed on $[0,T]$. Left limits $q(\tau^-)$, $\ell(\tau^-)$ are `Function.leftLim`, coordinatewise for $q$. $\tau_{n,k}=\inf\{t\ge0:\mathcal N^\lambda_n(t)\ge k\}$, used only for $k\le\mathcal N^\lambda_n(t)$, $t\le T$. (9b) is stated after casting $\ell$ to $\mathbb R$. $U_0$ exists but is never used.
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, pp. 22–25, §5.1.1 (primitives, I_i, J_i, r_ij, 𝒜_n, 𝒟_n, (9a)–(9b)); p. 14, §3 (assumptions on the initial conditions, (2))

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_PoissonProcess
import Definitions.Def_UnknownLoads_Refined_Load

namespace UnknownLoads.Refined

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- The stochastic primitives of the coupled construction (§5.1.1, pp. 22–23) and the standing
assumptions on the initial conditions (§3, p. 14), on one probability space `(Ω, P)`:
* driving Poisson processes `𝒩ᵢ`, `i ≥ 0`: independent, unit rate;
* selection variables `Uⱼ` (used for `j ≥ 1`): i.i.d. uniform with values in `[0, 1)`;
* initial conditions `qₙ(0)`, `ℓₙ(0)`, `n ≥ 1`: `Q`-valued, `n qₙ(0, i) ∈ ℕ`, `ℓₙ(0) ∈ Δℕ`,
  `qₙ(0, B+1) = 0` and `ℓₙ(0) ≤ B` for all `n` almost surely, and `qₙ(0) → q(0)`
  coordinatewise almost surely ((2) with `r = 1`);
* the three families are mutually independent. -/
structure Primitives (D : LoadData) (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) where
  /-- The driving unit-rate Poisson processes `𝒩ᵢ`, `i ≥ 0`. -/
  N : ℕ → BesbesZeevi.Parametric.PoissonProcess Ω P
  N_indep : iIndepFun (fun i (ω : Ω) => fun t : ℝ => (N i).count t ω) P
  /-- The selection variables `Uⱼ` (`U 0` is never used). -/
  U : ℕ → Ω → ℝ
  U_measurable : ∀ j, Measurable (U j)
  U_mem : ∀ j ω, U j ω ∈ Ico (0 : ℝ) 1
  U_indep : iIndepFun U P
  U_uniform : ∀ j, Measure.map (U j) P = volume.restrict (Ico (0 : ℝ) 1)
  /-- The initial occupancy states `qₙ(0)`. -/
  qInit : ℕ → Ω → ℕ → ℝ
  /-- The initial thresholds `ℓₙ(0)`. -/
  ℓInit : ℕ → Ω → ℕ
  qInit_measurable : ∀ n i, Measurable (fun ω => qInit n ω i)
  ℓInit_measurable : ∀ n, Measurable (ℓInit n)
  /-- The independence of the three families of primitives. -/
  families_indep : iIndep (fun k : Fin 3 =>
    if k = 0 then ⨆ i, MeasurableSpace.comap (fun ω => fun t : ℝ => (N i).count t ω) inferInstance
    else if k = 1 then ⨆ j, MeasurableSpace.comap (U j) inferInstance
    else (⨆ n, ⨆ i, MeasurableSpace.comap (fun ω => qInit n ω i) inferInstance) ⊔
      ⨆ n, MeasurableSpace.comap (ℓInit n) inferInstance) P
  /-- The constant `B` of §3. -/
  B : ℕ
  /-- The deterministic limit `q(0)` of the initial occupancy states. -/
  q0 : ℕ → ℝ
  init_space : ∀ᵐ ω ∂P, ∀ n : ℕ, 1 ≤ n → qInit n ω ∈ OccupancySpace
  init_integral : ∀ᵐ ω ∂P, ∀ n : ℕ, 1 ≤ n → ∀ i, ∃ k : ℕ, (n : ℝ) * qInit n ω i = k
  init_mult : ∀ᵐ ω ∂P, ∀ n : ℕ, 1 ≤ n → D.Δ ∣ ℓInit n ω
  init_bound : ∀ᵐ ω ∂P, ∀ n : ℕ, 1 ≤ n → qInit n ω (B + 1) = 0 ∧ ℓInit n ω ≤ B
  init_lim : ∀ᵐ ω ∂P, ∀ i, Tendsto (fun n => qInit n ω i) atTop (𝓝 (q0 i))

namespace Primitives

variable {D : LoadData} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable (prim : Primitives D Ω P)

/-- The arrival process `𝒩^λ_n(t) = 𝒩₀(n ∫₀ᵗ λ(s) ds)`. -/
noncomputable def arrivals (n : ℕ) (ω : Ω) (t : ℝ) : ℕ :=
  (prim.N 0).count ((n : ℝ) * D.cumRate t) ω

/-- The `k`-th jump time `τ_{n,k}` of `𝒩^λ_n` (`k ≥ 1`); `τ_{n,0} = 0`. -/
noncomputable def jumpTime (n : ℕ) (ω : Ω) (k : ℕ) : ℝ :=
  if k = 0 then 0 else sInf {t : ℝ | 0 ≤ t ∧ k ≤ prim.arrivals n ω t}

end Primitives

/-- `Iᵢ(q) = [1 - q(i-1), 1 - q(i))`, `i ≥ 1`. -/
def intI (q : ℕ → ℝ) (i : ℕ) : Set ℝ := Ico (1 - q (i - 1)) (1 - q i)

/-- `Jᵢ(q, j) = [(1 - q(i-1))/(1 - q(j)), (1 - q(i))/(1 - q(j)))` if `q(j) < 1`, and `∅` if
`q(j) = 1`, `1 ≤ i ≤ j`. -/
noncomputable def intJ (q : ℕ → ℝ) (i j : ℕ) : Set ℝ :=
  if q j < 1 then Ico ((1 - q (i - 1)) / (1 - q j)) ((1 - q i) / (1 - q j)) else ∅

open Classical in
/-- The routing indicator `r_{ij}(q, ℓ)` (p. 23) for a selection value `u = Uⱼ`, with
`h = ℓ + Δ`; `i ≥ 1`. -/
noncomputable def route (Δ : ℕ) (u : ℝ) (q : ℕ → ℝ) (ℓ : ℕ) (i : ℕ) : ℝ :=
  if i - 1 < ℓ then (if u ∈ intJ q i ℓ then 1 else 0)
  else if i - 1 < ℓ + Δ then (if q ℓ = 1 ∧ u ∈ intJ q i (ℓ + Δ) then 1 else 0)
  else (if q (ℓ + Δ) = 1 ∧ u ∈ intI q i then 1 else 0)

namespace Primitives

variable {D : LoadData} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable (prim : Primitives D Ω P)

/-- The left limit `q(τ⁻)` of an occupancy path, coordinatewise. -/
noncomputable def qLeft (q : ℝ → ℕ → ℝ) (τ : ℝ) : ℕ → ℝ :=
  fun i => Function.leftLim (fun s => q s i) τ

/-- The arrival counting process `𝒜ₙ(q, ℓ, t, i) = (1/n) ∑_{j=1}^{𝒩^λ_n(t)} r_{ij}(q(τ⁻_{n,j}),
ℓ(τ⁻_{n,j}))` for `i ≥ 1`; the `i = 0` coordinate is `0`. -/
noncomputable def arrivalProc (n : ℕ) (ω : Ω) (q : ℝ → ℕ → ℝ) (ℓ : ℝ → ℕ) (t : ℝ) (i : ℕ) :
    ℝ :=
  if i = 0 then 0 else
    (1 / (n : ℝ)) * ∑ j ∈ Finset.Icc 1 (prim.arrivals n ω t),
      route D.Δ (prim.U j ω) (qLeft q (prim.jumpTime n ω j))
        (Function.leftLim ℓ (prim.jumpTime n ω j)) i

/-- The departure counting process
`𝒟ₙ(q, t, i) = (1/n) 𝒩ᵢ(n ∫₀ᵗ µ i [q(s, i) - q(s, i+1)] ds)` for `i ≥ 1`; the `i = 0`
coordinate is `0`. -/
noncomputable def departureProc (n : ℕ) (ω : Ω) (q : ℝ → ℕ → ℝ) (t : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then 0 else
    (1 / (n : ℝ)) * ((prim.N i).count
      ((n : ℝ) * ∫ s in (0 : ℝ)..t, D.mu * i * (q s i - q s (i + 1))) ω : ℝ)

open Classical in
/-- `(q, ℓ)` is a solution, on `[0, T]` at the outcome `ω`, of the implicit equations (9a)–(9b)
of the `n`-th system with control parameter `αₙ = α`: both paths are càdlàg on `[0, T]`, `q`
takes values in `Q`, and for every `t ∈ [0, T]`
`q(t) = qₙ(0) + 𝒜ₙ(q, ℓ, t) − 𝒟ₙ(q, t)` and
`ℓ(t) = ℓₙ(0) + ∑_{k=1}^{𝒩^λ_n(t)} Δ [𝟙{q(τ⁻, ℓ(τ⁻)) = 1, n q(τ⁻, ℓ(τ⁻) + Δ) ≥ n − 1}
− 𝟙{q(τ⁻, ℓ(τ⁻)) ≤ α}]`, `τ = τ_{n,k}`. -/
def Solves (α : ℝ) (n : ℕ) (ω : Ω) (q : ℝ → ℕ → ℝ) (ℓ : ℝ → ℕ) : Prop :=
  (∀ i, IsCadlagOn (fun t => q t i) D.T) ∧
  IsCadlagOn (fun t => (ℓ t : ℝ)) D.T ∧
  (∀ t ∈ Icc 0 D.T, q t ∈ OccupancySpace) ∧
  (∀ t ∈ Icc 0 D.T, ∀ i,
    q t i = prim.qInit n ω i + prim.arrivalProc n ω q ℓ t i - prim.departureProc n ω q t i) ∧
  (∀ t ∈ Icc 0 D.T,
    (ℓ t : ℝ) = (prim.ℓInit n ω : ℝ) + ∑ k ∈ Finset.Icc 1 (prim.arrivals n ω t),
      (D.Δ : ℝ) *
        ((if qLeft q (prim.jumpTime n ω k) (Function.leftLim ℓ (prim.jumpTime n ω k)) = 1 ∧
              (n : ℝ) * qLeft q (prim.jumpTime n ω k)
                  (Function.leftLim ℓ (prim.jumpTime n ω k) + D.Δ) ≥ (n : ℝ) - 1
            then (1 : ℝ) else 0) -
          (if qLeft q (prim.jumpTime n ω k) (Function.leftLim ℓ (prim.jumpTime n ω k)) ≤ α
            then (1 : ℝ) else 0)))

end Primitives

end UnknownLoads.Refined


