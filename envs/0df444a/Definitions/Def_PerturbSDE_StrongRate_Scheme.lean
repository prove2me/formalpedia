-- Prove2me | Definitions.Def_PerturbSDE_StrongRate_Scheme
-- name    : PerturbSDE_StrongRate_Scheme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:08:43.905245+00:00
-- url     : https://prove2.me/theorems/412ee5f5-e6a8-4798-8b50-290d9669aa2e
-- title:
--   pp. 4, 6, 17, 19 — partitions 𝒫_T and mesh, the schemes (63), (76) and (8), the exit time τ
-- statement:
--   This file defines the time grids and numerical schemes of Hutzenthaler and Jentzen (arXiv:1401.0295v1). Let $T\in(0,\infty)$, $\mu:\mathbb R^d\to\mathbb R^d$, $\sigma:\mathbb R^d\to\mathbb R^{d\times m}$, a path $W:[0,\infty)\times\Omega\to\mathbb R^m$, and $\psi(v)=v/(1+\|v\|^2)$.
--
--   1. **Partitions** (p. 6). $\mathcal P_T$ consists of $\theta=(t_0,\dots,t_n)$ with $n\in\mathbb N$ and $0=t_0<t_1<\dots<t_n=T$; its mesh is $|\theta|=\max_{0\le k\le n-1}(t_{k+1}-t_k)$.
--   2. **Scheme (63)** (p. 17). For a set $\mathcal O\subseteq\mathbb R^d$, a process $Y$ satisfies (63) on $\theta$ if for every $\omega$, $k\in\{0,\dots,n-1\}$ and $t\in[t_k,t_{k+1}]$,
--   $$Y_t=Y_{t_k}+\mathbb 1_{\{Y_{t_k}\in\mathcal O\}}\,\psi\big(\mu(Y_{t_k})(t-t_k)+\sigma(Y_{t_k})(W_t-W_{t_k})\big).$$
--   3. **Stopped-tamed Euler–Maruyama interpolation (76)** (p. 19): (63) with $\mathcal O=\{x:\|x\|<\exp(|\ln|\theta||^{1/2})\}$.
--   4. **Stopped-tamed Euler–Maruyama scheme (8)** (p. 4). A family $Z^N:\{0,\dots,N\}\times\Omega\to\mathbb R^d$, $N\in\mathbb N$, satisfies (8) if $Z^N_0=X_0$ and
--   $$Z^N_{n+1}=Z^N_n+\mathbb 1_{\{\|Z^N_n\|<\exp(|\ln(T/N)|^{1/2})\}}\,\psi\Big(\mu(Z^N_n)\tfrac TN+\sigma(Z^N_n)\big(W_{(n+1)T/N}-W_{nT/N}\big)\Big)$$
--   for all $n\in\{0,\dots,N-1\}$.
--   5. **Exit time** (p. 17): $\tau=\inf\big(\{T\}\cup\{t\in\{t_0,\dots,t_n\}:Y_t\notin\mathcal O\}\big)$, a minimum over a finite nonempty set.
--
--   The scheme (8) is (76) on the uniform partition with mesh $T/N$, read at the grid points.
--
--   **Formalization Note** The schemes are predicates on given processes ("let $Y$ … satisfy"), required for every $\omega$, exactly as in the paper; they determine the processes. Both indicator conditions are strict inequalities. Time is $\mathbb R_{\ge 0}$.
-- source:
--   Hutzenthaler, Jentzen, arXiv:1401.0295v1, p. 4 (8); p. 6 (𝒫_T); p. 17 (63) and τ; p. 19 (76)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_PerturbSDE_StrongRate_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace PerturbSDE.StrongRate

open EthierKurtz SabanisEuler.Shared

/-- Hutzenthaler–Jentzen, p. 6: an element `θ = (t_0, …, t_n)` of `𝒫_T`, i.e. `n ∈ ℕ = {1, 2, …}`
and `0 = t_0 < t_1 < ⋯ < t_n = T`. -/
structure Partition (T : ℝ≥0) where
  n : ℕ
  one_le_n : 1 ≤ n
  t : Fin (n + 1) → ℝ≥0
  strictMono : StrictMono t
  t_zero : t 0 = 0
  t_last : t (Fin.last n) = T

/-- The mesh `max_{0 ≤ k ≤ n−1} |t_{k+1} − t_k|` of a partition. -/
noncomputable def Partition.mesh {T : ℝ≥0} (θ : Partition T) : ℝ≥0 :=
  Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, θ.one_le_n⟩⟩)
    (fun k : Fin θ.n => θ.t k.succ - θ.t k.castSucc)

open Classical in
/-- Hutzenthaler–Jentzen, p. 17, (63): `Y` satisfies, for every `ω`, every `k ∈ {0, …, n−1}` and
every `t ∈ [t_k, t_{k+1}]`,
`Y_t = Y_{t_k} + 𝟙_{Y_{t_k} ∈ O} ψ(µ(Y_{t_k})(t − t_k) + σ(Y_{t_k})(W_t − W_{t_k}))`,
with `ψ(v) = v / (1 + ‖v‖²)`. -/
def IsIndicatorTamedScheme {d m : ℕ} {Ω : Type*} {T : ℝ≥0} (mu : SDEState d → SDEState d)
    (sigma : SDEState d → Diffusion d m) (W : ℝ≥0 → Ω → SDEState m) (θ : Partition T)
    (O : Set (SDEState d)) (Y : ℝ≥0 → Ω → SDEState d) : Prop :=
  ∀ (k : Fin θ.n) (t : ℝ≥0), θ.t k.castSucc ≤ t → t ≤ θ.t k.succ → ∀ ω,
    Y t ω = Y (θ.t k.castSucc) ω +
      if Y (θ.t k.castSucc) ω ∈ O then
        tame (((t : ℝ) - θ.t k.castSucc) • mu (Y (θ.t k.castSucc) ω) +
          mulVec (sigma (Y (θ.t k.castSucc) ω)) (W t ω - W (θ.t k.castSucc) ω))
      else 0

/-- Hutzenthaler–Jentzen, p. 19, (76): the stopped-tamed Euler–Maruyama interpolation on `θ`,
i.e. (63) with `O = {x : ‖x‖ < exp(|ln(mesh θ)|^{1/2})}` (strict inequality). -/
def IsStoppedTamedScheme {d m : ℕ} {Ω : Type*} {T : ℝ≥0} (mu : SDEState d → SDEState d)
    (sigma : SDEState d → Diffusion d m) (W : ℝ≥0 → Ω → SDEState m) (θ : Partition T)
    (Y : ℝ≥0 → Ω → SDEState d) : Prop :=
  IsIndicatorTamedScheme mu sigma W θ
    {x | ‖x‖ < Real.exp (Real.sqrt |Real.log (θ.mesh : ℝ)|)} Y

/-- Hutzenthaler–Jentzen, p. 4, (8): for every `N ∈ ℕ = {1, 2, …}` and every `ω`,
`Z^N_0 = X_0` and, for `n ∈ {0, …, N−1}`,
`Z^N_{n+1} = Z^N_n + 𝟙_{‖Z^N_n‖ < exp(|ln(T/N)|^{1/2})} ψ(µ(Z^N_n) T/N + σ(Z^N_n)(W_{(n+1)T/N} − W_{nT/N}))`,
with `ψ(v) = v / (1 + ‖v‖²)`. -/
def IsStoppedTamedEuler {d m : ℕ} {Ω : Type*} (mu : SDEState d → SDEState d)
    (sigma : SDEState d → Diffusion d m) (W : ℝ≥0 → Ω → SDEState m) (T : ℝ≥0)
    (X₀ : Ω → SDEState d) (Z : ℕ → ℕ → Ω → SDEState d) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ ω, Z N 0 ω = X₀ ω ∧
    ∀ n < N, Z N (n + 1) ω = Z N n ω +
      if ‖Z N n ω‖ < Real.exp (Real.sqrt |Real.log ((T : ℝ) / N)|) then
        tame (((T : ℝ) / N) • mu (Z N n ω) +
          mulVec (sigma (Z N n ω))
            (W (((n + 1 : ℕ) : ℝ≥0) * T / N) ω - W ((n : ℝ≥0) * T / N) ω))
      else 0

open Classical in
/-- Hutzenthaler–Jentzen, p. 17: `τ = inf({T} ∪ {t ∈ {t_0, …, t_n} : Y_t ∉ O})`, a minimum over a
finite nonempty set. -/
noncomputable def exitTime {Ω : Type*} {d : ℕ} {T : ℝ≥0} (θ : Partition T)
    (O : Set (SDEState d)) (Y : ℝ≥0 → Ω → SDEState d) (ω : Ω) : ℝ≥0 :=
  (insert T ((Finset.univ.filter (fun i : Fin (θ.n + 1) => Y (θ.t i) ω ∉ O)).image θ.t)).min'
    (Finset.insert_nonempty _ _)

end PerturbSDE.StrongRate


