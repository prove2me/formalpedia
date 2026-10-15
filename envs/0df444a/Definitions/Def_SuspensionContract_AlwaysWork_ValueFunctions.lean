-- Prove2me | Definitions.Def_SuspensionContract_AlwaysWork_ValueFunctions
-- name    : SuspensionContract_AlwaysWork_ValueFunctions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:37.443975+00:00
-- url     : https://prove2.me/theorems/42d8970a-0c8c-4dd0-ab01-cc41e725ddd0
-- title:
--   (39)–(40), p. 25 and (EC.67), Lemma EC.3, p. ec32 — the value functions V_∅, V_I and the auxiliary functions C¹, m, ψ₁, θ̲_K
-- statement:
--   Given parameters as in the model and constants $c_K$, $m_K$, $\underline\theta_K$, define the **suspension-state value function** (39)
--   $$V_\emptyset(w)=\begin{cases}V_{c_K}(w),& w\in[0,\bar w],\\ \bar V-K,& w>\bar w,\end{cases}$$
--   and the **working-state value function** (40)
--   $$V_I(w)=\begin{cases}V_{c_K}(w),& w\in[0,\underline\theta_K],\\ \bar V+m_K(w-\bar w),& w\in(\underline\theta_K,\bar w],\\ \bar V,& w>\bar w,\end{cases}$$
--   where $V_c(w)=\underline v+w+c\,w^{r/\rho}$.
--
--   For $\underline\theta\in[0,\bar w]$ the e-companion introduces (EC.67)
--   $$C^1(\underline\theta)=\frac{\bar V-\underline v-\bar w}{\frac r\rho\,\underline\theta^{\,r/\rho-1}\big[(\frac\rho r-1)\underline\theta+\bar w\big]},\qquad m(\underline\theta)=\frac{(\frac\rho r-1)\underline\theta+\bar V-\underline v}{(\frac\rho r-1)\underline\theta+\bar w},$$
--   and (Lemma EC.3) $\psi_1(\underline\theta)=\bar V-\underline v-\bar w-C^1(\underline\theta)\,\bar w^{\,r/\rho}$. Finally $\underline\theta_K$, as a function of $K$, is the root of $\psi_1(\underline\theta)=K$ in $(0,\bar w)$ (taken as the infimum of the root set).
--
--   $V_\emptyset$ and $V_I$ are the candidate value functions in the medium-switching-cost regime, where the optimal contract never suspends the agent; $C^1$, $m$ and $\psi_1$ reduce the existence of $(c_K,m_K,\underline\theta_K)$ to a one-dimensional root problem.
--
--   **Formalization Note.** Where the branches of (39)–(40) overlap at $\underline\theta_K$ and $\bar w$, the first branch is used; the values agree under (36) and (38). In Lean $0^{x}=0$ for $x\ne0$ and $x/0=0$, so $C^1(0)=0$ whenever $r<\rho$ (Condition 2 gives this), which is the continuous extension used in Lemma EC.3. $\underline\theta_K$ is `sInf` of the root set $\{\underline\theta\in(0,\bar w):\psi_1(\underline\theta)=K\}$, which is $0$ when that set is empty; it is the root whenever the root is unique, which is what Lemma EC.3 asserts.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, p. 25, (39)–(40); p. ec32, EC.3.7, (EC.67) and Lemma EC.3

import Mathlib
import Definitions.Def_SuspensionContract_AlwaysWork_Setting

namespace SuspensionContract.AlwaysWork

namespace Params

variable (P : Params)

/-- The suspension-state value function (39), p. 25:
`V_∅(w) = V_{c_K}(w)` for `w ∈ [0, w̄]` and `V̄ − K` for `w > w̄`. -/
noncomputable def V039 (cK w : ℝ) : ℝ :=
  if w ≤ P.wbar then P.Vc cK w else P.Vbar - P.K

/-- The working-state value function (40), p. 25:
`V_I(w) = V_{c_K}(w)` on `[0, θ̲_K]`, `V̄ + m_K(w − w̄)` on `[θ̲_K, w̄]`, `V̄` for `w > w̄`. -/
noncomputable def VI40 (cK mK θK w : ℝ) : ℝ :=
  if w ≤ θK then P.Vc cK w else if w ≤ P.wbar then P.Vbar + mK * (w - P.wbar) else P.Vbar

/-- `C¹(θ̲) = (V̄ − v̲ − w̄) / (r/ρ · θ̲^{r/ρ−1}[(ρ/r − 1)θ̲ + w̄])` (EC.67), p. ec32 (`Real.rpow`;
at `θ̲ = 0` the denominator is `0` in Lean, so `C¹(0) = 0`, the continuous extension). -/
noncomputable def C1 (θ : ℝ) : ℝ :=
  (P.Vbar - P.vlow - P.wbar) /
    (P.r / P.ρ * θ ^ (P.r / P.ρ - 1) * ((P.ρ / P.r - 1) * θ + P.wbar))

/-- `m(θ̲) = ((ρ/r − 1)θ̲ + V̄ − v̲) / ((ρ/r − 1)θ̲ + w̄)` (EC.67), p. ec32. -/
noncomputable def mOf (θ : ℝ) : ℝ :=
  ((P.ρ / P.r - 1) * θ + P.Vbar - P.vlow) / ((P.ρ / P.r - 1) * θ + P.wbar)

/-- `ψ₁(θ̲) = V̄ − v̲ − w̄ − C¹(θ̲)·(w̄)^{r/ρ}` (Lemma EC.3, p. ec32). -/
noncomputable def psi1 (θ : ℝ) : ℝ :=
  P.Vbar - P.vlow - P.wbar - P.C1 θ * P.wbar ^ (P.r / P.ρ)

/-- `θ̲_K` as a function of `K`: the infimum of the roots of `ψ₁(θ̲) = K` in `(0, w̄)`
(Lemma EC.3 shows there is exactly one for `K ∈ (0, K̄₂)`; `sInf ∅ = 0` otherwise). -/
noncomputable def thetaOf (K : ℝ) : ℝ :=
  sInf {θ : ℝ | θ ∈ Set.Ioo 0 P.wbar ∧ P.psi1 θ = K}

end Params

end SuspensionContract.AlwaysWork


