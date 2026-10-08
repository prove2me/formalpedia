-- Prove2me | Definitions.Def_ZhangBSDE_Scheme_BackwardScheme
-- name    : ZhangBSDE_Scheme_BackwardScheme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:02:52.877772+00:00
-- url     : https://prove2.me/theorems/e2826e26-75d6-447b-8720-4468eac0cbaa
-- title:
--   (5.1)–(5.2), pp. 479, 482 — the backward scheme (Y^π, Z^π), Z^{π,1}, and the step processes Ŷ^π, Ẑ^π
-- statement:
--   Let $\pi:0=t_0<\dots<t_n=T$, let $X^\pi_{t_i}$ be the Euler grid values, and let $\xi^\pi\in L^2(\mathcal F_T)$.
--
--   1. **$Z^{\pi,1}$** (5.2). For a process $Z^\pi$,
--   $$Z^{\pi,1}_{t_i} = \frac1{\Delta t_{i+1}}\,E\Big\{\int_{t_i}^{t_{i+1}}Z^\pi_r\,dr\,\Big|\,\mathcal F_{t_i}\Big\},\quad i=0,\dots,n-1,\qquad Z^{\pi,1}_{t_n}=0.$$
--   2. **The scheme** (5.1). A pair $(Y^\pi,Z^\pi)$ solves the scheme with terminal value $\xi^\pi$ if $Z^\pi$ is progressively measurable with $E\int_0^T|Z^\pi_r|^2dr<\infty$, $Y^\pi$ is adapted, $Y^\pi_{t_n}=\xi^\pi$ almost surely, and for $i=n,n-1,\dots,1$ and every $t\in[t_{i-1},t_i)$, almost surely,
--   $$Y^\pi_t = Y^\pi_{t_i}+f\big(t_i,X^\pi_{t_i},Y^\pi_{t_i},Z^{\pi,1}_{t_i}\big)\,\Delta t_i-\int_t^{t_i}Z^\pi_r\,dW_r .$$
--   3. **Step processes** (p. 482). $\hat Y^\pi_t = Y^\pi_{t_{i-1}}$ and $\hat Z^\pi_t=Z^{\pi,1}_{t_{i-1}}$ for $t\in[t_{i-1},t_i)$; at $T$, $\hat Y^\pi_T=Y^\pi_T$ and $\hat Z^\pi_T=Z^{\pi,1}_{t_n}=0$.
--
--   Given $\xi^\pi$, the scheme determines $Y^\pi$ at the grid points and $Z^\pi$ ($dt\otimes dP$-a.e.) by backward induction; $(\hat Y^\pi,\hat Z^\pi)$ is the numerical approximation of $(Y,Z)$ whose error Theorems 5.6 and 6.1 bound.
--
--   **Formalization Note** $Z^{\pi,1}$, $\hat Y^\pi$ and $\hat Z^\pi$ are constructed from $Z^\pi$ and $Y^\pi$; only $(Y^\pi,Z^\pi)$ is quantified, as a solution of (5.1). The conditional expectation is Mathlib's `condExp` with respect to the augmented filtration. The values at $T$ are a convention (the paper defines the step processes on $[t_{i-1},t_i)$); they affect only a single time point except in $\sup_t$, where $\hat Y^\pi_T=\xi^\pi$ is the natural choice.
-- source:
--   Zhang (2004), Ann. Appl. Probab. 14, §5, p. 479, (5.1)–(5.2); p. 482, definition of Ŷ^π, Ẑ^π

import Mathlib
import Definitions.Def_ZhangBSDE_Scheme_FBSDE
import Definitions.Def_ZhangBSDE_Scheme_Euler

namespace ZhangBSDE.Scheme

open MeasureTheory Set Peng1990.SMP
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ} {T : ℝ≥0}

/-- `Z^{π,1}_{t_i}` of (5.2) (p. 479):
`Z^{π,1}_{t_i} ≜ (1/Δt_{i+1}) E{∫_{t_i}^{t_{i+1}} Z^π_r dr | 𝓕_{t_i}}` for `i = 0, …, n − 1`, and
`Z^{π,1}_{t_n} = 0` (and `0` for `i > n`). -/
noncomputable def Z1 (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (π : Partition T)
    (Zπ : ℝ≥0 → Ω → ℝ) (i : ℕ) : Ω → ℝ :=
  if i < π.n then
    fun ω => (1 / π.Δt (i + 1)) *
      (P[fun ω' => ∫ r in Icc (π.tt i : ℝ) (π.tt (i + 1)), Zπ r.toNNReal ω' | 𝓕 (π.tt i)]) ω
  else 0

/-- `(Y^π, Z^π)` solves the backward scheme (5.1)–(5.2) (p. 479) with terminal value `ξ^π`:
`Z^π ∈ L²(𝔽)`, `Y^π` is adapted, `Y^π_{t_n} = ξ^π` a.s., and for an Itô integral
`J = ∫₀^· Z^π dW`, every `i = n, …, 1` and every `t ∈ [t_{i−1}, t_i)`, almost surely,
`Y^π_t = Y^π_{t_i} + f(t_i, X^π_{t_i}, Y^π_{t_i}, Z^{π,1}_{t_i}) Δt_i − ∫_t^{t_i} Z^π_r dW_r`,
where `X^π_{t_i}` is the Euler scheme (`eulerGrid`) and `Z^{π,1}` is `Z1`. -/
def IsBackwardScheme (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (W : ℝ≥0 → Ω → ℝ) (π : Partition T) (x : EuclideanSpace ℝ (Fin d))
    (b σ : ℝ≥0 → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (f : ℝ≥0 → EuclideanSpace ℝ (Fin d) → ℝ → ℝ → ℝ)
    (ξπ : Ω → ℝ) (Yπ Zπ : ℝ≥0 → Ω → ℝ) : Prop :=
  L2F 𝓕 P T Zπ ∧ StronglyAdapted 𝓕 Yπ ∧ (∀ᵐ ω ∂P, Yπ T ω = ξπ ω) ∧
    ∃ J : ℝ≥0 → Ω → ℝ, IsItoIntegral 𝓕 P T W Zπ J ∧
      ∀ i ∈ Finset.Icc 1 π.n, ∀ t : ℝ≥0, π.tt (i - 1) ≤ t → t < π.tt i →
        ∀ᵐ ω ∂P, Yπ t ω = Yπ (π.tt i) ω
          + f (π.tt i) (eulerGrid π x b σ W i ω) (Yπ (π.tt i) ω) (Z1 𝓕 P π Zπ i ω) * π.Δt i
          - (J (π.tt i) ω - J t ω)

/-- The step process `Ŷ^π_t ≜ Y^π_{t_{i−1}}` for `t ∈ [t_{i−1}, t_i)` (p. 482), and
`Ŷ^π_T = Y^π_{t_n} = Y^π_T`. -/
noncomputable def Yhat (π : Partition T) (Yπ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Yπ (π.tt (π.gridIndex t)) ω

/-- The step process `Ẑ^π_t ≜ Z^{π,1}_{t_{i−1}}` for `t ∈ [t_{i−1}, t_i)` (p. 482), and
`Ẑ^π_T = Z^{π,1}_{t_n} = 0`. -/
noncomputable def Zhat (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (π : Partition T)
    (Zπ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Z1 𝓕 P π Zπ (π.gridIndex t) ω

end ZhangBSDE.Scheme


