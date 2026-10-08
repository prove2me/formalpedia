-- Prove2me | Definitions.Def_StochApproxDyn_MartingaleNoise_Interpolation
-- name    : StochApproxDyn_MartingaleNoise_Interpolation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T15:47:38.349292+00:00
-- url     : https://prove2.me/theorems/388e8b4f-191f-466a-96d5-49c5796e6ae5
-- title:
--   Step sizes $\gamma_n$, times $\tau_n$, the inverse $m(t)$, and the step processes $\bar U$, $\bar\gamma$ (§4.1)
-- statement:
--   This file sets up the time change of Section 4.1 of Benaïm's notes.
--
--   A **step sequence** is a sequence $\{\gamma_n\}_{n\ge 1}$ of nonnegative numbers with
--   $$\sum_{k\ge1}\gamma_k=\infty,\qquad \lim_{n\to\infty}\gamma_n=0 .$$
--   These are the standing assumptions of Section 4.1 on the step sizes of the scheme $x_{n+1}-x_n=\gamma_{n+1}(F(x_n)+U_{n+1})$.
--
--   From $\gamma$ one builds the times $\tau_0=0$ and $\tau_n=\sum_{i=1}^n\gamma_i$ for $n\ge1$, and their "inverse" $m:\mathbb R_+\to\mathbb N$,
--   $$m(t)=\sup\{k\ge 0:\ t\ge\tau_k\}. \tag{8}$$
--   For a sequence $\{U_n\}_{n\ge1}$ in a set $E$, the piecewise constant process $\bar U$ and the step-size process $\bar\gamma$ are
--   $$\bar U(\tau_n+s)=U_{n+1},\qquad \bar\gamma(\tau_n+s)=\gamma_{n+1}\qquad(n\in\mathbb N,\ 0\le s<\gamma_{n+1}),$$
--   that is, $\bar U(t)=U_{m(t)+1}$ and $\bar\gamma(t)=\gamma_{m(t)+1}$ for $t\ge0$.
--
--   These objects let one compare the discrete scheme with continuous time: the $n$-th step occupies the time interval $[\tau_n,\tau_{n+1})$ of length $\gamma_{n+1}$.
--
--   **Formalization Note** The paper indexes $\gamma$ and $U$ from $1$; in Lean they are sequences on $\mathbb N$ and the values $\gamma_0$, $U_0$ are never used. $m(t)$ is the natural-number supremum of $\{k:\tau_k\le t\}$; under the step-sequence assumptions and $t\ge0$ this set is nonempty and finite, so $m(t)$ is its largest element (Lean's `sSup` on `ℕ` returns $0$ for an empty or unbounded set, which does not occur in that case). A zero step $\gamma_{n+1}=0$ gives an empty interval $[\tau_n,\tau_{n+1})$, consistent with the paper. Only $t\ge 0$ is meaningful for $\bar U$ and $\bar\gamma$.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), DOI 10.1007/BFb0096509, Section 4.1, pp. 11–12 (PDF pp. 12–13), Eq. (7), (8) and the definitions of τ_n, Ū, γ̄

import Mathlib
import Definitions.Def_StochApproxDyn_Interpolation_Scheme

namespace StochApproxDyn.MartingaleNoise

open Filter Topology

/-- Standing assumptions on the step sizes (Benaïm 1999, §4.1, p. 11): `{γ_n}_{n ≥ 1}` is a
sequence of nonnegative numbers with `∑_k γ_k = ∞` and `γ_n → 0`. The paper indexes `γ` from
`1`; the value `γ 0` is never used (the limit `γ_n → 0` does not see it). -/
def IsStepSequence (γ : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 0 ≤ γ (n + 1)) ∧
  Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, γ (i + 1)) atTop atTop ∧
  Tendsto γ atTop (𝓝 0)

/-- The "inverse" of `n ↦ τ_n`, Eq. (8): `m(t) = sup {k ≥ 0 : t ≥ τ_k}`. Under
`IsStepSequence γ` and `t ≥ 0` the set is nonempty (it contains `0`) and bounded (since
`τ_k → ∞`), so `m(t)` is its largest element; `ℕ`'s `sSup` returns `0` on an empty or
unbounded set, which never happens under the standing assumptions. -/
noncomputable def stepIndex (γ : ℕ → ℝ) (t : ℝ) : ℕ :=
  sSup {k : ℕ | StochApproxDyn.Interpolation.tau γ k ≤ t}

/-- The piecewise constant noise process `Ū(τ_n + s) = U_{n+1}` for `0 ≤ s < γ_{n+1}`
(§4.1, p. 12), i.e. `Ū(t) = U_{m(t)+1}` for `t ≥ 0`. Only `t ≥ 0` is meaningful. -/
noncomputable def noisePath {E : Type*} (γ : ℕ → ℝ) (U : ℕ → E) (t : ℝ) : E :=
  U (stepIndex γ t + 1)

/-- The piecewise constant step-size process `γ̄(τ_n + s) = γ_{n+1}` for `0 ≤ s < γ_{n+1}`
(§4.1, p. 12), i.e. `γ̄(t) = γ_{m(t)+1}` for `t ≥ 0`. -/
noncomputable def stepPath (γ : ℕ → ℝ) (t : ℝ) : ℝ :=
  γ (stepIndex γ t + 1)

end StochApproxDyn.MartingaleNoise


