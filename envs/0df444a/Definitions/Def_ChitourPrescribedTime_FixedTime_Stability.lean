-- Prove2me | Definitions.Def_ChitourPrescribedTime_FixedTime_Stability
-- name    : ChitourPrescribedTime_FixedTime_Stability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:04:10.293134+00:00
-- url     : https://prove2.me/theorems/54c00432-56c6-465b-8b82-d06cdf45658a
-- title:
--   Solutions and global Lyapunov, asymptotic and fixed-time stability (Definition 1, $\Omega=\mathbb R^n$)
-- statement:
--   Consider a non-autonomous differential equation $\dot x = F(t,x)$ on $\mathbb R^n$, equipped with the Euclidean norm $\|\cdot\|$, where $F:\mathbb R\times\mathbb R^n\to\mathbb R^n$. A **solution** on $[0,\infty)$ is a map $x:[0,\infty)\to\mathbb R^n$ such that, for every $t\ge 0$, the map $\tau\mapsto F(\tau,x(\tau))$ is integrable on $[0,t]$ and
--   $$x(t)=x(0)+\int_0^t F(\tau,x(\tau))\,d\tau .$$
--   Solutions need not be unique, so every notion below quantifies over all solutions.
--
--   Following Definition 1 of the paper with $\Omega=\mathbb R^n$ ("globally"):
--
--   1. The origin is **globally Lyapunov stable** if from every $x_0\in\mathbb R^n$ some solution with $x(0)=x_0$ exists on $[0,\infty)$, and for every $\epsilon>0$ there is $\delta>0$ such that every solution with $\|x(0)\|\le\delta$ satisfies $\|x(t)\|\le\epsilon$ for all $t\ge0$.
--   2. It is **globally asymptotically stable** if moreover $F(t,0)=0$ for $t\ge 0$ and, for all $K>0$ and $\epsilon>0$, there is $T\ge0$ such that every solution with $\|x(0)\|\le K$ satisfies $\|x(t)\|\le\epsilon$ for all $t\ge T$.
--   3. It is **globally fixed-time stable with settling time at most $T_{\rm set}$** if $F(t,0)=0$ for $t\ge0$, it is globally Lyapunov stable, and every solution satisfies $x(t)=0$ for all $t\ge\max(0,T_{\rm set})$.
--
--   The last clause is the paper's "finite-time converging from $\Omega$" together with $\sup_{x_0}\mathcal T(x_0)\le T_{\rm set}$, where $\mathcal T(x_0)=\inf\{T\ge0\mid X(t,x_0)=0\ \forall t\ge T\}$ is the settling time; the set in that infimum is an up-set, so the bound on the supremum is exactly "every solution vanishes after $T_{\rm set}$".
--
--   These are the stability notions in which every result of §4.1 is stated.
--
--   **Formalization Note** States live in `EuclideanSpace ℝ (Fin n)` so that $\|\cdot\|$ is the Euclidean norm. Solutions are Carathéodory solutions in integral form with the integrability requirement written out; values of $x$ at negative times are irrelevant. The paper assumes the origin is an equilibrium ("assumed to be an equilibrium point of $f$"); this is the conjunct $F(t,0)=0$.
-- source:
--   Chitour, Ushirobira, Bouhemou, Stabilization for a Perturbed Chain of Integrators in Prescribed Time, SIAM J. Control Optim. 58 (2020), p. 1025, §2, Definition 1 (a)–(e)

import Mathlib

open MeasureTheory

namespace ChitourPrescribedTime.FixedTime

/-- A (Carathéodory) solution on `[0, ∞)` of the non-autonomous system `ẋ = F(t, x)` on
`ℝ^n` (Euclidean norm), written in integral form: for every `t ≥ 0` the map
`τ ↦ F(τ, x(τ))` is integrable on `[0, t]` and `x(t) = x(0) + ∫₀ᵗ F(τ, x(τ)) dτ`.
Values of `x` at negative times play no role. -/
def IsSol {n : ℕ} (F : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : ℝ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    IntervalIntegrable (fun τ => F τ (x τ)) volume 0 t ∧
      x t = x 0 + ∫ τ in (0 : ℝ)..t, F τ (x τ)

/-- Definition 1(a) with `Ω = ℝ^n` (global Lyapunov stability of the origin): from every
initial condition there is a solution defined for all `t ≥ 0`, and for every `ε > 0` there is
`δ > 0` such that every solution with `‖x(0)‖ ≤ δ` satisfies `‖x(t)‖ ≤ ε` for all `t ≥ 0`. -/
def GloballyLyapunovStable {n : ℕ}
    (F : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  (∀ x0 : EuclideanSpace ℝ (Fin n), ∃ x : ℝ → EuclideanSpace ℝ (Fin n), IsSol F x ∧ x 0 = x0) ∧
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x : ℝ → EuclideanSpace ℝ (Fin n), IsSol F x → ‖x 0‖ ≤ δ →
        ∀ t : ℝ, 0 ≤ t → ‖x t‖ ≤ ε

/-- Definition 1(b) with `Ω = ℝ^n`: the origin is an equilibrium (`F(t, 0) = 0` for `t ≥ 0`),
it is globally Lyapunov stable, and for all `K > 0`, `ε > 0` there is `T ≥ 0` such that every
solution with `‖x(0)‖ ≤ K` satisfies `‖x(t)‖ ≤ ε` for all `t ≥ T`. -/
def GloballyAsymptoticallyStable {n : ℕ}
    (F : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  (∀ t : ℝ, 0 ≤ t → F t 0 = 0) ∧ GloballyLyapunovStable F ∧
    ∀ K : ℝ, 0 < K → ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 ≤ T ∧
      ∀ x : ℝ → EuclideanSpace ℝ (Fin n), IsSol F x → ‖x 0‖ ≤ K →
        ∀ t : ℝ, T ≤ t → ‖x t‖ ≤ ε

/-- Definition 1(c)–(e) with `Ω = ℝ^n`, with settling time at most `Tset`: the origin is an
equilibrium, it is globally Lyapunov stable, and every solution vanishes at every time
`t ≥ max(0, Tset)`. The last clause is `sup_{x₀} 𝒯(x₀) ≤ Tset`, where `𝒯(x₀)` is the settling
time of Definition 1(c), taken over every solution (solutions need not be unique). -/
def GloballyFixedTimeStable {n : ℕ}
    (F : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (Tset : ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → F t 0 = 0) ∧ GloballyLyapunovStable F ∧
    ∀ x : ℝ → EuclideanSpace ℝ (Fin n), IsSol F x →
      ∀ t : ℝ, 0 ≤ t → Tset ≤ t → x t = 0

end ChitourPrescribedTime.FixedTime


