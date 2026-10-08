-- Prove2me | Definitions.Def_GJNSteadyState_Interchange_RBM
-- name    : GJNSteadyState_Interchange_RBM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:47.158982+00:00
-- url     : https://prove2.me/theorems/1fe9331e-ac46-4a9b-831a-2dc9629ba199
-- title:
--   Definition 1, pp. 12–13 — stationary distributions of the (β, Γ, I − P′)-RBM; weak convergence in 𝒟[0, T] with the uniform topology
-- statement:
--   Let $P$ be a substochastic $J\times J$ matrix, $\beta\in\mathbb R^J$ and $\Gamma$ a $J\times J$ covariance matrix. For a continuous input path $W$ with $W(0)\in\mathbb R^J_+$, a pair $(Z,Y)$ solves the **Skorohod problem** (18)–(19) if
--   $$Z(t) = W(t) + [I-P']Y(t)\ge 0,\qquad Y(0)=0,\ Y\text{ nondecreasing},\qquad \int_0^t Z_j(s)\,dY_j(s) = 0$$
--   for all $t\ge0$ and $j$. The **reflected Brownian motion** (RBM) with parameters $(\beta,\Gamma,I-P')$ is $Z$ when $W$ is a Brownian motion with drift $\beta$ and covariance $\Gamma$.
--
--   A probability measure $\nu$ on $\mathbb R^J$ is a **stationary distribution of the $(\beta,\Gamma,I-P')$-RBM** if it is carried by the orthant $\mathbb R^J_+$ and the following holds: whenever $Z(0)\sim\nu$ is independent of a Brownian motion $\xi$ with drift $\beta$, covariance $\Gamma$ and $\xi(0)=0$, and $(Z,Y)$ solves the Skorohod problem for $W=Z(0)+\xi$ almost surely, then $Z(t)\sim\nu$ for every $t\ge0$.
--
--   The file also fixes the mode of convergence of Theorem 4: random paths $X^n$ converge weakly to $X$ in $\mathcal D[0,T]$ with the topology of uniform convergence when, on some probability space, there are copies $Y^n$ of $X^n|_{[0,T]}$ (for all large $n$) and $Y$ of $X|_{[0,T]}$ with $\sup_{0\le t\le T}\|Y^n(t)-Y(t)\|\to0$ almost surely.
--
--   **Formalization Note** Built on the published `Reiman84.QueueLength.Paths`: `IsDriftedBM` (Brownian motion with drift and covariance, $\xi(0)=0$, continuous paths, independent Gaussian increments) and `IsReflectionPair` (row form $z = x + y(I-P)$, which coordinatewise is $Z = W + [I-P']Y$, with the complementarity (19) in the equivalent form "$Y_j$ is constant on intervals where $Z_j>0$"). The requirement that $\nu$ be carried by $\mathbb R^J_+$ is part of the definition; without it any law charging the complement would satisfy the implication vacuously. Weak convergence is written in Skorohod-representation (coupling) form, which on the separable space of continuous limits is equivalent to weak convergence of laws in the uniform topology.
-- source:
--   Gamarnik and Zeevi, Validity of Heavy Traffic Steady-State Approximations in Generalized Jackson Networks, arXiv:math/0410066v2, pp. 12–13, Definition 1, (18)–(19); p. 13, Theorem 3 (stationary distribution); p. 14, Theorem 4 (uniform topology on 𝒟[0, t])

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths

open MeasureTheory Filter Topology Matrix ProbabilityTheory

namespace GJNSteadyState.Interchange

/-!
Gamarnik–Zeevi (2006), Definition 1 (pp. 12–13) and Theorem 3 (p. 13): stationary
distributions of the reflected Brownian motion (RBM) with parameters `(β, Γ, I − P′)` in the
orthant `ℝ₊^J`; and Theorem 4 (p. 14): weak convergence of processes in `𝒟[0, T]` with the
uniform topology. Built on the published `Reiman84.QueueLength.Paths`: `IsDriftedBM` (Brownian
motion with drift and covariance, started at `0`) and `IsReflectionPair` (the Skorohod
problem (18)–(19), row form `z = x + y(I − P)`, which is the paper's `Z = W + [I − P′]Y`).
-/

/-- `ν` is a stationary distribution of the `(β, Γ, I − P′)`-RBM: `ν` is a probability measure
on `ℝ^J` carried by the orthant `ℝ₊^J`, and whenever `Z(0) ∼ ν` is independent of a Brownian
motion `ξ` with drift `β`, covariance `Γ` and `ξ(0) = 0`, and `(Y, Z)` solves the Skorohod
problem (18)–(19) for the input `W = Z(0) + ξ` almost surely, then `Z(t) ∼ ν` for every
`t ≥ 0`. -/
def IsRBMStationary {J : ℕ} (P : Matrix (Fin J) (Fin J) ℝ) (β : Fin J → ℝ)
    (Γ : Matrix (Fin J) (Fin J) ℝ) (ν : Measure (Fin J → ℝ)) : Prop :=
  IsProbabilityMeasure ν ∧ ν {z | ¬ (0 ≤ z)} = 0 ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (Z0 : Ω → Fin J → ℝ)
    (ξ : Ω → ℝ → Fin J → ℝ) (Y Z : Ω → ℝ → Fin J → ℝ),
    Measurable Z0 → Pr.map Z0 = ν → Reiman84.QueueLength.IsDriftedBM β Γ Pr ξ →
    IndepFun Z0 ξ Pr →
    (∀ᵐ ω ∂Pr, Reiman84.QueueLength.IsReflectionPair P (fun t => Z0 ω + ξ ω t) (Y ω) (Z ω)) →
    ∀ t : ℝ, 0 ≤ t → Pr.map (fun ω => Z ω t) = ν

/-- The path `x` restricted to `[0, T]` and extended constantly outside: `t ↦ x(min (max t 0) T)`. -/
noncomputable def onInterval {J : ℕ} (T : ℝ) (x : ℝ → Fin J → ℝ) : ℝ → Fin J → ℝ :=
  fun t => x (min (max t 0) T)

/-- Weak convergence `Xⁿ ⇒ X` of random paths on `[0, T]` in `𝒟[0, T]` with the topology of
uniform convergence (Theorem 4, p. 14), in coupling (Skorohod representation) form: there is a
probability space carrying paths `Yⁿ`, `Y` with `Yⁿ` distributed as `Xⁿ` restricted to
`[0, T]` for all large `n`, `Y` distributed as `X` restricted to `[0, T]`, and
`sup_{0 ≤ t ≤ T} ‖Yⁿ(t) − Y(t)‖ → 0` almost surely. -/
def WeakConvUnif {J : ℕ} (T : ℝ) {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (X : ∀ n, Ω n → ℝ → Fin J → ℝ)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (X' : Ω' → ℝ → Fin J → ℝ) : Prop :=
  ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (Q : Measure Ω₀) (Y : ℕ → Ω₀ → ℝ → Fin J → ℝ)
    (Y' : Ω₀ → ℝ → Fin J → ℝ),
    IsProbabilityMeasure Q ∧ (∀ n, Measurable (Y n)) ∧ Measurable Y' ∧
    (∀ᶠ n in atTop, Q.map (Y n) = (P n).map (fun ω => onInterval T (X n ω))) ∧
    Q.map Y' = P'.map (fun ω => onInterval T (X' ω)) ∧
    ∀ᵐ ω ∂Q, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖Y n ω t - Y' ω t‖ < ε

end GJNSteadyState.Interchange


