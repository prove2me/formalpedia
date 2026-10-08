-- Prove2me | Definitions.Def_WorstCaseCVaR_Box_Problems
-- name    : WorstCaseCVaR_Box_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T18:02:29.74432+00:00
-- url     : https://prove2.me/theorems/ea7d9d7e-a706-4e43-b83b-26f159373af0
-- title:
--   Worst-case CVaR minimization (16)–(20) under box uncertainty and the linear program (24)–(30)
-- statement:
--   This file defines the two minimization problems compared in Proposition 2 of Zhu and Fukushima (2009). The data are a loss function $f : \mathbb R^n \times \mathbb R^m \to \mathbb R$, scenarios $y_{[1]}, \dots, y_{[S]} \in \mathbb R^m$, a decision set $\mathcal X \subseteq \mathbb R^n$, a confidence level $\beta$, and the box data $\pi^0, \underline\eta, \overline\eta \in \mathbb R^S$ defining $\mathcal P_\pi^B$ (Eq. (21)).
--
--   **Problem (16)–(20)** with $\mathcal P_\pi = \mathcal P_\pi^B$, in the variables $(x, u, \alpha, \theta) \in \mathbb R^n \times \mathbb R^S \times \mathbb R \times \mathbb R$:
--   $$\begin{aligned} \min\ & \theta \\ \text{s.t. } & x \in \mathcal X, \\ & \alpha + \tfrac{1}{1-\beta}\pi^\top u \le \theta \quad \text{for all } \pi \in \mathcal P_\pi^B, \\ & u_k \ge f(x, y_{[k]}) - \alpha,\quad u_k \ge 0, \quad k = 1, \dots, S. \end{aligned}$$
--
--   **Problem (24)–(30)**, in the variables $(x, u, z, \xi, \omega, \alpha, \theta) \in \mathbb R^n \times \mathbb R^S \times \mathbb R \times \mathbb R^S \times \mathbb R^S \times \mathbb R \times \mathbb R$:
--   $$\begin{aligned} \min\ & \theta \\ \text{s.t. } & x \in \mathcal X, \\ & \alpha + \tfrac{1}{1-\beta}(\pi^0)^\top u + \tfrac{1}{1-\beta}(\overline\eta^\top\xi + \underline\eta^\top\omega) \le \theta, \\ & e z + \xi + \omega = u,\quad \xi \ge 0,\quad \omega \le 0, \\ & u_k \ge f(x, y_{[k]}) - \alpha,\quad u_k \ge 0, \quad k = 1, \dots, S. \end{aligned}$$
--
--   A point **solves** a problem if it is feasible and its $\theta$ is no larger than the $\theta$ of every feasible point. The first problem is the worst-case CVaR minimization over the box; the second removes the inner maximization by LP duality.
--
--   **Formalization Note** Points are the structures `Var16 n S` (fields `x u α θ`) and `Var24 n S` (fields `x u z ξ ω α θ`), with the projection `Var24.toVar16` and the assembly `Var16.withDual`. The paper prints (18) as $\max_{\pi \in \mathcal P_\pi^B} \alpha + \frac{1}{1-\beta}\pi^\top u \le \theta$; it is formalized as the equivalent constraint "for all $\pi \in \mathcal P_\pi^B$", which agrees with the max form whenever the max exists and does not turn into the junk constraint $0 \le \theta$ on an empty box. The factor $\frac1{1-\beta}$ is `(1 - β)⁻¹`; the hypotheses $0 < \beta < 1$ are carried by the theorems, not the definitions.
-- source:
--   Zhu & Fukushima, Worst-Case Conditional Value-at-Risk with Application to Robust Portfolio Management, Oper. Res. 57(5), 2009, p. 1159, problems (16)–(20) and (24)–(30)

import Mathlib
import Definitions.Def_WorstCaseCVaR_Box_DualPair

open Matrix

namespace WorstCaseCVaR.Box

/-- A point `(x, u, α, θ) ∈ ℝⁿ × ℝ^S × ℝ × ℝ` of problem (16)–(20). -/
structure Var16 (n S : ℕ) where
  x : Fin n → ℝ
  u : Fin S → ℝ
  α : ℝ
  θ : ℝ

/-- A point `(x, u, z, ξ, ω, α, θ) ∈ ℝⁿ × ℝ^S × ℝ × ℝ^S × ℝ^S × ℝ × ℝ` of problem (24)–(30). -/
structure Var24 (n S : ℕ) where
  x : Fin n → ℝ
  u : Fin S → ℝ
  z : ℝ
  ξ : Fin S → ℝ
  ω : Fin S → ℝ
  α : ℝ
  θ : ℝ

/-- The projection `(x, u, z, ξ, ω, α, θ) ↦ (x, u, α, θ)`. -/
def Var24.toVar16 {n S : ℕ} (q : Var24 n S) : Var16 n S :=
  ⟨q.x, q.u, q.α, q.θ⟩

/-- The point `(x, u, z, ξ, ω, α, θ)` assembled from `(x, u, α, θ)` and `(z, ξ, ω)`. -/
def Var16.withDual {n S : ℕ} (p : Var16 n S) (d : Dual23 S) : Var24 n S :=
  ⟨p.x, p.u, d.z, d.ξ, d.ω, p.α, p.θ⟩

/-- The feasible set of problem (16)–(20) with `𝒫_π = 𝒫_π^B`, for the loss `f`, scenarios
`y_[1], …, y_[S]` (`ys`), decision set `𝒳` and confidence level `β`:
(17) `x ∈ 𝒳`; (18) `α + (1 − β)⁻¹ πᵀu ≤ θ` for every `π ∈ 𝒫_π^B`;
(19) `u_k ≥ f(x, y_[k]) − α`; (20) `u_k ≥ 0`.
Constraint (18), printed as `max_{π ∈ 𝒫_π^B} α + (1 − β)⁻¹ πᵀu ≤ θ`, is written in its
equivalent `∀ π` form (equivalent whenever the max exists; correct also on an empty box). -/
def feas16 {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (ys : Fin S → Fin m → ℝ)
    (𝒳 : Set (Fin n → ℝ)) (β : ℝ) (π0 ηlo ηhi : Fin S → ℝ) : Set (Var16 n S) :=
  {p | p.x ∈ 𝒳 ∧
    (∀ π ∈ boxSet π0 ηlo ηhi, p.α + (1 - β)⁻¹ * (π ⬝ᵥ p.u) ≤ p.θ) ∧
    (∀ k, f p.x (ys k) - p.α ≤ p.u k) ∧
    (∀ k, 0 ≤ p.u k)}

/-- The feasible set of problem (24)–(30): (25) `x ∈ 𝒳`;
(26) `α + (1 − β)⁻¹ (π⁰)ᵀu + (1 − β)⁻¹ (η̄ᵀξ + η̲ᵀω) ≤ θ`; (27) `e z + ξ + ω = u`;
(28) `ξ ≥ 0`, `ω ≤ 0`; (29) `u_k ≥ f(x, y_[k]) − α`; (30) `u_k ≥ 0`. -/
def feas24 {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (ys : Fin S → Fin m → ℝ)
    (𝒳 : Set (Fin n → ℝ)) (β : ℝ) (π0 ηlo ηhi : Fin S → ℝ) : Set (Var24 n S) :=
  {q | q.x ∈ 𝒳 ∧
    q.α + (1 - β)⁻¹ * (π0 ⬝ᵥ q.u) + (1 - β)⁻¹ * (ηhi ⬝ᵥ q.ξ + ηlo ⬝ᵥ q.ω) ≤ q.θ ∧
    (fun _ => q.z) + q.ξ + q.ω = q.u ∧
    0 ≤ q.ξ ∧ q.ω ≤ 0 ∧
    (∀ k, f q.x (ys k) - q.α ≤ q.u k) ∧
    (∀ k, 0 ≤ q.u k)}

/-- `p` solves (16)–(20): it is feasible and its objective `θ` is minimal over the feasible set. -/
def Solves16 {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (ys : Fin S → Fin m → ℝ)
    (𝒳 : Set (Fin n → ℝ)) (β : ℝ) (π0 ηlo ηhi : Fin S → ℝ) (p : Var16 n S) : Prop :=
  p ∈ feas16 f ys 𝒳 β π0 ηlo ηhi ∧ IsMinOn Var16.θ (feas16 f ys 𝒳 β π0 ηlo ηhi) p

/-- `q` solves (24)–(30): it is feasible and its objective `θ` is minimal over the feasible set. -/
def Solves24 {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (ys : Fin S → Fin m → ℝ)
    (𝒳 : Set (Fin n → ℝ)) (β : ℝ) (π0 ηlo ηhi : Fin S → ℝ) (q : Var24 n S) : Prop :=
  q ∈ feas24 f ys 𝒳 β π0 ηlo ηhi ∧ IsMinOn Var24.θ (feas24 f ys 𝒳 β π0 ηlo ηhi) q

end WorstCaseCVaR.Box


