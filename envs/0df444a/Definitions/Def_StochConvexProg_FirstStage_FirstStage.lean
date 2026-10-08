-- Prove2me | Definitions.Def_StochConvexProg_FirstStage_FirstStage
-- name    : StochConvexProg_FirstStage_FirstStage
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:30.323457+00:00
-- url     : https://prove2.me/theorems/456c5a0b-f0c7-4d1a-813f-5a2acb759439
-- title:
--   F₁, F₂ (2.2)–(2.3), f (3.1), J (3.2), q, j and problem Q, ρ (3.7), Γ (3.10) and the argmin multifunction (pp. 180–188)
-- statement:
--   The objects of §3 of Rockafellar and Wets, seen from the first stage, built on the model $F$ and the integral convention (2.4).
--
--   1. **(2.2)–(2.3), p. 180.** $F_1(x_1,u_1)=f_{10}(x_1)$ if $x_1\in C_1$ and $f_{1i}(x_1)\le u_{1i}$ for all $i$, and $+\infty$ otherwise; $F_2(s,x_1,x_2,u_2)=f_{20}(s,x_1,x_2)$ if $x_2\in C_2$ and $f_{2i}(s,x_1,x_2)\le u_{2i}$ for all $i$, and $+\infty$ otherwise.
--   2. **(3.1), p. 185.** The essential objective of $\mathbf P$: $f(x)=F(x,0)$ for $x=(x_1,x_2)\in X$.
--   3. **(3.2), p. 185.** The first-stage problem induced by $\mathbf P$ minimizes
--   $$J(x_1)=\inf_{x_2\in\mathcal L^\infty_{n_2}} f(x_1,x_2).$$
--   4. **p. 185.** The optimal recourse cost $q(s,x_1)=\inf_{x_2\in\mathbb R^{n_2}}F_2(s,x_1,x_2,0)$, and the intrinsic first-stage problem $\mathbf Q$ minimizes
--   $$j(x_1)=F_1(x_1,0)+\int_S q(s,x_1)\,\sigma(ds),$$
--   with $j(x_1)=+\infty$ unless $F_1(x_1,0)<+\infty$ and the integral is taken under the convention (2.4) (so $j(x_1)=+\infty$ also when $q(\cdot,x_1)$ has no summable majorant). Further $\inf\mathbf Q=\inf_{x_1}j(x_1)$ and $\inf\mathbf P=\inf_{x\in X}f(x)$.
--   5. **(3.7), p. 186.** $\rho(s,x_1)=\inf\{|x_2|\mid F_2(s,x_1,x_2,0)<+\infty\}$, with $|\cdot|$ the Euclidean length and $\rho(s,x_1)=+\infty$ when the set is empty. A point $x_1$ is *intrinsically feasible* if $j(x_1)<+\infty$.
--   6. **(3.10), p. 187.** For fixed $x_1$, $\Gamma(s)=\{x_2\in\mathbb R^{n_2}\mid x_2\in C_2,\ f_{2i}(s,x_1,x_2)\le 0,\ i=1,\dots,m_2\}$.
--   7. **Proof of Theorem 2, p. 188.** For fixed $x_1$ and $s\in S'=\{s\mid \exists x_2,\ F_2(s,x_1,x_2,0)<+\infty\}$, the set of $x_2$ at which the infimum $q(s,x_1)$ of $F_2(s,x_1,\cdot,0)$ is attained; it is taken empty for $s\notin S'$.
--
--   These are the functions compared by Theorems 1 and 2: whether minimizing $j$ (an integral of pointwise optimal recourse costs) is the same as minimizing $J$ (an infimum over essentially bounded recourse functions).
--
--   **Formalization Note** All values are in `EReal` and all infima are complete-lattice infima, so an empty infimum is $+\infty$ (the paper's convention for $\rho$). The guard `F₁ x₁ 0 < ⊤` in $j$ is the paper's "+∞ unless $F_1(x_1,0)<+\infty$"; it also prevents $\top+\bot=\bot$ in `EReal`. The Euclidean length is $\sqrt{\sum_i v_i^2}$, not the sup norm of `Fin n → ℝ`. The two sets the page calls $\Gamma$ are named `Γ` ((3.10), feasible recourses) and `argminSet` (proof of Theorem 2). The integral under the convention (2.4) is the published definition `DupacovaWets.Consistency.expect`: $+\infty$ if $\int\theta^+\,d\sigma=\infty$, and $\int\theta^+\,d\sigma-\int\theta^-\,d\sigma$ (real or $-\infty$) otherwise, with lower Lebesgue integrals of the positive and negative parts; for a measurable $\theta$, $\int\theta^+<\infty$ holds exactly when $\theta$ is majorized almost everywhere by a summable function, so this is the paper's convention.
-- source:
--   Rockafellar and Wets, Stochastic convex programming: basic duality, Pacific J. Math. 62(1) (1976), p. 180 (2.2)–(2.3); p. 185 (3.1), (3.2), q and problem Q; p. 186 (3.7); p. 187 (3.10); p. 188 proof of Theorem 2

import Mathlib
import Definitions.Def_StochConvexProg_FirstStage_Problem
import Definitions.Def_DupacovaWets_Consistency_expect

open MeasureTheory

namespace StochConvexProg.FirstStage

/-- (2.2), p. 180: `F₁(x₁, u₁) = f₁₀(x₁)` if `x₁ ∈ C₁` and `f₁ᵢ(x₁) ≤ u₁ᵢ` for all `i`, `+∞`
otherwise. -/
noncomputable def Problem.F₁ {S : Type*} [MeasurableSpace S] {σ : Measure S} {n₁ n₂ m₁ m₂ : ℕ}
    (pr : Problem S σ n₁ n₂ m₁ m₂) (x₁ : Fin n₁ → ℝ) (u₁ : Fin m₁ → ℝ) : EReal := by
  classical
  exact if x₁ ∈ pr.C₁ ∧ ∀ i, pr.f₁ i x₁ ≤ u₁ i then (pr.f₁₀ x₁ : EReal) else ⊤

/-- (2.3), p. 180: `F₂(s, x₁, x₂, u₂) = f₂₀(s, x₁, x₂)` if `x₂ ∈ C₂` and `f₂ᵢ(s, x₁, x₂) ≤ u₂ᵢ`
for all `i`, `+∞` otherwise. -/
noncomputable def Problem.F₂ {S : Type*} [MeasurableSpace S] {σ : Measure S} {n₁ n₂ m₁ m₂ : ℕ}
    (pr : Problem S σ n₁ n₂ m₁ m₂) (s : S) (x₁ : Fin n₁ → ℝ) (x₂ : Fin n₂ → ℝ)
    (u₂ : Fin m₂ → ℝ) : EReal := by
  classical
  exact if x₂ ∈ pr.C₂ ∧ ∀ i, pr.f₂ i s x₁ x₂ ≤ u₂ i then (pr.f₂₀ s x₁ x₂ : EReal) else ⊤

/-- (3.1), p. 185: the essential objective of `P`, `f(x) = F(x, 0)`. -/
noncomputable def Problem.f {S : Type*} [MeasurableSpace S] {σ : Measure S} {n₁ n₂ m₁ m₂ : ℕ}
    (pr : Problem S σ n₁ n₂ m₁ m₂) (x : StochConvexProg.Duality.XSpace σ n₁ n₂) : EReal :=
  pr.F x 0

/-- (3.2), p. 185: `J(x₁) = inf_{x₂ ∈ ℒ^∞_{n₂}} f(x₁, x₂)`, the first-stage problem induced by `P`. -/
noncomputable def Problem.J {S : Type*} [MeasurableSpace S] {σ : Measure S} {n₁ n₂ m₁ m₂ : ℕ}
    (pr : Problem S σ n₁ n₂ m₁ m₂) (x₁ : Fin n₁ → ℝ) : EReal :=
  ⨅ x₂ : Lp (Fin n₂ → ℝ) ⊤ σ, pr.f (x₁, x₂)

/-- p. 185: `q(s, x₁) = inf_{x₂ ∈ Rⁿ²} F₂(s, x₁, x₂, 0)`, the optimal second-stage cost. -/
noncomputable def Problem.q {S : Type*} [MeasurableSpace S] {σ : Measure S} {n₁ n₂ m₁ m₂ : ℕ}
    (pr : Problem S σ n₁ n₂ m₁ m₂) (s : S) (x₁ : Fin n₁ → ℝ) : EReal :=
  ⨅ x₂ : Fin n₂ → ℝ, pr.F₂ s x₁ x₂ 0

/-- p. 185, problem `Q`: `j(x₁) = F₁(x₁, 0) + ∫_S q(s, x₁) σ(ds)`, the integral taken under the
convention (2.4) (`DupacovaWets.Consistency.expect`: `+∞` unless `q(·, x₁)` is majorized by a
summable function), and `j(x₁) = +∞` unless `F₁(x₁, 0) < +∞`. -/
noncomputable def Problem.j {S : Type*} [MeasurableSpace S] {σ : Measure S} {n₁ n₂ m₁ m₂ : ℕ}
    (pr : Problem S σ n₁ n₂ m₁ m₂) (x₁ : Fin n₁ → ℝ) : EReal := by
  classical
  exact if pr.F₁ x₁ 0 < ⊤ then pr.F₁ x₁ 0 + DupacovaWets.Consistency.expect σ (fun s => pr.q s x₁) else ⊤

/-- `inf Q = inf_{x₁ ∈ Rⁿ¹} j(x₁)`. -/
noncomputable def Problem.infQ {S : Type*} [MeasurableSpace S] {σ : Measure S}
    {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂) : EReal :=
  ⨅ x₁ : Fin n₁ → ℝ, pr.j x₁

/-- `inf P = inf_{x ∈ X} f(x)`. -/
noncomputable def Problem.infP {S : Type*} [MeasurableSpace S] {σ : Measure S}
    {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂) : EReal :=
  ⨅ x : StochConvexProg.Duality.XSpace σ n₁ n₂, pr.f x

/-- The Euclidean length `|v| = (∑ᵢ vᵢ²)^{1/2}` of `v ∈ Rⁿ` (p. 186). -/
noncomputable def eucNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- (3.7), p. 186: `ρ(s, x₁) = inf{|x₂| | F₂(s, x₁, x₂, 0) < +∞}`, `+∞` if the set is empty. -/
noncomputable def Problem.ρ {S : Type*} [MeasurableSpace S] {σ : Measure S} {n₁ n₂ m₁ m₂ : ℕ}
    (pr : Problem S σ n₁ n₂ m₁ m₂) (s : S) (x₁ : Fin n₁ → ℝ) : EReal :=
  ⨅ (x₂ : Fin n₂ → ℝ) (_ : pr.F₂ s x₁ x₂ 0 < ⊤), ((eucNorm x₂ : ℝ) : EReal)

/-- p. 186: `x₁` is intrinsically feasible in the first stage if `j(x₁) < +∞`. -/
def Problem.IntrinsicallyFeasible {S : Type*} [MeasurableSpace S] {σ : Measure S}
    {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂) (x₁ : Fin n₁ → ℝ) : Prop :=
  pr.j x₁ < ⊤

/-- (3.10), p. 187: the feasible recourses `Γ(s) = {x₂ | x₂ ∈ C₂, f₂ᵢ(s, x₁, x₂) ≤ 0 ∀ i}` for a
fixed `x₁`. -/
def Problem.Γ {S : Type*} [MeasurableSpace S] {σ : Measure S} {n₁ n₂ m₁ m₂ : ℕ}
    (pr : Problem S σ n₁ n₂ m₁ m₂) (x₁ : Fin n₁ → ℝ) (s : S) : Set (Fin n₂ → ℝ) :=
  {x₂ | x₂ ∈ pr.C₂ ∧ ∀ i, pr.f₂ i s x₁ x₂ ≤ 0}

/-- Proof of Theorem 2, p. 188: for `s ∈ S′ = {s | ∃ x₂, F₂(s, x₁, x₂, 0) < +∞}` the set of
`x₂` at which the infimum `q(s, x₁)` of `F₂(s, x₁, ·, 0)` is attained; empty off `S′`. (This is
the page's second `Γ`, distinct from (3.10).) -/
def Problem.argminSet {S : Type*} [MeasurableSpace S] {σ : Measure S} {n₁ n₂ m₁ m₂ : ℕ}
    (pr : Problem S σ n₁ n₂ m₁ m₂) (x₁ : Fin n₁ → ℝ) (s : S) : Set (Fin n₂ → ℝ) :=
  {x₂ | pr.F₂ s x₁ x₂ 0 = pr.q s x₁ ∧ pr.q s x₁ < ⊤}

end StochConvexProg.FirstStage


