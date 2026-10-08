-- Prove2me | Definitions.Def_WeakMFG_Approx_Empirical
-- name    : WeakMFG_Approx_Empirical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:32.915602+00:00
-- url     : https://prove2.me/theorems/fc683e44-a348-47ac-9380-e76558d3ac26
-- title:
--   Empirical measures $e_n$ and $q^n$, empirical measurability (Definition 3.1) and Assumption (F)
-- statement:
--   For $n\ge1$ paths $x=(x_1,\dots,x_n)\in\mathcal C^n$ the **empirical measure** is $e_n(x)=\frac1n\sum_{j=1}^n\delta_{x_j}$, an element of $\mathcal P_\psi(\mathcal C)$; for $a=(a^1,\dots,a^n)\in A^n$ the empirical control law is $q^n(a)=\frac1n\sum_{i=1}^n\delta_{a^i}\in\mathcal P(A)$.
--
--   **Definition 3.1.** Given measurable spaces $E$ and $F$, a function $F:\mathcal P(\mathcal C)\times E\to F$ is *empirically measurable* if $\mathcal C^n\times E\ni(x,y)\mapsto F(e_n(x),y)$ is jointly measurable for all $n\ge1$.
--
--   **Assumption (F).**
--   1. (F.1) $b=b(t,x,a)$ has no mean field term;
--   2. (F.2) $f(t,x,\mu,q,a)=f(t,x,\mu^t,q,a)$ for all $(t,x,\mu,q,a)$, where $\mu^t$ is the image of $\mu$ under $x\mapsto x_{\cdot\wedge t}$;
--   3. (F.3) $b$, $f$ and $g$ are empirically measurable, using the progressive $\sigma$-field on $[0,T]\times\mathcal C$ and Borel $\sigma$-fields elsewhere;
--   4. (F.4) for each $(t,x)$, the maps $\mathcal P_\psi(\mathcal C)\times\mathcal P(A)\times A\ni(\mu,q,a)\mapsto f(t,x,\mu,q,a)$ and $\mathcal P_\psi(\mathcal C)\ni\mu\mapsto g(x,\mu)$ are continuous at each point with $\mu\sim\mathcal X$;
--   5. (F.5) there is $c>0$ such that, for all $(t,x,\mu,q,a)$,
--   $$|g(x,\mu)|+|f(t,x,\mu,q,a)|\le c\Big(\psi(x)+\int\psi\,d\mu\Big).$$
--
--   Assumption (F) is what the finite-player approximation of §4 needs on top of (S) and (C); the continuity in (F.4) is genuine (topological) continuity, which is stronger than the sequential continuity of assumption (E).
--
--   **Formalization Note** (F.2) is stated for every element of $\mathcal P_\psi(\mathcal C)$ whose underlying measure is the image $\mu^t$, so it does not presuppose $\mu^t\in\mathcal P_\psi(\mathcal C)$. In (F.3) the time variable ranges over $[0,\infty)$ with the progressive $\sigma$-field of the canonical filtration, $\mathcal P(A)$ carries the Borel $\sigma$-field of its weak topology, and $A$ its subspace Borel $\sigma$-field. In (F.4) the topologies are $\tau_\psi$, the weak topology and the subspace topology of $A$.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), §3.1, p. 8, e_n and Definition 3.1; §4, p. 12, Assumption (F); p. 13, q^n

import Mathlib
import Definitions.Def_WeakMFG_Approx_Hyp

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace WeakMFG.Approx

variable {d : ℕ} {T : ℝ≥0} {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA]
  [MeasurableSpace EA] [BorelSpace EA]

/-- The empirical measure `e_n(x) = (1/n) Σ_j δ_{x_j}` of `n ≥ 1` paths (p. 8, (1.2)); it lies in
`P_ψ(C)` because `ψ` is finite-valued. -/
noncomputable def empPath {ψ : WeakMFG.Existence.Path d T → ℝ} {n : ℕ} [NeZero n] (x : Fin n → WeakMFG.Existence.Path d T) :
    Ppsi ψ where
  μ := (n : ℝ≥0∞)⁻¹ • ∑ j, Measure.dirac (x j)
  isProb := ⟨by
    simp [Measure.smul_apply, Finset.sum_apply,
      ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 (NeZero.ne n)) (ENNReal.natCast_ne_top n)]⟩
  integ := by
    rw [lintegral_smul_measure, lintegral_finsetSum_measure]
    simp only [lintegral_dirac]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (by simpa using Nat.pos_of_ne_zero (NeZero.ne n)))
      (ENNReal.sum_lt_top.2 fun _ _ => ENNReal.ofReal_lt_top)

/-- The empirical control law `qⁿ(a) := (1/n) Σ_i δ_{aⁱ}` for `a ∈ Aⁿ`, `n ≥ 1` (p. 13). -/
noncomputable def empCtrl {A : Set EA} {n : ℕ} [NeZero n] (a : Fin n → A) : PA A :=
  ⟨(n : ℝ≥0∞)⁻¹ • ∑ j, Measure.dirac (a j), ⟨by
    simp [Measure.smul_apply, Finset.sum_apply,
      ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 (NeZero.ne n)) (ENNReal.natCast_ne_top n)]⟩⟩

/-- (F.1), p. 12: `b = b(t, x, a)` has no mean field term. -/
def F1 {ψ : WeakMFG.Existence.Path d T → ℝ} (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ)) : Prop :=
  ∃ b₀ : ℝ≥0 → WeakMFG.Existence.Path d T → EA → (Fin d → ℝ), ∀ t x μ a, b t x μ a = b₀ t x a

/-- (F.2), p. 12: `f(t, x, μ, q, a) = f(t, x, μ^t, q, a)`, where `μ^t` is the image of `μ` under
`x ↦ x_{·∧t}`. Stated for every `μ' ∈ P_ψ(C)` whose underlying measure is that image. -/
def F2 {ψ : WeakMFG.Existence.Path d T → ℝ} {A : Set EA} (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) :
    Prop :=
  ∀ t x (μ μ' : Ppsi ψ) q a, μ'.μ = μ.μ.map (stopAt t) → f t x μ q a = f t x μ' q a

/-- (F.3), p. 12: `b`, `f`, `g` are empirically measurable (Definition 3.1, p. 8: for every
`n ≥ 1` the map `(x, y) ↦ F(e_n(x), y)` on `Cⁿ × E` is jointly measurable), using the progressive
σ-field of the canonical filtration on `[0, T] × C` (here `ℝ≥0 × C`) and Borel σ-fields on
`Cⁿ`, `C`, `P(A)` (weak topology) and `A`. -/
def F3 {ψ : WeakMFG.Existence.Path d T → ℝ} {A : Set EA} (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ) : Prop :=
  (∀ (n : ℕ) [NeZero n],
    Measurable[(progSigma (pathFilt (d := d) (T := T))).prod
        (MeasurableSpace.prod MeasurableSpace.pi (inferInstance : MeasurableSpace A))]
      (fun p : (ℝ≥0 × WeakMFG.Existence.Path d T) × (Fin n → WeakMFG.Existence.Path d T) × A =>
        b p.1.1 p.1.2 (empPath p.2.1) (p.2.2 : EA))) ∧
  (∀ (n : ℕ) [NeZero n],
    Measurable[(progSigma (pathFilt (d := d) (T := T))).prod
        (MeasurableSpace.prod MeasurableSpace.pi
          ((borel (PA A)).prod (inferInstance : MeasurableSpace A)))]
      (fun p : (ℝ≥0 × WeakMFG.Existence.Path d T) × (Fin n → WeakMFG.Existence.Path d T) × PA A × A =>
        f p.1.1 p.1.2 (empPath p.2.1) p.2.2.1 (p.2.2.2 : EA))) ∧
  (∀ (n : ℕ) [NeZero n],
    Measurable (fun p : WeakMFG.Existence.Path d T × (Fin n → WeakMFG.Existence.Path d T) => g p.1 (empPath p.2)))

/-- (F.4), p. 12: for each `(t, x)`, `(μ, q, a) ↦ f(t, x, μ, q, a)` on `P_ψ(C) × P(A) × A` and
`μ ↦ g(x, μ)` on `P_ψ(C)` are continuous (topologies `τ_ψ(C)`, weak, subspace) at each point with
`μ ∼ 𝒳`. -/
def F4 {ψ : WeakMFG.Existence.Path d T → ℝ} {A : Set EA} (law : Measure (WeakMFG.Existence.Path d T))
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ) : Prop :=
  (∀ t x (μ : Ppsi ψ) (q : PA A) (a : A), WeakMFG.Existence.MEquiv μ.μ law →
    ContinuousAt (fun p : Ppsi ψ × PA A × A => f t x p.1 p.2.1 (p.2.2 : EA)) (μ, q, a)) ∧
  ∀ x (μ : Ppsi ψ), WeakMFG.Existence.MEquiv μ.μ law → ContinuousAt (fun ν : Ppsi ψ => g x ν) μ

/-- (F.5), p. 12: there is `c > 0` with `|g(x, μ)| + |f(t, x, μ, q, a)| ≤ c (ψ(x) + ∫ ψ dμ)`. -/
def F5 {ψ : WeakMFG.Existence.Path d T → ℝ} {A : Set EA} (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ)
    (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ) : Prop :=
  ∃ c > (0 : ℝ), ∀ t x μ q, ∀ a ∈ A, |g x μ| + |f t x μ q a| ≤ c * (ψ x + ∫ y, ψ y ∂μ.μ)

/-- Assumption (F), p. 12, with `𝒳 = law`. -/
def CondF {ψ : WeakMFG.Existence.Path d T → ℝ} {A : Set EA} (law : Measure (WeakMFG.Existence.Path d T))
    (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ) : Prop :=
  F1 b ∧ F2 f ∧ F3 b f g ∧ F4 law f g ∧ F5 f g

end WeakMFG.Approx


