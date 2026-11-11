-- Prove2me | Definitions.Def_MulticalibrationERM_Oracle_ERM
-- name    : MulticalibrationERM_Oracle_ERM
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:49:18.67722+00:00
-- url     : https://prove2.me/theorems/e4c66daa-8e1b-4752-8328-58bd7881a555
-- title:
--   Definition 2.3, Equation (2) — weighted (approximate) ERM oracles, Gaussian follow-the-perturbed-leader, and Reg(T, d, ζ)
-- statement:
--   A **$\xi$-approximate weighted ERM oracle** for a class $G\subseteq\{-1,+1\}^X$ (`ERMOracle X G ξ Ω`; $\xi=0$ is the exact oracle) receives a finite list $(x_1,u_1),\dots,(x_n,u_n)\in X\times\mathbb R$ of inputs with real weights and returns some $g\in G$ with
--   $$\sum_i u_i\,g(x_i)\ \ge\ \max_{g'\in G}\sum_i u_i\,g'(x_i)-\xi .$$
--   Its answer depends only on the list and on an oracle seed $\omega\in\Omega$; every call uses a fresh independent seed of a fixed law $\nu$, so ties (or near-ties) may be broken by any deterministic or randomized rule. A returned auditor is a function on all of $X$ and can be stored and evaluated anywhere. The answer at each input is measurable in (weights, seed), which makes the law of an answer well defined.
--
--   **Gaussian follow-the-perturbed-leader** with scale $\gamma$ draws, on round $t$, independent standard Gaussians $G_{t,1},\dots,G_{t,t-1}$ and makes one oracle call on the past inputs with weights $Z_s+\gamma G_{t,s}$ (`ftplDraw`); $\pi_t$ is the law of the answer and the **mixed prediction** is $\bar h_t(x)=\mathbb E_{g\sim\pi_t}[g(x)]$ (`ftplMixed`, an integral over the Gaussians and the oracle seed). The horizon-$T$ scale is $\gamma=4\sqrt{\log(2T)}$ (`ftplScale`), and
--   $$\mathrm{Reg}(T,d_G,\zeta)=C_0\sqrt{T\,(d_G\log(eT)+\log(1/\zeta))}\,\log^2(2T),$$
--   with the absolute constant $C_0$ a parameter.
-- source:
--   Okoroafor, The Sample Complexity of Multicalibration with an ERM Oracle, supplied 61-page preprint (PDF SHA256 654c7a8127547d76c5a4b6db236ce672c2c09a70d21d56a3981583e1805d0f8d; exact arXiv revision unresolved, not arXiv:2610.14363v1), pp. 13–14, Definitions 2.3–2.4, Equation (2)

import Mathlib
import Definitions.Def_MulticalibrationERM_Oracle_Setting

namespace MulticalibrationERM.Oracle

open MeasureTheory ProbabilityTheory

/-! # Weighted ERM oracles and Gaussian follow-the-perturbed-leader

Okoroafor, *The Sample Complexity of Multicalibration with an ERM Oracle* (supplied preprint,
SHA256 654c7a81…), Section 2.2, pp. 13–14: Definition 2.3, Definition 2.4, Equation (2) and the
regret function `Reg`. -/

variable {X : Type*}

/-- The weighted score `∑_i u_i g(x_i)` of an auditor `g` on the weighted list
`(x_1, u_1), …, (x_n, u_n)`. -/
def score (n : ℕ) (xs : Fin n → X) (u : Fin n → ℝ) (g : X → Bool) : ℝ :=
  ∑ i, u i * pm (g (xs i))

/-- A `ξ`-approximate weighted ERM oracle for a class `G ⊆ {−1, +1}^X` (Definition 2.3;
`ξ = 0` is the exact oracle). It receives a finite list of pairs `(x_i, u_i) ∈ X × ℝ`, given as
its length `n`, the inputs `xs` and the real weights `u`, and returns an auditor of `G` whose
score is within `ξ` of the maximum score over `G`. Its answer depends only on the list and on
an oracle seed `ω ∈ Ω`; every call uses a fresh seed, independent of everything else, so ties
may be broken by any rule, deterministic or randomized. A returned auditor is a function on all of
`X` and can be stored and evaluated at any input. `meas` is the measurability that makes the law
of the answer (as a function of real weights and seed) well defined. -/
structure ERMOracle (X : Type*) (G : Set (X → Bool)) (ξ : ℝ) (Ω : Type*)
    [MeasurableSpace Ω] where
  answer : (n : ℕ) → (Fin n → X) → (Fin n → ℝ) → Ω → (X → Bool)
  mem : ∀ n xs u ω, answer n xs u ω ∈ G
  approx : ∀ n xs u ω, ∀ g ∈ G, score n xs u g ≤ score n xs u (answer n xs u ω) + ξ
  meas : ∀ n (xs : Fin n → X) (x : X),
    Measurable (fun p : (Fin n → ℝ) × Ω => answer n xs p.1 p.2 x)

variable {G : Set (X → Bool)} {ξ : ℝ} {Ω : Type*} [MeasurableSpace Ω]

/-- One oracle call on a list of weighted inputs, with oracle seed `ω`. -/
def ERMOracle.call (O : ERMOracle X G ξ Ω) (ℓ : List (X × ℝ)) (ω : Ω) : X → Bool :=
  O.answer ℓ.length (fun i => (ℓ.get i).1) (fun i => (ℓ.get i).2) ω

/-- The perturbation scale `γ = 4 √(log(2T))` of Gaussian follow-the-perturbed-leader with
horizon `T` (Theorem 2.5). -/
noncomputable def ftplScale (T : ℕ) : ℝ := 4 * Real.sqrt (Real.log (2 * T))

/-- One draw from the Gaussian follow-the-perturbed-leader distribution `π_t` (Equation (2)):
on the `n = t − 1` past inputs `xs` with feedback `zs`, and standard Gaussians `g`, one call to
the oracle on the weights `Z_s + γ G_{t,s}`, with oracle seed `ω`. -/
def ftplDraw (O : ERMOracle X G ξ Ω) (γ : ℝ) (n : ℕ) (xs : Fin n → X) (zs : Fin n → ℝ)
    (g : Fin n → ℝ) (ω : Ω) : X → Bool :=
  O.answer n xs (fun s => zs s + γ * g s) ω

/-- The mixed prediction `h̄_t(x) = E_{g ∼ π_t}[g(x)]` of Gaussian follow-the-perturbed-leader
(Definition 2.4 and Equation (2)): the expectation over independent standard Gaussians
`G_{t,1}, …, G_{t,t−1}` and the oracle seed (law `ν`) of the value at `x` of one draw. -/
noncomputable def ftplMixed (O : ERMOracle X G ξ Ω) (ν : Measure Ω) (γ : ℝ) (n : ℕ)
    (xs : Fin n → X) (zs : Fin n → ℝ) (x : X) : ℝ :=
  ∫ p, pm (ftplDraw O γ n xs zs p.1 p.2 x)
    ∂((Measure.pi fun _ : Fin n => gaussianReal 0 1).prod ν)

/-- The regret function `Reg(T, d_G, ζ) = C₀ √(T (d_G log(eT) + log(1/ζ))) · log²(2T)`
(p. 14), with the absolute constant `C₀` as a parameter. -/
noncomputable def Reg (C₀ : ℝ) (T : ℕ) (dG : ℝ) (ζ : ℝ) : ℝ :=
  C₀ * Real.sqrt (T * (dG * Real.log (Real.exp 1 * T) + Real.log (1 / ζ))) *
    Real.log (2 * T) ^ 2

end MulticalibrationERM.Oracle


