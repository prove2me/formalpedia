-- Prove2me | Definitions.Def_ResidualsDRO_Wass_Supplement_Assumptions
-- name    : ResidualsDRO_Wass_Supplement_Assumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T02:34:15.963897+00:00
-- url     : https://prove2.me/theorems/9bb54a4c-5777-48be-be44-7e76d07fce05
-- title:
--   Assumptions 3–8, 10–11, 16–18 — regularity, consistency and mean rates
-- statement:
--   These are the additional assumptions for the sequence-level results. They express continuity and growth of c, the alternative Lipschitz or smooth cost conditions, summable risk levels, uniform estimation tails, exponential estimation tails, uniform laws of large numbers, and covariate-averaged rates. Existing Assumptions 1, 2, 9, 12 and 13 are reused.
--
--   $$\sum_n\alpha_n<\infty,\quad\zeta_n(\alpha_n,x)\to0,\qquad \|\|f^*(X)-\widehat f_n(X)\|\|_{L^q}=O_p(n^{-r/2}).$$
--
--   Assumption 17 separately requires the average squared training error to be O_p(n^{-r}); its prediction condition is unsquared. Assumption 18 uses the Lq norm of the decision-uniform empirical second moment and the uniform FI-SAA error. Assumption 16 is a supremum over both x and probability vectors, with literal equality for all sufficiently large n. This eventual reading repairs the impossible positive equality at n=1; the same boundary convention is already part of the published Assumption 12. Gradients are represented by their Euclidean inner-product derivatives within 𝒴. The constants are explicitly quantified, not implicit asymptotic constants.
--
--   Differences from the source:
--
--   - correction: Assumption 16 prints the positive squared-simplex equality without a sample-size threshold → require the identical equality for every sufficiently large positive n; reason: at n=1 every simplex vector is (1) and its squared deviation is zero; pp.25 and 46 use only asymptotic bounds, and the imported Assumption12 already uses this boundary convention
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Mathematical Programming (2023), accepted manuscript, https://doi.org/10.1007/s10107-023-02014-7, pp. 15–19, 21, 25

import Mathlib
import Definitions.Def_ResidualsDRO_Wass_Supplement_Setting

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ResidualsDRO.Wass.Supplement

variable {dx dy dz : ℕ} {Ω : Type*} [MeasurableSpace Ω]

def A3 (M : Model dx dy dz Ω) (p : ℝ) : Prop :=
  (∀ y ∈ M.D.𝒴, LowerSemicontinuousOn (fun z => M.c z y) M.Z) ∧
  (∀ z ∈ M.Z, ContinuousOn (M.c z) M.D.𝒴) ∧
  ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ M.Z, ∀ y ∈ M.D.𝒴, |M.c z y| ≤ B * (1 + ‖y‖ ^ p)

def A4 (M : Model dx dy dz Ω) (L : E dz → ℝ) : Prop :=
  ∀ z ∈ M.Z, 0 ≤ L z ∧ ∀ y ∈ M.D.𝒴, ∀ y' ∈ M.D.𝒴,
    |M.c z y - M.c z y'| ≤ L z * ‖y - y'‖

/-- Assumption 5, p. 16. A gradient is represented by its Euclidean inner-product
linear form; within-set differentiation retains the source's domain 𝒴. -/
def A5 (M : Model dx dy dz Ω) (x : E dx) (p : ℝ)
    (L : E dz → ℝ) (G : E dz → E dy → E dy) : Prop :=
  2 ≤ p ∧ ∀ z ∈ M.Z, 0 ≤ L z ∧
    (∀ y ∈ M.D.𝒴, HasFDerivWithinAt (M.c z) (innerSL ℝ (G z y)) M.D.𝒴 y) ∧
    Integrable (fun e => ‖G z (M.D.fstar x + e)‖ ^ 2) M.Pε ∧
    ∀ y ∈ M.D.𝒴, ∀ y' ∈ M.D.𝒴, ‖G z y - G z y'‖ ≤ L z * ‖y - y'‖

noncomputable def gradMoment (M : Model dx dy dz Ω) (G : E dz → E dy → E dy)
    (x : E dx) (z : E dz) : ℝ := Real.sqrt (∫ e, ‖G z (M.D.fstar x + e)‖ ^ 2 ∂M.Pε)

def A6 (α ζ : ℕ → ℝ) : Prop :=
  (∀ n, 1 ≤ n → 0 < α n ∧ α n < 1) ∧ Summable α ∧ Tendsto ζ atTop (𝓝 0)

/-- Assumption 7 uses an extended supremum so an unbounded uniform error is ∞. -/
noncomputable def predictionSup (M : Model dx dy dz Ω) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ x ∈ M.X, ENNReal.ofReal ‖M.D.fstar x - M.D.fhat n ω x‖

def A7 (M : Model dx dy dz Ω) (P : Measure Ω) (κ : ℕ → ℝ → ℝ) : Prop :=
  ∀ n, 1 ≤ n → ∀ α : ℝ, 0 < α → α < 1 → 0 < κ n α ∧
    P {ω | ENNReal.ofReal (κ n α) < predictionSup M n ω} ≤ ENNReal.ofReal α

def A2 (M : Model dx dy dz Ω) (P : Measure Ω) (p : ℝ) (x : E dx)
    (κ : ℕ → ℝ → ℝ) : Prop :=
  ∀ n, 1 ≤ n → Assumption2 (n := n) P M.D.fstar (M.D.fhat n) (fun i => M.D.xs i) p x (κ n)

def Concentration (M : Model dx dy dz Ω) (P : Measure Ω) (x : E dx)
    (p a c₁ c₂ : ℝ) : Prop :=
  0 < dy ∧ 1 ≤ p ∧ p ≠ (dy : ℝ) / 2 ∧ Assumption1 M.Pε p a ∧
  0 < c₁ ∧ 0 < c₂ ∧ ∀ n, 1 ≤ n →
    Lemma2Bound (n := n) P M.Pε M.D.fstar (fun i => M.D.eps i) x dy p a c₁ c₂

noncomputable def radii (κ : ℕ → ℝ → ℝ) (p a c₁ c₂ : ℝ)
    (dy : ℕ) (α : ℕ → ℝ) (n : ℕ) : ℝ := radius (κ n) c₁ c₂ a p dy n (α n)

/-- All hypotheses of the asymptotic Wasserstein ball model, excluding A3–A5. -/
def WAssumptions (M : Model dx dy dz Ω) (P : Measure Ω) (x : E dx)
    (p a c₁ c₂ : ℝ) (κ : ℕ → ℝ → ℝ) (α : ℕ → ℝ) : Prop :=
  Standing M P x ∧ IID M P ∧ Concentration M P x p a c₁ c₂ ∧ A2 M P p x κ ∧
  A6 α (radii κ p a c₁ c₂ dy α) ∧
  ∀ n, 1 ≤ n → WRegular M x p (radii κ p a c₁ c₂ dy α n) n

/-- Assumption 8 at a fixed x, with constants uniform in sample size. -/
def A8 (M : Model dx dy dz Ω) (P : Measure Ω) (x : E dx) (p : ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → ∃ K K' b b' : ℝ, 0 < K ∧ 0 < K' ∧ 0 < b ∧ 0 < b' ∧
    ∀ n, 1 ≤ n →
      P {ω | t ^ p < ‖M.D.fstar x - M.D.fhat n ω x‖ ^ p} ≤
        ENNReal.ofReal (K * Real.exp (-(n : ℝ) * b)) ∧
      P {ω | t ^ p < (n : ℝ)⁻¹ * ∑ i : Fin n,
        ‖M.D.fstar (M.D.xs i ω) - M.D.fhat n ω (M.D.xs i ω)‖ ^ p} ≤
        ENNReal.ofReal (K' * Real.exp (-(n : ℝ) * b'))

def A10 (M : Model dx dy dz Ω) (P : Measure Ω) (x : E dx) : Prop :=
  Vanishes P (fun n ω => uniformError M (Unified.gstarN M.c M.D x n ω) x)

def A11 (M : Model dx dy dz Ω) (P : Measure Ω) (x : E dx) : Prop :=
  Vanishes P (fun n ω => ENNReal.ofReal ‖M.D.fstar x - M.D.fhat n ω x‖) ∧
  Vanishes P (fun n ω => ENNReal.ofReal ((n : ℝ)⁻¹ * ∑ i : Fin n,
    ‖M.D.fstar (M.D.xs i ω) - M.D.fhat n ω (M.D.xs i ω)‖ ^ 2))

def UAssumptions (M : Model dx dy dz Ω) (P : Measure Ω) (x : E dx)
    (ps : E dx → (n : ℕ) → Set (Fin n → ℝ)) (μ : E dx → ℕ → ℝ)
    (L : E dz → ℝ) (Cζ ρ : ℝ) : Prop :=
  Standing M P x ∧ URegular M ps μ x ∧ Unified.Assumption9 M.c M.D.𝒴 M.Z L ∧
  A10 M P x ∧ A11 M P x ∧ Unified.Assumption12 (ps x) Cζ ρ ∧
  Unified.Assumption13 P M.c M.D x M.Pε M.Z ∧ Tendsto (μ x) atTop (𝓝 0)

/-- Assumption 16 as an eventual equality (p. 25). At n=1 the simplex has zero
squared deviation, so the printed positive equality cannot apply there. -/
def A16 (M : Model dx dy dz Ω) (ps : E dx → (n : ℕ) → Set (Fin n → ℝ))
    (Cζ ρ : ℝ) : Prop :=
  1 < ρ ∧ 0 < Cζ ∧ ∃ N, ∀ n, N ≤ n → 1 ≤ n →
    (⨆ x : M.X, ⨆ p : ps x n, ∑ i, ((p : Fin n → ℝ) i - (n : ℝ)⁻¹) ^ 2) =
      Cζ * (n : ℝ) ^ (-ρ)

def A17 (M : Model dx dy dz Ω) (P : Measure Ω) (q : ℝ≥0∞) (r : ℝ) : Prop :=
  0 < r ∧ r ≤ 1 ∧
  Unified.IsBigOp P (fun n ω => lq M q (fun x => ‖M.D.fstar x - M.D.fhat n ω x‖))
    (fun n => (n : ℝ) ^ (-r / 2)) ∧
  Unified.IsBigOp P (fun n ω => ENNReal.ofReal ((n : ℝ)⁻¹ * ∑ i : Fin n,
    ‖M.D.fstar (M.D.xs i ω) - M.D.fhat n ω (M.D.xs i ω)‖ ^ 2))
    (fun n => (n : ℝ) ^ (-r))

/-- A nonnegative extended function's L^q norm, without converting ∞ to a real. -/
noncomputable def lqExtended (M : Model dx dy dz Ω) (q : ℝ≥0∞)
    (F : E dx → ℝ≥0∞) : ℝ≥0∞ :=
  if q = ⊤ then essSup F M.PX else
    (∫⁻ x, F x ^ q.toReal ∂M.PX) ^ (1 / q.toReal)

def A18 (M : Model dx dy dz Ω) (P : Measure Ω) (q : ℝ≥0∞) : Prop :=
  Unified.IsBigOp P (fun n ω => lqExtended M q (fun x =>
    ⨆ z ∈ M.Z, ENNReal.ofReal (Real.sqrt ((n : ℝ)⁻¹ * ∑ i : Fin n,
      (M.c z (M.D.fstar x + M.D.eps i ω)) ^ 2)))) (fun _ => 1) ∧
  Unified.IsBigOp P (fun n ω => lqExtended M q (fun x =>
    uniformError M (Unified.gstarN M.c M.D x n ω) x)) (fun n => (n : ℝ) ^ (-(1 : ℝ) / 2))

end ResidualsDRO.Wass.Supplement


