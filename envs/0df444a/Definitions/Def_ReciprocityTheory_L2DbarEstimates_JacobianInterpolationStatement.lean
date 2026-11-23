-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
-- name    : ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:56.70882+00:00
-- url     : https://prove2.me/theorems/5937676c-dc19-48c8-b6ee-42f80f11f203
-- title:
--   Jacobian Interpolation Statement
-- statement:
--   Definitions and structural lemmas for Jacobian Interpolation Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/JacobianInterpolationStatement.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates
open MeasureTheory Metric Filter Topology
open scoped ENNReal ComplexOrder
noncomputable section
def HStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (X : EtaleStein n M) (ph : M → ℝ) (F0 : M → ℂ) (h : M → ℝ≥0∞),
    SmoothR n X.z ph → LeviNonneg n X.z ph → Smooth n X.z F0 → Measurable h →
    (∀ (x : M) (ξ : Fin n → ℂ), ENNReal.ofReal (‖dbarDot n X.z F0 x ξ‖ ^ 2) ≤
      h x * ENNReal.ofReal (Levi n X.z ph x ξ).re) →
    ∃ F : M → ℂ, Holo n X.z F ∧
      wint n X.z (fun x => F0 x - F x) ph ≤
        ∫⁻ x, h x * ENNReal.ofReal (Real.exp (-ph x)) ∂vol n X.z
def SStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (X : EtaleStein n M) (p : ℕ) (g : Fin p → M → ℂ) (ph0 : M → ℝ) (t : ℝ) (f : M → ℂ),
    2 ≤ p → (∀ i, Holo n X.z (g i)) → (∀ x, ∃ i, g i x ≠ 0) →
    SmoothR n X.z ph0 → LeviNonneg n X.z ph0 → (p : ℝ) - 1 < t → Holo n X.z f →
    ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2 * (∑ i, ‖g i x‖ ^ 2) ^ (-(t + 1)) *
        Real.exp (-ph0 x)) ∂vol n X.z < ⊤ →
    ∃ hh : Fin p → M → ℂ, (∀ i, Holo n X.z (hh i)) ∧ (∀ x, f x = ∑ i, g i x * hh i x) ∧
      ∫⁻ x, ENNReal.ofReal ((∑ i, ‖hh i x‖ ^ 2) * (∑ i, ‖g i x‖ ^ 2) ^ (-t) *
          Real.exp (-ph0 x)) ∂vol n X.z ≤
        ENNReal.ofReal (t / (t - ((p : ℝ) - 1))) *
          ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2 * (∑ i, ‖g i x‖ ^ 2) ^ (-(t + 1)) *
            Real.exp (-ph0 x)) ∂vol n X.z
def EXTStatement (n : ℕ) : Prop :=
  ∀ (c : V n) (r : ℝ) (F u : V n → ℂ),
    DifferentiableOn ℂ F (ball c r) →
    DifferentiableOn ℂ u (ball c r \ {y | F y = 0}) →
    ∫⁻ y in ball c r \ {y | F y = 0}, ENNReal.ofReal (‖u y‖ ^ 2) < ⊤ →
    ∃ U : V n → ℂ, DifferentiableOn ℂ U (ball c r) ∧ Set.EqOn U u (ball c r \ {y | F y = 0})
def EXTNullStatement (n : ℕ) : Prop :=
  ∀ (c : V n) (r : ℝ) (F : V n → ℂ),
    DifferentiableOn ℂ F (ball c r) → (∃ y ∈ ball c r, F y ≠ 0) →
    volume (ball c r ∩ {y | F y = 0}) = 0
def MVStatement (n : ℕ) : Prop :=
  ∀ (R : ℝ) (u : V n → ℂ) (ρ : ℝ → ℝ≥0∞),
    DifferentiableOn ℂ u (ball 0 R) → Measurable ρ → (∀ t : ℝ, R ≤ t → ρ t = 0) →
    ENNReal.ofReal (‖u 0‖ ^ 2) * ∫⁻ y : V n, ρ ‖y‖ ≤
      ∫⁻ y : V n, ENNReal.ofReal (‖u y‖ ^ 2) * ρ ‖y‖
def MVBlowupStatement (n : ℕ) : Prop :=
  1 ≤ n →
    Tendsto (fun δ : ℝ => ∫⁻ y in ball (0 : V n) 1, ENNReal.ofReal ((‖y‖ ^ 2 + δ) ^ (-(n : ℝ))))
      (𝓝[>] 0) (𝓝 ⊤)
def MVIntStatement (n : ℕ) : Prop :=
  1 ≤ n → ∀ s : ℝ,
    (∫⁻ y in ball (0 : V n) 1, ENNReal.ofReal ‖y‖ ^ (-2 * s) < ⊤ ↔ s < n)
def LSEStatement (n : ℕ) (M : Type*) [TopologicalSpace M] : Prop :=
  ∀ (z : M → V n), IsLocalHomeomorph z →
    ∀ (p q : ℕ) (ph : Fin p → M → ℝ) (g : Fin q → M → ℂ),
      (∀ i, SmoothR n z (ph i)) → (∀ i, LeviNonneg n z (ph i)) → (∀ j, Holo n z (g j)) →
      (∀ x, 0 < ∑ i, Real.exp (ph i x) + ∑ j, ‖g j x‖ ^ 2) →
      SmoothR n z (fun x => Real.log (∑ i, Real.exp (ph i x) + ∑ j, ‖g j x‖ ^ 2)) ∧
        LeviNonneg n z (fun x => Real.log (∑ i, Real.exp (ph i x) + ∑ j, ‖g j x‖ ^ 2))
def ChainStatement (n : ℕ) (M : Type*) [TopologicalSpace M] : Prop :=
  ∀ (z : M → V n), IsLocalHomeomorph z →
    ∀ (k : ℝ → ℝ) (v : M → ℝ), ContDiff ℝ 2 k → SmoothR n z v →
      ∀ (x : M) (ξ : Fin n → ℂ),
        Levi n z (fun y => k (v y)) x ξ =
          ((deriv k (v x) : ℝ) : ℂ) * Levi n z v x ξ +
            ((deriv (deriv k) (v x) : ℝ) : ℂ) * ((‖dDot n z (fun y => (v y : ℂ)) x ξ‖ ^ 2 : ℝ) : ℂ)
def TWStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (X : EtaleStein n M) (ps Ph : M → ℝ) (F0 : M → ℂ) (a b : M → ℝ),
    SmoothR n X.z ps → SmoothR n X.z Ph → (∃ C : ℝ, ∀ x, |Ph x| ≤ C) →
    LeviNonneg n X.z (fun x => ps x + Ph x) →
    Smooth n X.z F0 → wint n X.z F0 ps < ⊤ →
    Measurable a → Measurable b → (∀ x, 0 ≤ a x) → (∀ x, 0 ≤ b x) → (∀ x, b x ≤ 1) →
    (∀ (x : M) (ξ : Fin n → ℂ),
      ‖dbarDot n X.z F0 x ξ‖ ^ 2 ≤ a x * (Levi n X.z (fun y => ps y + Ph y) x ξ).re) →
    (∀ (x : M) (ξ : Fin n → ℂ),
      ‖dbarDot n X.z (fun y => (Ph y : ℂ)) x ξ‖ ^ 2 ≤
        b x * (Levi n X.z (fun y => ps y + Ph y) x ξ).re) →
    (∃ F : M → ℂ, IsBergmanProj n X.z ps F0 F) ∧
      ∀ F : M → ℂ, IsBergmanProj n X.z ps F0 F →
        ∫⁻ x, ENNReal.ofReal (‖F0 x - F x‖ ^ 2 * Real.exp (Ph x - ps x)) ∂vol n X.z ≤
          ∫⁻ x, ENNReal.ofReal ((Real.sqrt (a x) + ‖F0 x - F x‖ * Real.sqrt (b x)) ^ 2 *
            Real.exp (Ph x - ps x)) ∂vol n X.z
def NORMStatement (n : ℕ) (M : Type*) [TopologicalSpace M] : Prop :=
  ∀ (z : M → V n) (Δ : MvPolynomial (Fin n) ℂ) (u : M → ℂ) (C : ℝ) (m : ℕ),
    MvPolynomial.constantCoeff Δ ≠ 0 →
    IsCoveringMapOn z {y : V n | MvPolynomial.eval (fun i => y i) Δ ≠ 0} →
    (∀ x, MvPolynomial.eval (fun i => z x i) Δ ≠ 0) →
    (∀ y : V n, (z ⁻¹' {y}).Finite) →
    ConnectedSpace M → Holo n z u →
    (∀ x, ‖u x‖ ≤ C * (1 + ‖z x‖ ^ 2) ^ ((m : ℝ) / 2)) →
    (∀ x, z x = 0 → VanishesBeyond n z u x m) →
    u = 0
def ohsawaTakegoshiConstant (n : ℕ) (r : ℝ) : ℝ :=
  280 * Real.pi ^ n / (Nat.factorial (n - 1) : ℝ) * r ^ (2 * n)
def JacobianInterpolationStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (X : EtaleStein n M) (g : Fin n → M → ℂ) (ph ph2 : M → ℝ) (r : ℝ) (j : ℕ) (c : M → ℂ),
    1 ≤ n → 2 ≤ j → 0 < r → (∀ i, Holo n X.z (g i)) →
    SmoothR n X.z ph → LeviNonneg n X.z ph → SmoothR n X.z ph2 → LeviNonneg n X.z ph2 →
    (∀ x, (∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x) ≤ r ^ 2) →
    {x | ∀ i, g i x = 0}.Finite →
    (∀ x, (∀ i, g i x = 0) → jac n X.z g x ≠ 0) →
    ∃ F : M → ℂ, Holo n X.z F ∧ (∀ x, (∀ i, g i x = 0) → F x = c x * jac n X.z g x) ∧
      ∫⁻ x, ENNReal.ofReal (‖F x‖ ^ 2 * Real.exp (-ph2 x - ((n : ℝ) + j) * ph x)) ∂vol n X.z ≤
        ENNReal.ofReal (ohsawaTakegoshiConstant n r) *
          ∑' x : {x : M // ∀ i, g i x = 0},
            ENNReal.ofReal (‖c x‖ ^ 2 * Real.exp (-ph2 x - (j : ℝ) * ph x))
def MAStatement (n : ℕ) : Prop :=
  ∀ (Ω : Set (V n)) (ph v : V n → ℝ),
    IsOpen Ω → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ph Ω → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v → HasCompactSupport v → tsupport v ⊆ Ω →
    ∫ y in Ω, ((cHess n (fun w => ((ph w + v w : ℝ) : ℂ)) y).det -
      (cHess n (fun w => (ph w : ℂ)) y).det) = 0
def DetMonoStatement (n : ℕ) : Prop :=
  ∀ A B : Matrix (Fin n) (Fin n) ℂ, B.PosSemidef → (A - B).PosSemidef → B.det.re ≤ A.det.re
def InhabitedStatement (n : ℕ) : Prop :=
  Nonempty (EtaleStein n (V n))
end
end ReciprocityTheory.L2DbarEstimates


