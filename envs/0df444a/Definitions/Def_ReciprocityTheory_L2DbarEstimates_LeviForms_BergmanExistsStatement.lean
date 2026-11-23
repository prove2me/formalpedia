-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
-- name    : ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:28:22.577063+00:00
-- url     : https://prove2.me/theorems/e4bb838c-fee1-487e-878e-b57dca04cbb9
-- title:
--   Bergman Exists Statement
-- statement:
--   Definitions and structural lemmas for Bergman Exists Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/BergmanExistsStatement.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_MinimalSolutionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff ComplexOrder
noncomputable section
def TwBoundStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (X : EtaleStein n M) (ps Ph : M → ℝ) (F0 : M → ℂ) (a b : M → ℝ),
    SmoothR n X.z ps → SmoothR n X.z Ph → (∃ C : ℝ, ∀ x, |Ph x| ≤ C) →
    LeviNonneg n X.z (fun x => ps x + Ph x) →
    Smooth n X.z F0 → wint n X.z F0 ps < ⊤ →
    Measurable a → Measurable b → (∀ x, 0 ≤ a x) → (∀ x, 0 ≤ b x) →
    (∀ (x : M) (ξ : Fin n → ℂ),
      ‖dbarDot n X.z F0 x ξ‖ ^ 2 ≤ a x * (Levi n X.z (fun y => ps y + Ph y) x ξ).re) →
    (∀ (x : M) (ξ : Fin n → ℂ),
      ‖dbarDot n X.z (fun y => (Ph y : ℂ)) x ξ‖ ^ 2 ≤
        b x * (Levi n X.z (fun y => ps y + Ph y) x ξ).re) →
    ∀ F : M → ℂ, IsBergmanProj n X.z ps F0 F →
      ∫⁻ x, ENNReal.ofReal (‖F0 x - F x‖ ^ 2 * Real.exp (Ph x - ps x)) ∂vol n X.z ≤
        ∫⁻ x, ENNReal.ofReal ((Real.sqrt (a x) + ‖F0 x - F x‖ * Real.sqrt (b x)) ^ 2 *
          Real.exp (Ph x - ps x)) ∂vol n X.z
def BergmanExistsStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (X : EtaleStein n M) (ps : M → ℝ) (F0 : M → ℂ),
    SmoothR n X.z ps → Measurable F0 → wint n X.z F0 ps < ⊤ →
    ∃ F : M → ℂ, IsBergmanProj n X.z ps F0 F
def zeroSet {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) : Set M := {x | ∀ i, g i x = 0}
def ev {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (x : M) : ℝ :=
  (∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x) / r ^ 2
def lw {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r ε : ℝ) (x : M) : ℝ :=
  Real.log (ev n g ph r x + ε ^ 2)
def xx {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r ε : ℝ) (x : M) : ℝ :=
  1 + Real.log (1 + ε ^ 2) - lw n g ph r ε x
def eta {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r ε : ℝ) (x : M) : ℝ :=
  xx n g ph r ε x + Real.log (xx n g ph r ε x)
def kap {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r ε : ℝ) (x : M) : ℝ :=
  1 + 1 / xx n g ph r ε x
def twist {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r ε : ℝ) (x : M) : ℝ :=
  -Real.log (eta n g ph r ε x)
def wgt {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph ph2 : M → ℝ) (r : ℝ) (j : ℕ) (δ : ℝ)
    (x : M) : ℝ :=
  ph2 x + ((n : ℝ) + j) * ph x + n * lw n g ph r δ x
def bfun {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r ε : ℝ) (x : M) : ℝ :=
  (xx n g ph r ε x + 1) ^ 2 / ((xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x)
def shell {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r ε : ℝ) : Set M :=
  {x | ε ^ 2 / 2 ≤ ev n g ph r x ∧ ev n g ph r x ≤ ε ^ 2}
def gt {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : Fin n → M → ℂ) (c : M → ℂ)
    (W : M → Set M) (x : M) : ℂ :=
  ∑ᶠ (p : M) (_ : p ∈ zeroSet n g), (W p).indicator (fun y => c p * jac n z g y) x
def cutExt {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : Fin n → M → ℂ)
    (ph : M → ℝ) (r : ℝ) (c : M → ℂ) (W : M → Set M) (χ : ℝ → ℝ) (ε : ℝ) (x : M) : ℂ :=
  (χ (ev n g ph r x / ε ^ 2) : ℂ) * gt n z g c W x
def otNorm {M : Type*} [MeasurableSpace M] (n : ℕ) (z : M → V n) (ph ph2 : M → ℝ) (j : ℕ)
    (F : M → ℂ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖F x‖ ^ 2 * Real.exp (-ph2 x - ((n : ℝ) + j) * ph x)) ∂vol n z
def EvLeviStatement (n : ℕ) (M : Type*) [TopologicalSpace M] : Prop :=
  ∀ (z : M → V n) (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ),
    IsLocalHomeomorph z → (∀ i, Holo n z (g i)) → SmoothR n z ph → r ≠ 0 →
    ∀ (x : M) (ξ : Fin n → ℂ),
      ‖dDot n z (fun y => (ev n g ph r y : ℂ)) x ξ‖ ^ 2 ≤
          ev n g ph r x * ((Levi n z (ev n g ph r) x ξ).re +
            ev n g ph r x * (Levi n z ph x ξ).re) ∧
        0 ≤ (Levi n z (ev n g ph r) x ξ).re + ev n g ph r x * (Levi n z ph x ξ).re
def LogLeviStatement (n : ℕ) (M : Type*) [TopologicalSpace M] : Prop :=
  ∀ (z : M → V n) (g : Fin n → M → ℂ) (ph : M → ℝ) (r ε : ℝ),
    IsLocalHomeomorph z → (∀ i, Holo n z (g i)) → SmoothR n z ph → LeviNonneg n z ph →
    r ≠ 0 → 0 < ε →
    ∀ (x : M) (ξ : Fin n → ℂ),
      ε ^ 2 * ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ ^ 2 ≤
          ev n g ph r x * ((Levi n z (lw n g ph r ε) x ξ).re + (Levi n z ph x ξ).re) ∧
        0 ≤ (Levi n z (lw n g ph r ε) x ξ).re + (Levi n z ph x ξ).re
def TwistLeviStatement (n : ℕ) (M : Type*) [TopologicalSpace M] : Prop :=
  ∀ (z : M → V n) (g : Fin n → M → ℂ) (ph ph2 : M → ℝ) (r : ℝ) (j : ℕ) (ε δ : ℝ),
    IsLocalHomeomorph z → (∀ i, Holo n z (g i)) →
    SmoothR n z ph → LeviNonneg n z ph → SmoothR n z ph2 → LeviNonneg n z ph2 →
    0 < r → 2 ≤ j → 0 < ε → 0 < δ →
    (∀ x, (∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x) ≤ r ^ 2) →
    SmoothR n z (wgt n g ph ph2 r j δ) ∧ SmoothR n z (twist n g ph r ε) ∧
    (∀ (x : M) (ξ : Fin n → ℂ),
      (1 / (xx n g ph r ε x ^ 2 * eta n g ph r ε x) + (kap n g ph r ε x / eta n g ph r ε x) ^ 2) *
          ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ ^ 2 ≤
        (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re) ∧
    (∀ (x : M) (ξ : Fin n → ℂ), ev n g ph r x ≤ ε ^ 2 →
      kap n g ph r ε x * ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ ^ 2 ≤
        eta n g ph r ε x *
          (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re)
def DualStatement (n : ℕ) (M : Type*) [TopologicalSpace M] : Prop :=
  ∀ (z : M → V n) (g : Fin n → M → ℂ) (ph ph2 : M → ℝ) (r : ℝ) (j : ℕ) (ε δ : ℝ),
    IsLocalHomeomorph z → (∀ i, Holo n z (g i)) →
    SmoothR n z ph → LeviNonneg n z ph → SmoothR n z ph2 → LeviNonneg n z ph2 →
    0 < r → 2 ≤ j → 0 < ε → 0 < δ →
    (∀ x, (∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x) ≤ r ^ 2) →
    (∀ (x : M) (ξ : Fin n → ℂ),
      ‖dbarDot n z (fun y => (twist n g ph r ε y : ℂ)) x ξ‖ ^ 2 ≤
        bfun n g ph r ε x *
          (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re) ∧
    (∀ (x : M) (ξ : Fin n → ℂ), ev n g ph r x ≤ ε ^ 2 →
      ‖dbarDot n z (fun y => (twist n g ph r ε y : ℂ)) x ξ‖ ^ 2 ≤
        2 / eta n g ph r ε x *
          (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re) ∧
    (∀ (x : M) (ξ : Fin n → ℂ), ev n g ph r x ≤ ε ^ 2 →
      ‖dbarDot n z (fun y => (ev n g ph r y : ℂ)) x ξ‖ ^ 2 ≤
        4 * ε ^ 4 * eta n g ph r ε x *
          (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re)
def BasicStatement (n : ℕ) (M : Type*) : Prop :=
  ∀ (g : Fin n → M → ℂ) (ph ph2 : M → ℝ) (r : ℝ) (j : ℕ) (ε δ : ℝ),
    0 < r → 0 < ε → (∀ x, (∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x) ≤ r ^ 2) →
    (∀ x, 1 ≤ xx n g ph r ε x ∧ 1 ≤ eta n g ph r ε x ∧ kap n g ph r ε x ≤ 2 ∧
      eta n g ph r ε x ≤ (xx n g ph r ε x + 1) ^ 2) ∧
    (∃ C : ℝ, ∀ x, |twist n g ph r ε x| ≤ C) ∧
    (ε ≤ 1 / 50 → ∀ x, ev n g ph r x ≤ ε ^ 2 → 8 ≤ eta n g ph r ε x) ∧
    (1 ≤ n → 0 < δ → δ ≤ ε → ∀ x,
      Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) ≤
        2 * Real.exp 1 * (1 + ε ^ 2) ^ n * (Real.exp (-wgt n g ph ph2 r j δ x) /
          ((xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x)))
def IsCutoff (χ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ χ ∧ (∀ t, t ≤ 1 / 2 → χ t = 1) ∧ (∀ t, 1 ≤ t → χ t = 0) ∧
    (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) ∧ ∀ t, |deriv χ t| ≤ 3
def CutoffStatement : Prop := ∃ χ : ℝ → ℝ, IsCutoff χ
def PolarStatement (n : ℕ) : Prop :=
  1 ≤ n → ∀ a b : ℝ, 0 < a → a ≤ b →
    ∫⁻ y in {y : V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}, ENNReal.ofReal ((‖y‖ ^ 2) ^ (-(n : ℝ))) =
      ENNReal.ofReal (Real.pi ^ n / (Nat.factorial (n - 1) : ℝ) * Real.log (b / a))
def ShellStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (z : M → V n) (g : Fin n → M → ℂ) (ph ph2 : M → ℝ) (r : ℝ) (j : ℕ) (p : M),
    1 ≤ n → IsLocalHomeomorph z → (∀ i, Holo n z (g i)) → SmoothR n z ph → SmoothR n z ph2 →
    0 < r → p ∈ zeroSet n g → jac n z g p ≠ 0 →
    ∃ W : Set M, IsOpen W ∧ p ∈ W ∧ ∀ τ : ℝ, 0 < τ → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∫⁻ x in W ∩ shell n g ph r ε, ENNReal.ofReal (‖jac n z g x‖ ^ 2 *
          Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) * ev n g ph r x ^ (-(n : ℝ))) ∂vol n z ≤
        ENNReal.ofReal ((1 + τ) * (Real.pi ^ n / (Nat.factorial (n - 1) : ℝ) * Real.log 2) *
          r ^ (2 * n) * Real.exp (-ph2 p - (j : ℝ) * ph p))
def CovStatement (n : ℕ) : Prop :=
  ∀ (W : Set (V n)) (G : V n → V n) (f : V n → ℝ≥0∞), IsOpen W → DifferentiableOn ℂ G W →
    Set.InjOn G W → Measurable f →
    ∫⁻ y in G '' W, f y =
      ∫⁻ y in W, ENNReal.ofReal (‖LinearMap.det (fderiv ℂ G y : V n →ₗ[ℂ] V n)‖ ^ 2) * f (G y)
def VanishStatement (n : ℕ) : Prop :=
  1 ≤ n → ∀ (ρ c C : ℝ) (δ : ℕ → ℝ) (u : ℕ → V n → ℂ),
    0 < ρ → 0 < c → Tendsto δ atTop (𝓝[>] 0) →
    (∀ k, DifferentiableOn ℂ (u k) (ball 0 ρ)) →
    (∀ k, ∫⁻ y in ball (0 : V n) ρ,
      ENNReal.ofReal (‖u k y‖ ^ 2 * (c * ‖y‖ ^ 2 + δ k) ^ (-(n : ℝ))) ≤ ENNReal.ofReal C) →
    Tendsto (fun k => u k 0) atTop (𝓝 0)
def IsLocalData {M : Type*} [TopologicalSpace M] (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ)
    (r : ℝ) (W : M → Set M) (m : ℝ) : Prop :=
  0 < m ∧ ∀ p ∈ zeroSet n g, IsOpen (W p) ∧ p ∈ W p ∧ IsCompact (closure (W p)) ∧
    (∀ x ∈ frontier (W p), m ≤ ev n g ph r x) ∧
    ∀ q ∈ zeroSet n g, q ≠ p → Disjoint (closure (W p)) (closure (W q))
def LocalStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M] : Prop :=
  ∀ (z : M → V n) (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (N : M → Set M),
    IsLocalHomeomorph z → (∀ i, Holo n z (g i)) → SmoothR n z ph → 0 < r →
    (zeroSet n g).Finite → (∀ p ∈ zeroSet n g, jac n z g p ≠ 0) →
    (∀ p ∈ zeroSet n g, IsOpen (N p) ∧ p ∈ N p) →
    ∃ (W : M → Set M) (m : ℝ), IsLocalData n g ph r W m ∧ ∀ p ∈ zeroSet n g, W p ⊆ N p
def ApplyStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (X : EtaleStein n M) (g : Fin n → M → ℂ) (ph ph2 : M → ℝ) (r : ℝ) (j : ℕ) (c : M → ℂ)
    (W : M → Set M) (m : ℝ) (χ : ℝ → ℝ) (ε δ : ℝ),
    (∀ i, Holo n X.z (g i)) → SmoothR n X.z ph → LeviNonneg n X.z ph →
    SmoothR n X.z ph2 → LeviNonneg n X.z ph2 → 0 < r → 2 ≤ j →
    (∀ x, (∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x) ≤ r ^ 2) →
    (zeroSet n g).Finite → (∀ p ∈ zeroSet n g, jac n X.z g p ≠ 0) →
    IsLocalData n g ph r W m → IsCutoff χ →
    0 < ε → ε ≤ 1 / 50 → 2 * ε ^ 2 < m → 0 < δ → δ ≤ ε →
    ∃ F : M → ℂ, Holo n X.z F ∧
      ∫⁻ x, ENNReal.ofReal (‖cutExt n X.z g ph r c W χ ε x - F x‖ ^ 2 *
          (Real.exp (-wgt n g ph ph2 r j δ x) /
            ((xx n g ph r ε x + 1) ^ 2 + eta n g ph r ε x))) ∂vol n X.z ≤
        72 * ∫⁻ x in shell n g ph r ε, ENNReal.ofReal (‖gt n X.z g c W x‖ ^ 2 *
          Real.exp (-wgt n g ph ph2 r j δ x)) ∂vol n X.z
def FixedStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (X : EtaleStein n M) (g : Fin n → M → ℂ) (ph ph2 : M → ℝ) (r : ℝ) (j : ℕ) (c : M → ℂ)
    (W : M → Set M) (m : ℝ) (χ : ℝ → ℝ) (ε : ℝ),
    1 ≤ n → (∀ i, Holo n X.z (g i)) → SmoothR n X.z ph → LeviNonneg n X.z ph →
    SmoothR n X.z ph2 → LeviNonneg n X.z ph2 → 0 < r → 2 ≤ j →
    (∀ x, (∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x) ≤ r ^ 2) →
    (zeroSet n g).Finite → (∀ p ∈ zeroSet n g, jac n X.z g p ≠ 0) →
    IsLocalData n g ph r W m → IsCutoff χ →
    0 < ε → ε ≤ 1 / 50 → 2 * ε ^ 2 < m →
    ∃ F : M → ℂ, Holo n X.z F ∧ (∀ x ∈ zeroSet n g, F x = c x * jac n X.z g x) ∧
      otNorm n X.z ph ph2 j F ≤
        ((ENNReal.ofReal (2 * Real.exp 1 * (1 + ε ^ 2) ^ n * 72) *
            ∫⁻ x in shell n g ph r ε, ENNReal.ofReal (‖gt n X.z g c W x‖ ^ 2 *
              Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) * ev n g ph r x ^ (-(n : ℝ))) ∂vol n X.z)
            ^ (1 / 2 : ℝ) +
          otNorm n X.z ph ph2 j (cutExt n X.z g ph r c W χ ε) ^ (1 / 2 : ℝ)) ^ (2 : ℝ)
def MACofStatement (n : ℕ) : Prop :=
  ∀ (U : Set (V n)) (f : V n → ℝ), IsOpen U → ContDiffOn ℝ ∞ f U →
    ∀ y ∈ U, ∀ k : Fin n,
      ∑ j, wd n j (fun w => (cHess n (fun w' => (f w' : ℂ)) w).adjugate k j) y = 0
end
end ReciprocityTheory.L2DbarEstimates.I


