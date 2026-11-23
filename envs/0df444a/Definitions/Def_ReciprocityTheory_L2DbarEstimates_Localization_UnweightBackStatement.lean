-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
-- name    : ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:25:40.764157+00:00
-- url     : https://prove2.me/theorems/4de297c9-bb21-4253-b272-efd6cc05e6eb
-- title:
--   Unweight Back Statement
-- statement:
--   Definitions and structural lemmas for Unweight Back Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightBackStatement.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_BasicIdentityStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
def wvol {M : Type*} [MeasurableSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ) : Measure M :=
  (vol n z).withDensity (fun x => ENNReal.ofReal (Real.exp (-ph x)))
def SmoothForm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → V n) : Prop :=
  ∀ j, Smooth n z (fun x => f x j)
def dbarF {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : M → ℂ) : M → V n :=
  fun x => WithLp.toLp 2 (fun j => db n z j g x)
def divF {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → V n) : M → ℂ :=
  fun x => ∑ j, d n z j (fun y => f y j) x
def wedge {n : ℕ} (a b : Fin n → ℂ) : Fin n → Fin n → ℂ :=
  fun j k => a j * b k - a k * b j
def dbarSq {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (u : M → ℂ) (x : M) : ℝ :=
  ∑ j, ‖db n z j u x‖ ^ 2
def w1 {M : Type*} (ph ψ : M → ℝ) : M → ℝ := fun x => ph x - 2 * ψ x
def w2 {M : Type*} (ph ψ : M → ℝ) : M → ℝ := fun x => ph x - ψ x
def nV {M : Type*} [MeasurableSpace M] (n : ℕ) (z : M → V n) (f : M → V n) (ph : M → ℝ) :
    ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2 * Real.exp (-ph x)) ∂vol n z
def n2 {M : Type*} [MeasurableSpace M] (n : ℕ) (z : M → V n) (σ : M → Fin n → Fin n → ℂ)
    (ph : M → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (sq2 n (σ x) * Real.exp (-ph x)) ∂vol n z
def ipV {M : Type*} [MeasurableSpace M] (n : ℕ) (z : M → V n) (v f : M → V n) (ph : M → ℝ) :
    ℂ :=
  ∫ x, ⟪v x, f x⟫_ℂ * (Real.exp (-ph x) : ℂ) ∂vol n z
def MemWeightedL2 {M : Type*} [MeasurableSpace M] (n : ℕ) (z : M → V n) (u : M → ℂ) (ph : M → ℝ) :
    Prop :=
  AEStronglyMeasurable u (vol n z) ∧ wint n z u ph < ⊤
def MemWeightedL2OneForm {M : Type*} [MeasurableSpace M] (n : ℕ) (z : M → V n) (f : M → V n) (ph : M → ℝ) :
    Prop :=
  AEStronglyMeasurable f (vol n z) ∧ nV n z f ph < ⊤
def MemWeightedL2TwoForm {M : Type*} [MeasurableSpace M] (n : ℕ) (z : M → V n) (σ : M → Fin n → Fin n → ℂ)
    (ph : M → ℝ) : Prop :=
  AEStronglyMeasurable σ (vol n z) ∧ n2 n z σ ph < ⊤
def LocalL2Isometry {M E : Type*} [TopologicalSpace M] [MeasurableSpace M] [NormedAddCommGroup E]
    (μ : Measure M) (f : M → E) : Prop :=
  AEStronglyMeasurable f μ ∧ ∀ C : Set M, IsCompact C → ∫⁻ x in C, ‖f x‖ₑ ^ 2 ∂μ < ⊤
def IsWeakAdj {M : Type*} [TopologicalSpace M] [MeasurableSpace M] (n : ℕ) (z : M → V n)
    (ph₁ ph₂ : M → ℝ) (f : M → V n) (w : M → ℂ) : Prop :=
  ∀ g : M → ℂ, IsTest n z g →
    ∫ x, ⟪dbarF n z g x, f x⟫_ℂ * (Real.exp (-ph₂ x) : ℂ) ∂vol n z =
      ∫ x, conj (g x) * w x * (Real.exp (-ph₁ x) : ℂ) ∂vol n z
def IsWeakS {M : Type*} [TopologicalSpace M] [MeasurableSpace M] (n : ℕ) (z : M → V n)
    (f : M → V n) (σ : M → Fin n → Fin n → ℂ) : Prop :=
  ∀ φ : M → ℂ, IsTest n z φ → ∀ j k : Fin n,
    ∫ x, (f x k * db n z j φ x - f x j * db n z k φ x) ∂vol n z = -∫ x, σ x j k * φ x ∂vol n z
def IsWeakDiv {M : Type*} [TopologicalSpace M] [MeasurableSpace M] (n : ℕ) (z : M → V n)
    (G : M → V n) (D : M → ℂ) : Prop :=
  ∀ φ : M → ℂ, IsTest n z φ →
    ∫ x, ∑ j, G x j * d n z j φ x ∂vol n z = -∫ x, D x * φ x ∂vol n z
def HasCutoffs {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (e ψ : M → ℝ) : Prop :=
  ∀ ν : ℕ, ∃ η : M → ℝ, IsTest n z (fun x => (η x : ℂ)) ∧ (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧
    (∀ x, e x ≤ ν → η x = 1) ∧ ∀ x, dbarSq n z (fun y => (η y : ℂ)) x ≤ Real.exp (ψ x)
def GraphApprox {M : Type*} [TopologicalSpace M] [MeasurableSpace M] (n : ℕ) (z : M → V n)
    (ph ψ : M → ℝ) (f : M → V n) (w : M → ℂ) (σ : M → Fin n → Fin n → ℂ) : Prop :=
  ∀ δ : ℝ≥0∞, 0 < δ → ∃ g : M → V n, IsTestForm n z g ∧
    nV n z (fun x => g x - f x) (w2 ph ψ) < δ ∧
    wint n z (fun x => tstar n z (w1 ph ψ) (w2 ph ψ) g x - w x) (w1 ph ψ) < δ ∧
    n2 n z (fun x => sbar n z g x - σ x) ph < δ
def FlatApprox {M : Type*} [TopologicalSpace M] [MeasurableSpace M] (n : ℕ) (z : M → V n)
    (G : M → V n) (D : M → ℂ) (S : M → Fin n → Fin n → ℂ) : Prop :=
  ∃ K₀ : Set M, IsCompact K₀ ∧ ∀ δ : ℝ≥0∞, 0 < δ → ∃ g : M → V n, IsTestForm n z g ∧
    (∀ x, x ∉ K₀ → g x = 0) ∧
    nV n z (fun x => g x - G x) (fun _ => 0) < δ ∧
    wint n z (fun x => divF n z g x - D x) (fun _ => 0) < δ ∧
    n2 n z (fun x => sbar n z g x - S x) (fun _ => 0) < δ
def unwG {M : Type*} {n : ℕ} (ph ψ : M → ℝ) (f : M → V n) : M → V n :=
  fun x => (Real.exp (-w2 ph ψ x) : ℂ) • f x
def unwD {M : Type*} (ph ψ : M → ℝ) (w : M → ℂ) : M → ℂ :=
  fun x => -((Real.exp (-w1 ph ψ x) : ℂ) * w x)
def unwS {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph ψ : M → ℝ) (f : M → V n)
    (σ : M → Fin n → Fin n → ℂ) : M → Fin n → Fin n → ℂ :=
  fun x j k => (Real.exp (-w2 ph ψ x) : ℂ) *
    (σ x j k - wedge (fun i => db n z i (fun y => (w2 ph ψ y : ℂ)) x) (fun i => f x i) j k)
def WeakSSmoothStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ z : M → V n, IsLocalHomeomorph z → ∀ f : M → V n, (∀ j, Ck n z 1 (fun x => f x j)) →
    IsWeakS n z f (sbar n z f)
def SbarDbarStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ z : M → V n, IsLocalHomeomorph z → ∀ g : M → ℂ, Ck n z 2 g → ∀ x : M,
    sbar n z (dbarF n z g) x = 0
def MultAdjStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ z : M → V n, IsLocalHomeomorph z → ∀ (ph₁ ph₂ η : M → ℝ) (f : M → V n) (w : M → ℂ),
    SmoothR n z ph₁ → SmoothR n z ph₂ → SmoothR n z η →
    MemWeightedL2OneForm n z f ph₂ → MemWeightedL2 n z w ph₁ → IsWeakAdj n z ph₁ ph₂ f w →
    IsWeakAdj n z ph₁ ph₂ (fun x => (η x : ℂ) • f x)
      (fun x => (η x : ℂ) * w x -
        (Real.exp (ph₁ x - ph₂ x) : ℂ) * ∑ j, d n z j (fun y => (η y : ℂ)) x * f x j)
def MultSStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ z : M → V n, IsLocalHomeomorph z →
    ∀ (η : M → ℝ) (f : M → V n) (σ : M → Fin n → Fin n → ℂ),
    SmoothR n z η → LocalL2Isometry (vol n z) f → LocalL2Isometry (vol n z) σ → IsWeakS n z f σ →
    IsWeakS n z (fun x => (η x : ℂ) • f x)
      (fun x j k => (η x : ℂ) * σ x j k +
        wedge (fun i => db n z i (fun y => (η y : ℂ)) x) (fun i => f x i) j k)
def MultDivStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ z : M → V n, IsLocalHomeomorph z → ∀ (η : M → ℝ) (G : M → V n) (D : M → ℂ),
    SmoothR n z η → LocalL2Isometry (vol n z) G → LocalL2Isometry (vol n z) D → IsWeakDiv n z G D →
    IsWeakDiv n z (fun x => (η x : ℂ) • G x)
      (fun x => (η x : ℂ) * D x + ∑ j, d n z j (fun y => (η y : ℂ)) x * G x j)
def CutoffStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ z : M → V n, IsLocalHomeomorph z → ∀ (e ph ψ : M → ℝ), Continuous e →
    SmoothR n z ph → SmoothR n z ψ → HasCutoffs n z e ψ →
    (∀ (f : M → V n) (w : M → ℂ) (σ : M → Fin n → Fin n → ℂ),
      MemWeightedL2OneForm n z f (w2 ph ψ) → MemWeightedL2 n z w (w1 ph ψ) → MemWeightedL2TwoForm n z σ ph →
      IsWeakAdj n z (w1 ph ψ) (w2 ph ψ) f w → IsWeakS n z f σ →
      HasCompactSupport f → HasCompactSupport w → HasCompactSupport σ →
      GraphApprox n z ph ψ f w σ) →
    ∀ (f : M → V n) (w : M → ℂ) (σ : M → Fin n → Fin n → ℂ),
      MemWeightedL2OneForm n z f (w2 ph ψ) → MemWeightedL2 n z w (w1 ph ψ) → MemWeightedL2TwoForm n z σ ph →
      IsWeakAdj n z (w1 ph ψ) (w2 ph ψ) f w → IsWeakS n z f σ → GraphApprox n z ph ψ f w σ
def UnweightRelStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ z : M → V n, IsLocalHomeomorph z →
    ∀ (ph ψ : M → ℝ) (f : M → V n) (w : M → ℂ) (σ : M → Fin n → Fin n → ℂ),
    SmoothR n z ph → SmoothR n z ψ → MemWeightedL2OneForm n z f (w2 ph ψ) → MemWeightedL2 n z w (w1 ph ψ) → MemWeightedL2TwoForm n z σ ph →
      IsWeakAdj n z (w1 ph ψ) (w2 ph ψ) f w → IsWeakS n z f σ →
    LocalL2Isometry (vol n z) (unwG ph ψ f) ∧ LocalL2Isometry (vol n z) (unwD ph ψ w) ∧
      LocalL2Isometry (vol n z) (unwS n z ph ψ f σ) ∧
      IsWeakDiv n z (unwG ph ψ f) (unwD ph ψ w) ∧ IsWeakS n z (unwG ph ψ f) (unwS n z ph ψ f σ) ∧
      (HasCompactSupport f → HasCompactSupport (unwG ph ψ f)) ∧
      (HasCompactSupport w → HasCompactSupport (unwD ph ψ w)) ∧
      (HasCompactSupport f → HasCompactSupport σ → HasCompactSupport (unwS n z ph ψ f σ))
def UnweightBackStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ z : M → V n, IsLocalHomeomorph z →
    ∀ (ph ψ : M → ℝ) (f : M → V n) (w : M → ℂ) (σ : M → Fin n → Fin n → ℂ),
    SmoothR n z ph → SmoothR n z ψ →
    MemWeightedL2OneForm n z f (w2 ph ψ) → MemWeightedL2 n z w (w1 ph ψ) → MemWeightedL2TwoForm n z σ ph →
    HasCompactSupport f → HasCompactSupport w → HasCompactSupport σ →
    FlatApprox n z (unwG ph ψ f) (unwD ph ψ w) (unwS n z ph ψ f σ) →
    GraphApprox n z ph ψ f w σ
def LocalizeStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ z : M → V n, IsLocalHomeomorph z →
    (∀ (e : OpenPartialHomeomorph M (V n)) (G : M → V n) (D : M → ℂ)
        (S : M → Fin n → Fin n → ℂ), IsChart n z e →
      LocalL2Isometry (vol n z) G → LocalL2Isometry (vol n z) D → LocalL2Isometry (vol n z) S →
      IsWeakDiv n z G D → IsWeakS n z G S →
      HasCompactSupport G → HasCompactSupport D → HasCompactSupport S →
      tsupport G ⊆ e.source → tsupport D ⊆ e.source → tsupport S ⊆ e.source →
      FlatApprox n z G D S) →
    ∀ (G : M → V n) (D : M → ℂ) (S : M → Fin n → Fin n → ℂ),
      LocalL2Isometry (vol n z) G → LocalL2Isometry (vol n z) D → LocalL2Isometry (vol n z) S →
      IsWeakDiv n z G D → IsWeakS n z G S →
      HasCompactSupport G → HasCompactSupport D → HasCompactSupport S → FlatApprox n z G D S
def ExtendStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ z : M → V n, IsLocalHomeomorph z → ∀ (e : OpenPartialHomeomorph M (V n)) (G : V n → ℂ),
    IsChart n z e → ContDiff ℝ ∞ G → HasCompactSupport G → tsupport G ⊆ e.target →
    Smooth n z (e.source.indicator (G ∘ e)) ∧ HasCompactSupport (e.source.indicator (G ∘ e)) ∧
      tsupport (e.source.indicator (G ∘ e)) ⊆ e.source ∧
      ∀ (j : Fin n) (x : M), x ∈ e.source →
        d n z j (e.source.indicator (G ∘ e)) x = wd n j G (e x) ∧
          db n z j (e.source.indicator (G ∘ e)) x = wdb n j G (e x)
def ChartFlatStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ z : M → V n, IsLocalHomeomorph z →
    ∀ (e : OpenPartialHomeomorph M (V n)) (G : M → V n) (D : M → ℂ)
      (S : M → Fin n → Fin n → ℂ), IsChart n z e →
    LocalL2Isometry (vol n z) G → LocalL2Isometry (vol n z) D → LocalL2Isometry (vol n z) S →
    IsWeakDiv n z G D → IsWeakS n z G S →
    HasCompactSupport G → HasCompactSupport D → HasCompactSupport S →
    tsupport G ⊆ e.source → tsupport D ⊆ e.source → tsupport S ⊆ e.source →
    FlatApprox n z G D S
def FlatGraphStatement (n : ℕ) : Prop :=
  ∀ (Ω K : Set (V n)) (G : V n → V n) (D : V n → ℂ) (S : V n → Fin n → Fin n → ℂ),
    IsOpen Ω → IsCompact K → K ⊆ Ω → (∀ y, y ∉ K → G y = 0 ∧ D y = 0 ∧ S y = 0) →
    MemLp G 2 volume → MemLp D 2 volume → MemLp S 2 volume →
    (∀ φ : V n → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ y, ∑ j, G y j * wd n j φ y = -∫ y, D y * φ y) →
    (∀ φ : V n → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ j k : Fin n,
      ∫ y, (G y k * wdb n j φ y - G y j * wdb n k φ y) = -∫ y, S y j k * φ y) →
    ∃ K₀ : Set (V n), IsCompact K₀ ∧ K₀ ⊆ Ω ∧ ∀ δ : ℝ≥0∞, 0 < δ → ∃ G' : V n → V n,
      ContDiff ℝ ∞ G' ∧ (∀ y, y ∉ K₀ → G' y = 0) ∧
      ∫⁻ y, ‖G' y - G y‖ₑ ^ 2 < δ ∧
      ∫⁻ y, ‖(∑ j, wd n j (fun u => G' u j) y) - D y‖ₑ ^ 2 < δ ∧
      ∫⁻ y, ENNReal.ofReal (sq2 n (fun j k =>
        wdb n j (fun u => G' u k) y - wdb n k (fun u => G' u j) y - S y j k)) < δ
def DensStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ z : M → V n, IsLocalHomeomorph z → ∀ (e ph ψ : M → ℝ), Continuous e →
    SmoothR n z ph → SmoothR n z ψ → HasCutoffs n z e ψ →
    ∀ (f : M → V n) (w : M → ℂ) (σ : M → Fin n → Fin n → ℂ),
      MemWeightedL2OneForm n z f (w2 ph ψ) → MemWeightedL2 n z w (w1 ph ψ) → MemWeightedL2TwoForm n z σ ph →
      IsWeakAdj n z (w1 ph ψ) (w2 ph ψ) f w → IsWeakS n z f σ → GraphApprox n z ph ψ f w σ
def ChiStatement : Prop :=
  ∀ (a : ℝ) (R : ℝ → ℝ), (∀ b : ℝ, BddAbove (R '' Set.Iic b)) →
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ (∀ t, t ≤ a → χ t = 0) ∧ (∀ t, 0 ≤ χ t) ∧
      (∀ t, 0 ≤ deriv χ t) ∧ (∀ t, 0 ≤ deriv (deriv χ) t) ∧
      ∀ t, a + 1 ≤ t → R t ≤ χ t ∧ R t ≤ deriv χ t
def PsiStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ z : M → V n, IsLocalHomeomorph z → ∀ (e : M → ℝ) (a : ℝ), SmoothR n z e →
    (∀ b : ℝ, IsCompact {x | e x ≤ b}) →
    ∃ ψ : M → ℝ, SmoothR n z ψ ∧ (∀ x, e x ≤ a + 1 → ψ x = 0 ∧ dSqR n z ψ x = 0) ∧
      HasCutoffs n z e ψ
def ShellStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ z : M → V n, IsLocalHomeomorph z →
    ∀ (e ph ψ : M → ℝ) (v : M → V n) (a : ℝ), Continuous e →
    (∀ b : ℝ, IsCompact {x | e x ≤ b}) → Continuous ph → Continuous ψ → Continuous v →
    ∃ R : ℝ → ℝ, (∀ b : ℝ, BddAbove (R '' Set.Iic b)) ∧
      ∀ χ : ℝ → ℝ, (∀ t, 0 ≤ χ t) → (∀ t, a + 1 ≤ t → R t ≤ χ t) →
        nV n z v (fun x => ph x + χ (e x) - ψ x) < ⊤
def LeviNormSqStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ z : M → V n, IsLocalHomeomorph z →
    SmoothR n z (fun y => ‖z y‖ ^ 2) ∧
      ∀ (x : M) (ξ : Fin n → ℂ), Levi n z (fun y => ‖z y‖ ^ 2) x ξ = ((∑ j, ‖ξ j‖ ^ 2 : ℝ) : ℂ)
def ChoiceStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (X : EtaleStein n M) (ph : M → ℝ) (v : M → V n) (C : Set M) (ε : ℝ),
    SmoothR n X.z ph → Continuous v → IsCompact C → 0 < ε →
    ∃ (ph' ψ e' : M → ℝ) (U : Set M), SmoothR n X.z ph' ∧ SmoothR n X.z ψ ∧ Continuous e' ∧
      HasCutoffs n X.z e' ψ ∧ IsOpen U ∧ C ⊆ U ∧ (∀ x ∈ U, ph' x = ph x ∧ ψ x = 0) ∧
      (∀ x, ph x + 2 * ψ x ≤ ph' x) ∧
      (∀ (x : M) (ξ : Fin n → ℂ), (Levi n X.z ph x ξ).re +
          (1 + 1 / ε) * dSqR n X.z ψ x * ∑ j, ‖ξ j‖ ^ 2 ≤ (Levi n X.z ph' x ξ).re) ∧
      MemWeightedL2OneForm n X.z v (w2 ph' ψ)
def PrimedIneqStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ z : M → V n, IsLocalHomeomorph z →
    ∀ (ph ph' ψ : M → ℝ) (F0 : M → ℂ) (h : M → ℝ≥0∞) (ε : ℝ),
    SmoothR n z ph → LeviNonneg n z ph → SmoothR n z ph' → SmoothR n z ψ → Smooth n z F0 →
    Measurable h →
    (∀ (x : M) (ξ : Fin n → ℂ), ENNReal.ofReal (‖dbarDot n z F0 x ξ‖ ^ 2) ≤
      h x * ENNReal.ofReal (Levi n z ph x ξ).re) →
    0 < ε → (∀ x, ph x + 2 * ψ x ≤ ph' x) →
    (∀ (x : M) (ξ : Fin n → ℂ), (Levi n z ph x ξ).re +
        (1 + 1 / ε) * dSqR n z ψ x * ∑ j, ‖ξ j‖ ^ 2 ≤ (Levi n z ph' x ξ).re) →
    (∫⁻ x, h x * ENNReal.ofReal (Real.exp (-ph x)) ∂vol n z) ≠ ⊤ →
    ∀ g : M → V n, IsTestForm n z g →
      ENNReal.ofReal (‖ipV n z (dbarF n z F0) g (w2 ph' ψ)‖ ^ 2) ≤
        (∫⁻ x, h x * ENNReal.ofReal (Real.exp (-ph x)) ∂vol n z) *
          (ENNReal.ofReal (1 + ε) * wint n z (tstar n z (w1 ph' ψ) (w2 ph' ψ) g) (w1 ph' ψ) +
            n2 n z (sbar n z g) ph')
def ClosureIneqStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ z : M → V n, IsLocalHomeomorph z →
    ∀ (e ph ψ : M → ℝ) (v : M → V n) (B : ℝ≥0∞) (ε : ℝ), Continuous e →
    SmoothR n z ph → SmoothR n z ψ → HasCutoffs n z e ψ → MemWeightedL2OneForm n z v (w2 ph ψ) →
    B ≠ ⊤ → 0 < ε →
    (∀ g : M → V n, IsTestForm n z g →
      ENNReal.ofReal (‖ipV n z v g (w2 ph ψ)‖ ^ 2) ≤
        B * (ENNReal.ofReal (1 + ε) * wint n z (tstar n z (w1 ph ψ) (w2 ph ψ) g) (w1 ph ψ) +
          n2 n z (sbar n z g) ph)) →
    ∀ (f : M → V n) (w : M → ℂ), MemWeightedL2OneForm n z f (w2 ph ψ) → MemWeightedL2 n z w (w1 ph ψ) →
      IsWeakAdj n z (w1 ph ψ) (w2 ph ψ) f w → IsWeakS n z f 0 →
      ENNReal.ofReal (‖ipV n z v f (w2 ph ψ)‖ ^ 2) ≤
        B * (ENNReal.ofReal (1 + ε) * wint n z w (w1 ph ψ))
def KSubStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ z : M → V n, IsLocalHomeomorph z → ∀ ph₂ : M → ℝ, Continuous ph₂ →
    ∃ K : Submodule ℂ (Lp (V n) 2 (wvol n z ph₂)),
      IsClosed (K : Set (Lp (V n) 2 (wvol n z ph₂))) ∧
      ∀ F : Lp (V n) 2 (wvol n z ph₂), F ∈ K ↔ IsWeakS n z (fun x => F x) 0
def SplitTestStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ z : M → V n, IsLocalHomeomorph z → ∀ (ph₁ ph₂ : M → ℝ) (v f : M → V n),
    SmoothR n z ph₁ → SmoothR n z ph₂ → MemWeightedL2OneForm n z v ph₂ → IsWeakS n z v 0 → IsTestForm n z f →
    MemWeightedL2 n z (tstar n z ph₁ ph₂ f) ph₁ ∧
    ∃ f₁ : M → V n, MemWeightedL2OneForm n z f₁ ph₂ ∧ IsWeakS n z f₁ 0 ∧
      IsWeakAdj n z ph₁ ph₂ f₁ (tstar n z ph₁ ph₂ f) ∧ ipV n z v f ph₂ = ipV n z v f₁ ph₂
def LocalityStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ z : M → V n, IsLocalHomeomorph z → ∀ (ph ph' ψ : M → ℝ) (U : Set M) (f : M → V n),
    IsOpen U → IsTestForm n z f → tsupport f ⊆ U → (∀ x ∈ U, ph' x = ph x ∧ ψ x = 0) →
    (∀ v : M → V n, ipV n z v f (w2 ph' ψ) = ipV n z v f ph) ∧
      wint n z (tstar n z (w1 ph' ψ) (w2 ph' ψ) f) (w1 ph' ψ) = wint n z (tstar n z ph ph f) ph
def TestIneqStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (X : EtaleStein n M) (ph : M → ℝ) (F0 : M → ℂ) (h : M → ℝ≥0∞),
    SmoothR n X.z ph → LeviNonneg n X.z ph → Smooth n X.z F0 → Measurable h →
    (∀ (x : M) (ξ : Fin n → ℂ), ENNReal.ofReal (‖dbarDot n X.z F0 x ξ‖ ^ 2) ≤
      h x * ENNReal.ofReal (Levi n X.z ph x ξ).re) →
    (∫⁻ x, h x * ENNReal.ofReal (Real.exp (-ph x)) ∂vol n X.z) ≠ ⊤ →
    ∀ f : M → V n, IsTestForm n X.z f →
      ENNReal.ofReal (‖ipV n X.z (dbarF n X.z F0) f ph‖ ^ 2) ≤
        (∫⁻ x, h x * ENNReal.ofReal (Real.exp (-ph x)) ∂vol n X.z) *
          wint n X.z (tstar n X.z ph ph f) ph
def RegMStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ z : M → V n, IsLocalHomeomorph z → ∀ F : M → ℂ, LocalL2Isometry (vol n z) F →
    (∀ φ : M → ℂ, IsTest n z φ → ∀ j : Fin n, ∫ x, F x * db n z j φ x ∂vol n z = 0) →
    ∃ G : M → ℂ, Holo n z G ∧ F =ᵐ[vol n z] G
end
end ReciprocityTheory.L2DbarEstimates.F


