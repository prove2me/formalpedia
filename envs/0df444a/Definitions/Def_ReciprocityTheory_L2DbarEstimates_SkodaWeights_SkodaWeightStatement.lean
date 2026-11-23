-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaWeightStatement
-- name    : ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaWeightStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:31:53.618113+00:00
-- url     : https://prove2.me/theorems/edd47ceb-60ca-407d-b324-83c29cffbf70
-- title:
--   Skoda Weight Statement
-- statement:
--   Definitions and structural lemmas for Skoda Weight Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/SkodaWeightStatement.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_MinimalSolutionStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace
noncomputable section
def vsq {p : ℕ} (w : Fin p → ℂ) : ℝ := ∑ i, ‖w i‖ ^ 2
def perp {p : ℕ} (g w : Fin p → ℂ) : Fin p → ℂ :=
  fun i => w i - g i * ((∑ j, (starRingEnd ℂ) (g j) * w j) / ((vsq g : ℝ) : ℂ))
def PerpEntryStatement : Prop :=
  ∀ (p : ℕ) (g w : Fin p → ℂ) (i : Fin p), g ≠ 0 →
    ‖perp g w i‖ ^ 2 ≤ (1 - ‖g i‖ ^ 2 / vsq g) * vsq (perp g w)
def PerpTraceStatement : Prop :=
  ∀ (p : ℕ) (g : Fin p → ℂ), g ≠ 0 →
    (∀ i, 0 ≤ 1 - ‖g i‖ ^ 2 / vsq g) ∧ ∑ i, (1 - ‖g i‖ ^ 2 / vsq g) = (p : ℝ) - 1
def PerpNormStatement : Prop :=
  ∀ (p : ℕ) (g w : Fin p → ℂ), g ≠ 0 →
    vsq (perp g w) = vsq w - ‖∑ j, (starRingEnd ℂ) (g j) * w j‖ ^ 2 / vsq g
def gv {X : Type*} {p : ℕ} (g : Fin p → X → ℂ) (y : X) : Fin p → ℂ := fun l => g l y
def jacV (n : ℕ) {p : ℕ} (g : Fin p → V n → ℂ) (y : V n) (ξ : Fin n → ℂ) : Fin p → ℂ :=
  fun l => ∑ k, wd n k (g l) y * ξ k
def DbarQuotVStatement : Prop :=
  ∀ (n p : ℕ) (g : Fin p → V n → ℂ) (u : V n → ℂ) (U : Set (V n)), IsOpen U →
    (∀ l, DifferentiableOn ℂ (g l) U) → DifferentiableOn ℂ u U → (∀ y ∈ U, gv g y ≠ 0) →
    ∀ y ∈ U, ∀ (i : Fin p) (k : Fin n),
      wdb n k (fun y => u y * (starRingEnd ℂ) (g i y) / ((vsq (gv g y) : ℝ) : ℂ)) y =
        u y * (starRingEnd ℂ) (perp (gv g y) (fun l => wd n k (g l) y) i) / ((vsq (gv g y) : ℝ) : ℂ)
def LeviLogVStatement : Prop :=
  ∀ (n p : ℕ) (g : Fin p → V n → ℂ) (U : Set (V n)), IsOpen U →
    (∀ l, DifferentiableOn ℂ (g l) U) → (∀ l, ContDiffOn ℝ 2 (g l) U) →
    (∀ y ∈ U, gv g y ≠ 0) →
    ∀ y ∈ U, ∀ ξ : Fin n → ℂ,
      leviV n (fun y => ((Real.log (vsq (gv g y)) : ℝ) : ℂ)) y ξ =
        ((vsq (perp (gv g y) (jacV n g y ξ)) / vsq (gv g y) : ℝ) : ℂ)
def jacM (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n) {p : ℕ} (g : Fin p → M → ℂ)
    (x : M) (ξ : Fin n → ℂ) : Fin p → ℂ :=
  fun l => ∑ k, d n z k (g l) x * ξ k
def SkodaDbarStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M] : Prop :=
  ∀ (z : M → V n), IsLocalHomeomorph z → ∀ (p : ℕ) (g : Fin p → M → ℂ) (u : M → ℂ),
    (∀ l, Holo n z (g l)) → Holo n z u → (∀ x, gv g x ≠ 0) →
    ∀ (x : M) (i : Fin p) (ξ : Fin n → ℂ),
      dbarDot n z (fun y => u y * (starRingEnd ℂ) (g i y) / ((vsq (gv g y) : ℝ) : ℂ)) x ξ =
        u x * (starRingEnd ℂ) (perp (gv g x) (jacM n z g x ξ) i) / ((vsq (gv g x) : ℝ) : ℂ)
def SkodaLeviStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M] : Prop :=
  ∀ (z : M → V n), IsLocalHomeomorph z → ∀ (p : ℕ) (g : Fin p → M → ℂ),
    (∀ l, Holo n z (g l)) → (∀ x, gv g x ≠ 0) →
    ∀ (x : M) (ξ : Fin n → ℂ),
      Levi n z (fun y => Real.log (vsq (gv g y))) x ξ =
        ((vsq (perp (gv g x) (jacM n z g x ξ)) / vsq (gv g x) : ℝ) : ℂ)
def skW {M : Type*} {p : ℕ} (g : Fin p → M → ℂ) (φ₀ : M → ℝ) (t : ℝ) : M → ℝ :=
  fun x => φ₀ x + t * Real.log (vsq (gv g x))
def SkodaWeightStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M] : Prop :=
  ∀ (z : M → V n), IsLocalHomeomorph z → ∀ (p : ℕ) (g : Fin p → M → ℂ) (φ₀ : M → ℝ) (t : ℝ),
    (∀ l, Holo n z (g l)) → (∀ x, gv g x ≠ 0) → SmoothR n z φ₀ → LeviNonneg n z φ₀ → 0 ≤ t →
    SmoothR n z (skW g φ₀ t) ∧ LeviNonneg n z (skW g φ₀ t) ∧
      ∀ (x : M) (ξ : Fin n → ℂ),
        t * (vsq (perp (gv g x) (jacM n z g x ξ)) / vsq (gv g x)) ≤ (Levi n z (skW g φ₀ t) x ξ).re
def SkodaHypStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M] : Prop :=
  ∀ (z : M → V n), IsLocalHomeomorph z →
    ∀ (p : ℕ) (g : Fin p → M → ℂ) (φ₀ : M → ℝ) (t : ℝ) (u : M → ℂ),
    (∀ l, Holo n z (g l)) → Holo n z u → (∀ x, gv g x ≠ 0) → SmoothR n z φ₀ →
    LeviNonneg n z φ₀ → 0 < t →
    ∀ (x : M) (i : Fin p) (ξ : Fin n → ℂ),
      ‖dbarDot n z (fun y => u y * (starRingEnd ℂ) (g i y) / ((vsq (gv g y) : ℝ) : ℂ)) x ξ‖ ^ 2 ≤
        ‖u x‖ ^ 2 * (1 - ‖g i x‖ ^ 2 / vsq (gv g x)) / (t * vsq (gv g x)) *
          (Levi n z (skW g φ₀ t) x ξ).re
def wvol (n : ℕ) {M : Type*} [MeasurableSpace M] (z : M → V n) (ψ : M → ℝ) : Measure M :=
  (vol n z).withDensity (fun x => ENNReal.ofReal (Real.exp (-ψ x)))
abbrev WeightedL2 (n : ℕ) {M : Type*} [MeasurableSpace M] (z : M → V n) (ψ : M → ℝ) : Type _ :=
  Lp ℂ 2 (wvol n z ψ)
def holSub (n : ℕ) {M : Type*} [TopologicalSpace M] [MeasurableSpace M] (z : M → V n)
    (ψ : M → ℝ) : Submodule ℂ (WeightedL2 n z ψ) where
  carrier := {F | ∃ f : M → ℂ, Holo n z f ∧ (F : M → ℂ) =ᵐ[wvol n z ψ] f}
  zero_mem' := ⟨fun _ => 0, Holo.const n z 0, Lp.coeFn_zero _ _ _⟩
  add_mem' := by
    rintro F G ⟨f, hf, hFf⟩ ⟨g, hg, hGg⟩
    exact ⟨f + g, Holo.add n z f g hf hg, (Lp.coeFn_add F G).trans (hFf.add hGg)⟩
  smul_mem' := by
    rintro c F ⟨f, hf, hFf⟩
    exact ⟨c • f, Holo.mul n z _ f (Holo.const n z c) hf,
      (Lp.coeFn_smul c F).trans (hFf.const_smul c)⟩
def WeightedL2Properties (n : ℕ) (M : Type*) [MeasurableSpace M] : Prop :=
  ∀ (z : M → V n) (ψ : M → ℝ), Measurable ψ →
    (∀ P : M → Prop, (∀ᵐ x ∂wvol n z ψ, P x) ↔ ∀ᵐ x ∂vol n z, P x) ∧
    (∀ F : WeightedL2 n z ψ, wint n z F ψ < ⊤ ∧ ‖F‖ ^ 2 = (wint n z F ψ).toReal) ∧
    (∀ f : M → ℂ, AEStronglyMeasurable f (vol n z) → wint n z f ψ < ⊤ →
      ∃ F : WeightedL2 n z ψ, (F : M → ℂ) =ᵐ[vol n z] f)
def VolOpenPosStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ z : M → V n, IsLocalHomeomorph z → ∀ U : Set M, IsOpen U → U.Nonempty → 0 < vol n z U
def SkodaOpsStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (X : EtaleStein n M) (p : ℕ) (g : Fin p → M → ℂ) (φ : M → ℝ),
    (∀ l, Holo n X.z (g l)) → (∀ x, gv g x ≠ 0) → Continuous φ →
    ∃ (G : WeightedL2 n (fun q : M × Fin p => X.z q.1) (fun x => φ x.1) →L[ℂ]
        WeightedL2 n X.z (fun x => φ x + Real.log (vsq (gv g x))))
      (Gs : WeightedL2 n X.z (fun x => φ x + Real.log (vsq (gv g x))) →L[ℂ]
        WeightedL2 n (fun q : M × Fin p => X.z q.1) (fun x => φ x.1)),
      (∀ h, (G h : M → ℂ) =ᵐ[vol n X.z] fun x => ∑ i, g i x * (h : M × Fin p → ℂ) (x, i)) ∧
      (∀ w, (Gs w : M × Fin p → ℂ) =ᵐ[vol n (fun q : M × Fin p => X.z q.1)]
        fun x => (w : M → ℂ) x.1 * (starRingEnd ℂ) (g x.2 x.1) / ((vsq (gv g x.1) : ℝ) : ℂ)) ∧
      (∀ w h, ⟪Gs w, h⟫_ℂ = ⟪w, G h⟫_ℂ) ∧ (∀ w, ‖Gs w‖ = ‖w‖)
def SkodaNearStatement (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (X : EtaleStein n M) (p : ℕ) (g : Fin p → M → ℂ) (φ₀ : M → ℝ) (t : ℝ),
    HStatement n (M × Fin p) → 1 ≤ p →
    (∀ l, Holo n X.z (g l)) → (∀ x, gv g x ≠ 0) → SmoothR n X.z φ₀ → LeviNonneg n X.z φ₀ →
    0 < t →
    ∀ (u : WeightedL2 n X.z (fun x => skW g φ₀ t x + Real.log (vsq (gv g x)))) (u' : M → ℂ),
      Holo n X.z u' → (u : M → ℂ) =ᵐ[vol n X.z] u' →
      ∀ F0 : WeightedL2 n (fun q : M × Fin p => X.z q.1) (fun x => skW g φ₀ t x.1),
        (F0 : M × Fin p → ℂ) =ᵐ[vol n (fun q : M × Fin p => X.z q.1)]
          (fun x => u' x.1 * (starRingEnd ℂ) (g x.2 x.1) / ((vsq (gv g x.1) : ℝ) : ℂ)) →
        ∃ F ∈ holSub n (fun q : M × Fin p => X.z q.1) (fun x => skW g φ₀ t x.1),
          ‖F0 - F‖ ^ 2 ≤ ((p : ℝ) - 1) / t * ‖u‖ ^ 2
end
end ReciprocityTheory.L2DbarEstimates.H


