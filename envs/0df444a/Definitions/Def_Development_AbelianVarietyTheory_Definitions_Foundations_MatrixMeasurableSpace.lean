-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:41.385037+00:00
-- url     : https://prove2.me/theorems/7d35df12-12a4-454a-a7ec-266eb66f764d
-- title:
--   Matrix Measurable Space
-- statement:
--   Definitions and structural lemmas for Matrix Measurable Space, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MatrixMeasurableSpace.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
namespace GlobalTheory.SplitWeil
def SB (X : Type*) [TopologicalSpace X] : Submodule ℂ (X → ℂ) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  smul_mem' c f hf := ⟨(IsLocallyConstant.const c).mul hf.1, hf.2.smul_left (f := fun _ => c)⟩
def IsSmoothRep {G V : Type*} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : Prop := ∀ v : V, IsOpen {g : G | ρ g v = v}
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def nabs (x : kˣ) : ℝ := (distribHaarChar k x : ℝ≥0)
def resCard : ℕ := Nat.card 𝓀[k]
def KO (n : Type*) [Fintype n] [DecidableEq n] : Subgroup (GL n k) :=
  (Matrix.GeneralLinearGroup.map (n := n) (algebraMap 𝒪[k] k)).range
def KOne (n : Type*) [Fintype n] [DecidableEq n] : Subgroup (GL n k) :=
  ((Matrix.GeneralLinearGroup.map (n := n) (IsLocalRing.residue 𝒪[k])).ker).map
    (Matrix.GeneralLinearGroup.map (n := n) (algebraMap 𝒪[k] k))
variable {k}
def HasConductor (ψ : AddChar k Circle) (c : kˣ) : Prop :=
  ∀ x : k, (∀ y : k, valuation k y ≤ valuation k x → ψ y = 1) ↔ valuation k x ≤ valuation k (c : k)
def IsTame (μ : kˣ →* ℂˣ) : Prop := ∀ x : kˣ, valuation k ((x : k) - 1) < 1 → μ x = 1
def IsUnram (μ : kˣ →* ℂˣ) : Prop := ∀ x : kˣ, valuation k (x : k) = 1 → μ x = 1
def om {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ) : Matrix b a k → ℂ := fun x =>
  (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * ((μ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) *
    ((nabs k (Matrix.GeneralLinearGroup.det g) ^ ((Fintype.card b : ℝ) / 2) : ℝ) : ℂ) *
    ((nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card a : ℝ) / 2) : ℝ) : ℂ) *
    Φ ((h⁻¹ : GL b k).val * x * g.val)
instance matrixMeasurableSpace {m n α : Type*} [MeasurableSpace α] : MeasurableSpace (Matrix m n α) :=
  (MeasurableSpace.pi : MeasurableSpace (m → n → α))
variable [MeasurableSpace k] [BorelSpace k]
def IsUnitVol (ν : Measure k) : Prop := ν.IsAddHaarMeasure ∧ ν (𝒪[k] : Set k) = 1
def IsSelfDual (ψ : AddChar k Circle) (ν : Measure k) : Prop :=
  ν.IsAddHaarMeasure ∧ ∀ f ∈ SB k, ∫ y, (∫ x, f x * (ψ (x * y) : ℂ) ∂ν) ∂ν = f 0
def volM (ν : Measure k) (m n : Type*) [Fintype m] [Fintype n] : Measure (Matrix m n k) :=
  (Measure.pi fun _ : m => Measure.pi fun _ : n => ν : Measure (m → n → k))
def volGL (ν : Measure k) (n : Type*) [Fintype n] [DecidableEq n] : Measure (GL n k) :=
  ((volM ν n n).comap (fun g : GL n k => g.val)).withDensity fun g =>
    ENNReal.ofReal (nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card n : ℝ)))
def ip (ν : Measure k) {m n : Type*} [Fintype m] [Fintype n] (Φ₁ Φ₂ : Matrix m n k → ℂ) : ℂ :=
  ∫ x, Φ₁ x * (starRingEnd ℂ) (Φ₂ x) ∂(volM ν m n)
end GlobalTheory.SplitWeil


