-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_DefiningCoordinates
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_DefiningCoordinates
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:54:51.499483+00:00
-- url     : https://prove2.me/theorems/b487477e-ecdf-4fe5-ba6b-ad09fb8e70a0
-- title:
--   Defining Coordinates
-- statement:
--   Definitions and structural lemmas for Defining Coordinates, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/DefiningCoordinates.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
namespace GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] [DecidableEq I]
def cWt (E : Type) [Field E] [NumberField E] (k : ℕ) : ℝ :=
  ((k - 1).factorial : ℝ) ^ Module.finrank ℚ (maximalRealSubfield E) *
    |(discr (maximalRealSubfield E) : ℝ)| ^ (((k : ℝ) - 1) / 2)
def polydisc (I : Type) : Set (I → ℂ) := {z | ∀ i, ‖z i‖ < 1}
def defCoord (φ : I → E →+* ℂ) (z : I → ℂ) (x : E) (i : I) : ℂ := φ i x + z i * starRingEnd ℂ (φ i x)
def defTerm (φ : I → E →+* ℂ) (k : ℕ) (z : I → ℂ) (σ : ℂ) (x : E) : ℂ :=
  ∏ i, ((defCoord φ z x i)⁻¹ ^ k * ((‖defCoord φ z x i‖ : ℝ) : ℂ) ^ (-2 * σ))
def IsEisValue (φ : I → E →+* ℂ) (k : ℕ) (L : Set E) (z : I → ℂ) (G : ℂ) : Prop :=
  (k ≠ 2 → HasSum (fun q : modUnits L => ∏ i, (defCoord φ z q.1.out i)⁻¹ ^ k) G) ∧
  (k = 2 → ∃ H : ℂ → ℂ, DifferentiableOn ℂ H {σ : ℂ | -1 / 2 < σ.re} ∧
    (∀ σ : ℂ, 0 < σ.re → HasSum (fun q : modUnits L => defTerm φ 2 z σ q.1.out) (H σ)) ∧ G = H 0)
def IsDefSum (φ : I → E →+* ℂ) (k : ℕ) (L : Set E) (g : (I → ℂ) → ℂ) : Prop :=
  ∀ z ∈ polydisc I, ∃ G : ℂ, IsEisValue φ k L z G ∧ g z = (cWt E k : ℂ) * G
def partialD (i : I) (g : (I → ℂ) → ℂ) : (I → ℂ) → ℂ := fun z => lineDeriv ℂ g z (Pi.single i 1)
def iterD (l : List I) (g : (I → ℂ) → ℂ) : (I → ℂ) → ℂ := l.foldr partialD g
def risingFactor (k : ℕ) (κ : I → ℕ) : ℂ := ∏ i, ((-1 : ℂ) ^ κ i * ∏ j ∈ Finset.range (κ i), ((k : ℂ) + j))
def DerivFormula (φ : I → E →+* ℂ) (k : ℕ) (L : Set E) : Prop :=
  (∃ g, IsDefSum φ k L g) ∧ ∀ g, IsDefSum φ k L g →
    DifferentiableOn ℂ g (polydisc I) ∧
    ∀ (κ : I → ℕ) (l : List I), (∀ i, l.count i = κ i) →
      (∀ S : ℂ → ℂ, IsLatSum φ k κ L S → iterD l g 0 = (cWt E k : ℂ) * risingFactor k κ * S 0) ∧
      (4 ≤ k → ∃ S₀ : ℂ,
        HasSum (fun q : modUnits L => ∏ i, ((φ i q.1.out)⁻¹ ^ (k + κ i) * (starRingEnd ℂ (φ i q.1.out)) ^ κ i)) S₀ ∧
        iterD l g 0 = (cWt E k : ℂ) * risingFactor k κ * S₀)
def lamInf (φ : I → E →+* ℂ) (k : ℕ) (κ : I → ℕ) (α : Eˣ) : ℂ :=
  ∏ i, ((φ i α) ^ (k + κ i) * (starRingEnd ℂ (φ i α))⁻¹ ^ κ i)
def Homothety (φ : I → E →+* ℂ) (k : ℕ) (L : Set E) : Prop :=
  ∀ (κ : I → ℕ) (α : Eˣ) (S : ℂ → ℂ), IsLatSum φ k κ L S →
    IsLatSum φ k κ ((fun x => (α : E) * x) '' L)
      (fun σ => (lamInf φ k κ α)⁻¹ * ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-σ) * S σ) ∧
    ∀ S' : ℂ → ℂ, IsLatSum φ k κ ((fun x => (α : E) * x) '' L) S' → S' 0 = (lamInf φ k κ α)⁻¹ * S 0
def lamFin (χ : HChar E) (s : ℕ) (y : (Af E)ˣ) : ℂ := (finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ)
def ClassInvariance (φ : I → E →+* ℂ) (s : ℕ) : Prop :=
  ∀ (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (κ : I → ℕ) (χ : HChar E),
    IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → IsValChar φ s κ 𝔣 Q χ →
    ∀ (y y' : (Af E)ˣ) (S S' : ℂ → ℂ),
      (QuotientGroup.mk y : PicO (condQ 𝔣 Q)) = QuotientGroup.mk y' →
      IsLatSum φ (2 * s) κ (lattice (condQ 𝔣 Q) y) S → IsLatSum φ (2 * s) κ (lattice (condQ 𝔣 Q) y') S' →
      (lamFin χ s y)⁻¹ * S 0 = (lamFin χ s y')⁻¹ * S' 0
abbrev Coh (E : Type) [Field E] [NumberField E] : Type := E →ₗ[ℚ] ℂ
def eCl (φ : I → E →+* ℂ) (i : I) : Coh E := (φ i).toRatAlgHom.toLinearMap
def fCl (φ : I → E →+* ℂ) (i : I) : Coh E := (ComplexEmbedding.conjugate (φ i)).toRatAlgHom.toLinearMap
def plane (φ : I → E →+* ℂ) (i : I) : Submodule ℂ (Coh E) := Submodule.span ℂ {eCl φ i, fCl φ i}
variable [IsCMField E]
def riemann (ξ x y : E) : ℚ := Algebra.trace ℚ E (ξ * x * IsCMField.complexConj E y)
def riemannCl (ξ x : E) : Coh E where
  toFun y := (riemann ξ x y : ℂ)
  map_add' y y' := by simp [riemann, mul_add]
  map_smul' a y := by
    have h : IsCMField.complexConj E (a • y) = a • IsCMField.complexConj E y := map_rat_smul _ a y
    simp only [riemann, h, mul_smul_comm, map_smul, RingHom.id_apply]
    simp [Rat.smul_def]
def IsDualForm (ξ : E) (B : LinearMap.BilinForm ℂ (Coh E)) : Prop :=
  ∀ x y : E, B (riemannCl ξ x) (riemannCl ξ y) = (riemann ξ x y : ℂ)
def pairing (ε : ℤˣ) (B : LinearMap.BilinForm ℂ (Coh E)) (a b : Coh E) : ℂ :=
  ((ε : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * B a b
def DualFormValue (φ : I → E →+* ℂ) : Prop :=
  ∀ ξ : E, ξ ≠ 0 → IsCMField.complexConj E ξ = -ξ →
    (∃! B, IsDualForm ξ B) ∧ ∀ B, IsDualForm ξ B → ∀ ε : ℤˣ,
      (∀ i j, i ≠ j → ∀ a ∈ plane φ i, ∀ b ∈ plane φ j, pairing ε B a b = 0) ∧
      ∀ i, pairing ε B (eCl φ i) (fCl φ i) = ((ε : ℤ) : ℂ) * (φ i ξ)⁻¹ / (2 * (Real.pi : ℂ) * Complex.I)
def DualFormBase (φ : I → E →+* ℂ) : Prop :=
  ∀ (d : ℕ) (δ : E), 0 < d → δ ^ 2 = -(d : E) → (∀ i, φ i δ = Complex.I * (Real.sqrt d : ℂ)) → ∀ η : ℤˣ,
    (∃! B, IsDualForm (((η : ℤ) : E) * δ⁻¹) B) ∧ ∀ B, IsDualForm (((η : ℤ) : E) * δ⁻¹) B → ∀ ε : ℤˣ,
      (∀ i j, i ≠ j → ∀ a ∈ plane φ i, ∀ b ∈ plane φ j, pairing ε B a b = 0) ∧
      ∀ i, pairing ε B (eCl φ i) (fCl φ i) = ((ε * η : ℤˣ) : ℤ) * ((Real.sqrt d / (2 * Real.pi) : ℝ) : ℂ)
def Statement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ),
    2 ≤ Module.finrank ℚ (maximalRealSubfield E) → IsCMType φ →
    (∀ s : ℕ, 1 ≤ s →
      (∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
        DerivFormula φ (2 * s) (lattice c y) ∧ Homothety φ (2 * s) (lattice c y)) ∧
      ClassInvariance φ s) ∧
    DualFormValue φ ∧ DualFormBase φ
example (φ : I → E →+* ℂ) (k : ℕ) (σ : ℂ) (x : E) : defTerm φ k 0 σ x = term φ k (fun _ => 0) σ x := by
  simp [defTerm, term, defCoord]
example : risingFactor 2 (fun _ : Unit => 2) = 6 := by
  simp [risingFactor, Finset.prod_range_succ]; norm_num
example (φ : I → E →+* ℂ) (z : I → ℂ) (hz : z ∈ polydisc I) (x : E) (hx : x ≠ 0) (i : I) : defCoord φ z x i ≠ 0 := by
  intro h
  have h0 : φ i x ≠ 0 := by simpa using hx
  have h1 : φ i x = -(z i * starRingEnd ℂ (φ i x)) := eq_neg_of_add_eq_zero_left h
  have h2 : ‖φ i x‖ = ‖z i‖ * ‖φ i x‖ := by
    conv_lhs => rw [h1]
    simp
  have h3 : 0 < ‖φ i x‖ := norm_pos_iff.2 h0
  have h4 := hz i
  nlinarith
end GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates


