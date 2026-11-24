-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:42:47.340472+00:00
-- url     : https://prove2.me/theorems/3f4f7652-db17-4209-81ed-a5a36dc58ffb
-- title:
--   Eq Zero Of Mem Zero Locus Line Origin Ideal
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Mem Zero Locus Line Origin Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/EqZeroOfMemZeroLocusLineOriginIdeal.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial MeasureTheory Filter Topology Matrix
open scoped ContDiff ENNReal
noncomputable section
variable {n d e : ℕ}
def zeroLocus {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) : Set (Fin n → ℂ) :=
  {x | ∀ q ∈ J, eval x q = 0}
structure IsAffVariety (J : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) : Prop where
  isPrime : J.IsPrime
  dim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d
def linVal (u x : Fin n → ℂ) : ℂ := ∑ j, u j * x j
def IsFiniteProj (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) : Prop :=
  (aeval (R := ℂ) fun i : Fin d => Ideal.Quotient.mk J (linForm (A i))).Finite
def IsGraphChart (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (x : Fin n → ℂ) (σ : (Fin d → ℂ) → (Fin n → ℂ)) : Prop :=
  x ∈ zeroLocus J ∧ ∃ (U : Set (Fin n → ℂ)) (V : Set (Fin d → ℂ)), IsOpen U ∧ x ∈ U ∧ IsOpen V ∧
    AnalyticOnNhd ℂ σ V ∧ Set.BijOn σ V (zeroLocus J ∩ U) ∧ ∀ w ∈ V, A *ᵥ σ w = w
open Classical in

def sheetDens (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (x : Fin n → ℂ) : ℝ :=
  if h : ∃ σ, IsGraphChart J A x σ then
    ReciprocityTheory.AnForm.maDens (fun i => φ i ∘ h.choose) (A *ᵥ x)
  else 0
def fibre (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (w : Fin d → ℂ) :
    Set (Fin n → ℂ) :=
  {x | x ∈ zeroLocus J ∧ A *ᵥ x = w}
def projInt (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) : ℝ :=
  ∫ w : Fin d → ℂ, ∑ᶠ x ∈ fibre J A w, g x * sheetDens J A φ x
def ProjIntegrable (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) : Prop :=
  Integrable fun w : Fin d → ℂ => ∑ᶠ x ∈ fibre J A w, |g x * sheetDens J A φ x|
open Classical in

def varIntegral (J : Ideal (MvPolynomial (Fin n) ℂ)) (g : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) : ℝ :=
  if h : ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProj J A then projInt J h.choose g φ else 0
def withFirst (f : (Fin n → ℂ) → ℝ) (ψ : Fin e → (Fin n → ℂ) → ℝ) :
    Fin (e + 1) → (Fin n → ℂ) → ℝ :=
  Fin.cons (α := fun _ => (Fin n → ℂ) → ℝ) f ψ
def SmoothNear (Z : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℝ) : Prop :=
  ∃ U, IsOpen U ∧ Z ⊆ U ∧ ContDiffOn ℝ ∞ f U
def eucNorm (v : Fin n → ℂ) : ℝ := √(∑ j, ‖v j‖ ^ 2)
def zarTangent (J : Ideal (MvPolynomial (Fin n) ℂ)) (x : Fin n → ℂ) : Set (Fin n → ℂ) :=
  {v | ∀ q ∈ J, ∑ j, eval x (pderiv j q) * v j = 0}
def restrGradNorm (χ : (Fin n → ℂ) → ℝ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (x : Fin n → ℂ) : ℝ :=
  sSup ((fun v => |fderiv ℝ χ x v|) '' {v | v ∈ zarTangent J x ∧ eucNorm v ≤ 1})
def restrLeviNorm (χ : (Fin n → ℂ) → ℝ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (x : Fin n → ℂ) : ℝ :=
  sSup ((fun v => |ReciprocityTheory.AnForm.levi χ x v|) '' {v | v ∈ zarTangent J x ∧ eucNorm v ≤ 1})
def zLIntegral (J : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) (B : Set (Fin n → ℂ))
    (g : (Fin n → ℂ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ y in {y : EuclideanSpace ℂ (Fin n) | (fun i => y i) ∈ zeroLocus J ∩ B},
    g (fun i => y i) ∂(Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ))
structure GoodPosition (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u p : Fin n → ℂ)
    (π : Matrix (Fin e) (Fin n) ℂ) (U : Set (Fin n → ℂ)) (V : Set (Fin e → ℂ)) (ρ : ℝ) (N : ℕ) :
    Prop where
  isOpen_U : IsOpen U
  isBounded_U : Bornology.IsBounded U
  mem_U : p ∈ U
  mem_W : p ∈ zeroLocus W
  isOpen_V : IsOpen V
  mem_V : π *ᵥ p ∈ V
  pos : 0 < ρ
  zeros : ∀ q ∈ closure U, q ∈ zeroLocus J → linVal u q = 0 → π *ᵥ q ∈ V → q ∈ U ∧ q ∈ zeroLocus W
  injOn : ∀ q ∈ U ∩ zeroLocus W, ∀ q' ∈ U ∩ zeroLocus W, π *ᵥ q = π *ᵥ q' → q = q'
  count : ∀ w ∈ V, ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ →
    {x | x ∈ U ∩ zeroLocus J ∧ π *ᵥ x = w ∧ linVal u x = t}.encard = N
def fsPot (h : HermNorm n) (y : Fin n → ℂ) : ℝ := Real.log (h.dualNorm y ^ 2)
def planeIdeal (n e : ℕ) : Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.span {q | ∃ j : Fin n, e + 1 ≤ (j : ℕ) ∧ q = X j}
def ProjectionIndependence.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A A' : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    IsAffVariety J d → IsFiniteProj J A → IsFiniteProj J A' → Measurable f →
    (∀ i, SmoothNear (zeroLocus J) (φ i)) →
      projInt J A f φ = projInt J A' f φ
def VarIntegralFlat.Statement : Prop :=
  ∀ (d : ℕ) (f : (Fin d → ℂ) → ℝ) (φ : Fin d → (Fin d → ℂ) → ℝ), Measurable f →
    (∀ i, ContDiff ℝ ∞ (φ i)) →
      varIntegral (⊥ : Ideal (MvPolynomial (Fin d) ℂ)) f φ =
        ∫ x : Fin d → ℂ, f x * ReciprocityTheory.AnForm.maDens φ x
def CutOff.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (P : Ideal (MvPolynomial (Fin d) ℂ)), IsAffVariety J d → IsFiniteProj J A → P ≠ ⊥ →
    ∃ χ : ℝ → (Fin n → ℂ) → ℝ,
      (∀ ε, ContDiff ℝ ∞ (χ ε)) ∧ (∀ ε x, 0 ≤ χ ε x ∧ χ ε x ≤ 1) ∧
      (∀ ε, 0 < ε → ∃ U : Set (Fin n → ℂ), IsOpen U ∧
        {x | x ∈ zeroLocus J ∧ A *ᵥ x ∈ zeroLocus P} ⊆ U ∧ ∀ x ∈ U ∩ zeroLocus J, χ ε x = 0) ∧
      (∀ x ∈ zeroLocus J, A *ᵥ x ∉ zeroLocus P → Tendsto (fun ε => χ ε x) (𝓝[>] 0) (𝓝 1)) ∧
      ∀ B : Set (Fin n → ℂ), Bornology.IsBounded B →
        Tendsto (fun ε => zLIntegral J d B fun x => ENNReal.ofReal (restrGradNorm (χ ε) J x ^ 2))
            (𝓝[>] 0) (𝓝 0) ∧
          Tendsto (fun ε => zLIntegral J d B fun x => ENNReal.ofReal (restrLeviNorm (χ ε) J x))
            (𝓝[>] 0) (𝓝 0)
def StokesOnVariety.Statement : Prop :=
  ∀ (n e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (f g : (Fin n → ℂ) → ℝ)
    (ψ : Fin e → (Fin n → ℂ) → ℝ), IsAffVariety J (e + 1) →
    SmoothNear (zeroLocus J) f → SmoothNear (zeroLocus J) g → (HasCompactSupport f ∨ HasCompactSupport g) →
    (∀ i, SmoothNear (zeroLocus J) (ψ i)) →
      varIntegral J f (withFirst g ψ) = varIntegral J g (withFirst f ψ)
def LogIntegrable.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (u : Fin n → ℂ) (B : Set (Fin n → ℂ)),
    IsAffVariety J d → IsFiniteProj J A → (∀ i, SmoothNear (zeroLocus J) (φ i)) →
    linForm u ∉ J → Bornology.IsBounded B →
      ProjIntegrable J A (B.indicator fun x => Real.log ‖linVal u x‖) φ
def LocalOrder.Statement : Prop :=
  ∀ (n e : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u p : Fin n → ℂ)
    (π : Matrix (Fin e) (Fin n) ℂ) (U : Set (Fin n → ℂ)) (V : Set (Fin e → ℂ)) (ρ : ℝ) (N : ℕ),
    IsAffVariety J (e + 1) → linForm u ∉ J → W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes →
    GoodPosition J W u p π U V ρ N →
      localMult (J ⊔ Ideal.span {linForm u}) W = N
def PoincareLelong.Statement : Prop :=
  ∀ (n e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (f : (Fin n → ℂ) → ℝ)
    (ψ : Fin e → (Fin n → ℂ) → ℝ), IsAffVariety J (e + 1) → linForm u ∉ J →
    ContDiff ℝ ∞ f → HasCompactSupport f → (∀ i, SmoothNear (zeroLocus J) (ψ i)) →
      varIntegral J (fun x => Real.log ‖linVal u x‖) (withFirst f ψ) =
        ∑ᶠ W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes,
          (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varIntegral W f ψ
def ConeToProjective.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ)
    (g : (Fin n → ℂ) → ℝ), IsAffVariety J (e + 1) → IsHomogIdeal J → linForm ℓ ∉ J →
    Measurable g → (∀ c : ℂ, c ≠ 0 → ∀ y, g (c • y) = g y) →
      coneIntegral h J e g =
        ((2 : ℝ) ^ e)⁻¹ * varIntegral (J ⊔ Ideal.span {linForm ℓ - 1}) g (fun _ : Fin e => fsPot h)
def ConeSlicePlane.Statement : Prop :=
  ∀ (n e : ℕ) (hn : e + 1 ≤ n),
    coneIntegral (HermNorm.std n) (planeIdeal n e) e (fun _ => 1) = 1 ∧
      varIntegral (planeIdeal n e ⊔ Ideal.span {linForm (Pi.single (⟨0, by omega⟩ : Fin n) 1) - 1})
          (fun _ => (1 : ℝ)) (fun _ : Fin e => fsPot (HermNorm.std n)) = 2 ^ e
def GreenFromLelong.Statement : Prop :=
  PoincareLelong.Statement → ConeToProjective.Statement → GreenSymmetry.Statement
def MassFromLelong.Statement : Prop :=
  PoincareLelong.Statement → ConeToProjective.Statement → ConeIntegralMass.Statement
section Inhabitants
def lineBump : (Fin 1 → ℂ) → ℝ := fun x => (⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : ℂ)) (x 0)
def lineOriginIdeal : Ideal (MvPolynomial (Fin 1) ℂ) := RingHom.ker (eval (0 : Fin 1 → ℂ))
end Inhabitants
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


