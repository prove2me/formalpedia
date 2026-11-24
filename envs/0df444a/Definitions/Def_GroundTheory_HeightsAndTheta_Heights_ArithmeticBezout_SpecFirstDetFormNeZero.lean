-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:04.281699+00:00
-- url     : https://prove2.me/theorems/b469189f-3891-4aa5-85e2-4d68b9f7f6fa
-- title:
--   Spec First Det Form Ne Zero
-- statement:
--   Definitions and structural lemmas for Spec First Det Form Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SpecFirstDetFormNeZero.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LatticePointLogCount
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Matrix
section Objects
variable {n : ℕ}
def finIdeal (P : Ideal (MRing (PBlk n))) : Ideal (MvPolynomial (Fin n) ℤ) :=
  P.comap (rename fun i : Fin n => (⟨(), i⟩ : Σ _ : Unit, PBlk n ()))
def linForm (u : Fin n → ℤ) : MRing (PBlk n) :=
  ∑ i, C (u i) * Xc n i
def pointMetric (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) : ConeMetric ℂ (Fin n) where
  ρ z := ‖WithLp.toLp 2 (S *ᵥ z)‖
  pos z hz := by
    have h : S *ᵥ z ≠ 0 := fun h0 =>
      hz (Matrix.mulVec_injective_iff_isUnit.mpr hS (by rw [h0, Matrix.mulVec_zero]))
    exact norm_pos_iff.mpr (by simpa using h)
  smul c z := by rw [Matrix.mulVec_smul, WithLp.toLp_smul, norm_smul]
def formNorm (S : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) : ℝ :=
  ‖WithLp.toLp 2 ((S⁻¹)ᵀ *ᵥ u)‖
def hermLine (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) : HermLine (PBlk n) :=
  HermLine.ofMetrics (fun _ => pointMetric S hS) 1
def logFormNorm (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (u : Fin n → ℂ)
    (z : (Σ _ : Unit, PBlk n ()) → ℂ) : ℝ :=
  Real.log (‖∑ i, u i * z ⟨(), i⟩‖ / (hermLine S hS).h z)
def normSq (u : Fin n → ℂ) : ℝ :=
  ∑ i, ‖u i‖ ^ 2
variable (n) in

def sphereLaw : Measure (Fin n → ℂ) :=
  ((volume {u : Fin n → ℂ | normSq u ≤ 1})⁻¹ • volume.restrict {u : Fin n → ℂ | normSq u ≤ 1}).map
    fun u => (Real.sqrt (normSq u))⁻¹ • u
def formSphereLaw (S : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) : Measure (Fin k × Fin n → ℂ) :=
  (Measure.pi fun _ : Fin k => sphereLaw n).map fun v p => (Sᵀ *ᵥ v p.1) p.2
def chowMean (S : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) (g : MvPolynomial (Fin k × Fin n) ℂ) : ℝ :=
  ∫ u, Real.log ‖eval u g‖ ∂formSphereLaw S k
def chowHeight (S : Matrix (Fin n) (Fin n) ℂ) {e : ℕ} (f : MvPolynomial (Fin (e + 1) × Fin n) ℚ)
    (δ : ℕ) : ℝ :=
  chowHt (fun _ : NumberField.InfinitePlace ℚ => formSphereLaw S (e + 1)) f δ
def finGaussLog {σ : Type*} (f : MvPolynomial σ ℚ) : ℝ :=
  ∑ᶠ v : Height.AdmissibleAbsValues.nonarchAbsVal (K := ℚ), Real.log (coeffGaussNorm v.1 f)
def IsPrimitive {σ : Type*} (f : MvPolynomial σ ℤ) : Prop :=
  ∀ c : ℤ, (∀ m, c ∣ f.coeff m) → IsUnit c
def IsIntChowForm (P : Ideal (MRing (PBlk n))) (e δ : ℕ)
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℤ) : Prop :=
  IsPrimitive f ∧ IsChowForm (Int.castRingHom ℂ) (finIdeal P) e δ (map (Int.castRingHom ℂ) f)
open Classical in

def chowFormZ (P : Ideal (MRing (PBlk n))) (e : ℕ) : MvPolynomial (Fin (e + 1) × Fin n) ℤ :=
  if h : ∃ f : MvPolynomial (Fin (e + 1) × Fin n) ℤ, ∃ δ, IsIntChowForm P e δ f then h.choose else 0
def cycleChowForm {ι R σ : Type*} [CommSemiring R] (Z : ι →₀ ℕ) (f : ι → MvPolynomial σ R) :
    MvPolynomial σ R :=
  Z.prod fun W m => f W ^ m
def specFirst {R : Type*} [CommRing R] {e : ℕ} (u : Fin n → R) :
    MvPolynomial (Fin (e + 1) × Fin n) R →ₐ[R] MvPolynomial (Fin e × Fin n) R :=
  aeval fun p => Fin.cases (motive := fun _ => MvPolynomial (Fin e × Fin n) R) (C (u p.2))
    (fun k => X (k, p.2)) p.1
open Classical in

def vertPart (P : Ideal (MRing (PBlk n))) (e : ℕ) (s : MRing (PBlk n)) : ℝ :=
  ∑ᶠ W ∈ divSupp P s, (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
    (if IsHorizontal W then 0 else (geoNum e W (fun _ _ => 1) : ℝ) * Real.log (charOf W))
def detForm (R : Type*) [CommRing R] : MvPolynomial (Fin (1 + 1) × Fin 2) R :=
  X (0, 0) * X (1, 1) - X (0, 1) * X (1, 0)
end Objects
def SphereMeanLinear.Statement : Prop :=
  ∀ (n : ℕ) (p : Fin n → ℂ), normSq p = 1 →
    ∫ z, Real.log ‖∑ i, z i * p i‖ ∂sphereLaw n = -(harmonic (n - 1) : ℝ) / 2
def ChowFormTransposition.Statement : Prop :=
  ∀ (n e δ : ℕ) (P : Ideal (MRing (PBlk n))) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ)
    (i j : Fin (e + 1)),
    IsArithVar P (e + 1) → IsChowForm (Int.castRingHom ℂ) (finIdeal P) e δ f →
      ∃ c : ℂ, c ^ 2 = 1 ∧ rename (fun p : Fin (e + 1) × Fin n => (Equiv.swap i j p.1, p.2)) f = C c * f
open Classical in

def ChowFormSection.Statement : Prop :=
  ∀ (n e δ : ℕ) (P : Ideal (MRing (PBlk n))) (f : MvPolynomial (Fin (e + 1 + 1) × Fin n) ℤ)
    (u : Fin n → ℤ),
    IsArithVar P (e + 1 + 1) → IsIntChowForm P (e + 1) δ f → linForm u ∉ P →
      ∃ ε : ℤ, IsUnit ε ∧ specFirst u f =
        C ε * cycleChowForm (divCycle P (linForm u)) fun W =>
          if IsHorizontal W then chowFormZ W e
          else C ((charOf W : ℤ) ^ (geoNum (e + 1) W fun _ _ => 1).toNat)
def ChowFormSectionPoint.Statement : Prop :=
  ∀ (n δ : ℕ) (P : Ideal (MRing (PBlk n))) (f : MvPolynomial (Fin (0 + 1) × Fin n) ℤ) (u : Fin n → ℤ),
    IsArithVar P (0 + 1) → IsIntChowForm P 0 δ f → linForm u ∉ P →
      ∃ ε : ℤ, IsUnit ε ∧ specFirst u f =
        C ε * cycleChowForm (divCycle P (linForm u)) fun W =>
          C ((charOf W : ℤ) ^ (geoNum 0 W fun _ _ => 1).toNat)
def VerticalPartGauss.Statement : Prop :=
  ∀ (n e δ : ℕ) (P : Ideal (MRing (PBlk n))) (f : MvPolynomial (Fin (e + 1) × Fin n) ℚ)
    (u : Fin n → ℤ),
    IsArithVar P (e + 1) → IsChowForm (Int.castRingHom ℂ) (finIdeal P) e δ (map (Rat.castHom ℂ) f) →
      linForm u ∉ P →
        vertPart P e (linForm u) = finGaussLog f - finGaussLog (specFirst (fun i => (u i : ℚ)) f)
def LogNormIntegral.Statement : Prop :=
  ∀ (n e δ : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (P : Ideal (MRing (PBlk n)))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
    IsArithVar P (e + 1) → IsChowForm (Int.castRingHom ℂ) (finIdeal P) e δ f → specFirst u f ≠ 0 →
      chowMean S e (specFirst u f) - chowMean S (e + 1) f - δ * (harmonic (n - 1) : ℝ) / 2 =
        ptsIntegral P (pot fun _ : Fin e => hermLine S hS) (logFormNorm S hS u)
def IntersectionEqChowHeight.Statement : Prop :=
  ∀ (n e δ : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    (I : Ideal (MRing (PBlk n)) → (k : ℕ) → (Fin k → HermLine (PBlk n)) → ℝ)
    (P : Ideal (MRing (PBlk n))) (f : MvPolynomial (Fin (e + 1) × Fin n) ℚ),
    IsIntersectionFamily I → IsArithVar P (e + 1) →
      IsChowForm (Int.castRingHom ℂ) (finIdeal P) e δ (map (Rat.castHom ℂ) f) →
        I P (e + 1) (fun _ => hermLine S hS) = chowHeight S f δ
def ChowHeightLowerBound.Statement : Prop :=
  ∀ (n e δ : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (Λ : ℝ) (P : Ideal (MRing (PBlk n)))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℚ),
    IsUnit S → IsArithVar P (e + 1) →
      IsChowForm (Int.castRingHom ℂ) (finIdeal P) e δ (map (Rat.castHom ℂ) f) →
      (∃ G : Set (Fin n → ℤ), Submodule.span ℤ G = ⊤ ∧ ∀ u ∈ G, formNorm S (fun i => (u i : ℂ)) ≤ Λ) →
        -((e + 1 : ℝ) * δ * Real.log Λ) ≤ chowHeight S f δ
def GaussNormMul.Statement : Prop :=
  ∀ (K : Type) [Field K] (σ : Type) (v : AbsoluteValue K ℝ), IsNonarchimedean v →
    ∀ f g : MvPolynomial σ K, coeffGaussNorm v (f * g) = coeffGaussNorm v f * coeffGaussNorm v g
def LogMeanMul.Statement : Prop :=
  ∀ (n e : ℕ) (S : Matrix (Fin n) (Fin n) ℂ), IsUnit S →
    ∀ f g : MvPolynomial (Fin (e + 1) × Fin n) ℂ, f ≠ 0 → g ≠ 0 →
      logMean (formSphereLaw S (e + 1)) (f * g) =
        logMean (formSphereLaw S (e + 1)) f + logMean (formSphereLaw S (e + 1)) g
def ChowHeightCycle.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ)
    (S : NumberField.InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ w, IsUnit (S w)) →
    ∀ (ι : Type) (Z : ι →₀ ℕ) (f : ι → MvPolynomial (Fin (e + 1) × Fin n) K) (δ : ι → ℕ),
      (∀ i ∈ Z.support, f i ≠ 0) →
        chowHt (fun w => formSphereLaw (S w) (e + 1)) (cycleChowForm Z f) (Z.sum fun i m => m * δ i) =
          Z.sum fun i m => (m : ℝ) * chowHt (fun w => formSphereLaw (S w) (e + 1)) (f i) (δ i)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
end


