-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:00.348478+00:00
-- url     : https://prove2.me/theorems/d212c723-b00e-4c3d-b0cb-09d70cfc1968
-- title:
--   Is Saturated First Coordinate Line
-- statement:
--   Definitions and structural lemmas for Is Saturated First Coordinate Line, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/IsSaturatedFirstCoordinateLine.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterNamed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
section HeightObjects
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
def height (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (A : HermLine ι)
    (W : Ideal (MRing ι)) : ℝ :=
  I W 1 ![A] / degC W
variable {Ω : Type*} [Field Ω]
def IsSectionBounded (P : Ideal (MRing ι)) (y : (Σ k, ι k) → Ω) (A : HermLine ι) (s : Ω) (c : ℝ) :
    Prop :=
  ∀ (dg dh : K → ℕ) (g h : MRing ι) (z : (Σ k, ι k) → ℂ),
    IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + A.a k) →
    aeval y g = s * aeval y h → z ∈ mcPts P →
    ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤ c * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z
def NoCommonZero {n : ℕ} (P : Ideal (MRing ι)) (y : (Σ k, ι k) → Ω) (a : K → ℤ) (s : Fin n → Ω) :
    Prop :=
  ∀ z ∈ mcPts P, ∃ (j : Fin n) (dg dh : K → ℕ) (g h : MRing ι),
    IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + a k) ∧
      aeval y g = s j * aeval y h ∧
      eval z (map (Int.castRingHom ℂ) g) ≠ 0 ∧ eval z (map (Int.castRingHom ℂ) h) ≠ 0
end HeightObjects
def HeightLowerBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (A : HermLine ι) (n : ℕ) (s : Fin n → Ω) (C : ℝ),
    IsIntersectionFamily I → IsSmoothHerm A →
    (∀ j, s j ∈ chartLat y A.a 1) → (∀ j, IsSectionBounded (mCoordIdeal y) y A (s j) (Real.exp C)) →
    NoCommonZero (mCoordIdeal y) y A.a s →
    ∀ W : Ideal (MRing ι), IsArithVar W 1 → mCoordIdeal y ≤ W → -C ≤ height I A W
def HeightMetricChange.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι))
    (A A' : HermLine ι) (c : ℝ),
    IsIntersectionFamily I → IsSmoothHerm A → IsSmoothHerm A' → A.a = A'.a →
    (∀ z ∈ mcPts P, |Real.log (A.h z / A'.h z)| ≤ c) →
    ∀ W : Ideal (MRing ι), IsArithVar W 1 → P ≤ W → |height I A W - height I A' W| ≤ c
def HeightPullback.Statement : Prop :=
  ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (Ω : Type) [Field Ω] [CharZero Ω]
      (y : (Σ k', ι' k') → Ω) (A : HermLine ι) (A' : HermLine ι'),
      IsBlockMap κ v → IsArithVar (mCoordIdeal y) 1 → IsArithVar (imageZ v (mCoordIdeal y)) 1 →
      IsSmoothHerm A → IsPullHerm κ v A A' →
      IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) = 1 →
      height (II K' ι') A' (mCoordIdeal y) = height (II K ι) A (imageZ v (mCoordIdeal y))
def HeightComparison.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (A H : HermLine ι),
    IsIntersectionFamily I → IsSmoothHerm A → IsSmoothHerm H → H.a = 1 →
    ∃ (k : ℕ) (C : ℝ), ∀ W : Ideal (MRing ι), IsArithVar W 1 →
      |height I A W| ≤ (k : ℝ) * height I H W + C
def DenseBoundedHeight.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) (D : ℕ)
    (H : HermLine ι),
    IsIntersectionFamily I → IsArithVar P (D + 1) → IsSmoothHerm H → H.a = 1 →
    ∃ (C : ℝ) (F : Set (Ideal (MRing ι))), IsZariskiDense P F ∧
      ∀ W ∈ F, IsArithVar W 1 ∧ P ≤ W ∧ height I H W ≤ C
section Lattices
open NumberField Matrix
variable {K : Type*} [Field K] [NumberField K] (E : HermitianBundle K)
def IsSaturated (F : Submodule (𝓞 K) E.carrier) : Prop :=
  ∀ (a : 𝓞 K) (x : E.carrier), a ≠ 0 → a • x ∈ F → x ∈ F
def subDegree (F : Submodule (𝓞 K) E.carrier) : ℝ :=
  Real.log (Nat.card (F ⧸ Submodule.span (𝓞 K)
      (Set.range (exists_linearIndependent_fin (K := K) (E := F)).choose))) -
    (1 / 2) * ∑ σ : K →+* ℂ, Real.log (gramDet E.metric σ
      (fun i ↦ ((exists_linearIndependent_fin (K := K) (E := F)).choose i : E.carrier)))
def subSlope (F : Submodule (𝓞 K) E.carrier) : ℝ :=
  subDegree E F / ((Module.finrank (𝓞 K) F : ℝ) * Module.finrank ℚ K)
def slopeMax : EReal :=
  ⨆ (F : Submodule (𝓞 K) E.carrier) (_ : F ≠ ⊥), ((subSlope E F : ℝ) : EReal)
def slopeMaxSub (F' : Submodule (𝓞 K) E.carrier) : EReal :=
  ⨆ (F : Submodule (𝓞 K) E.carrier) (_ : F ≠ ⊥) (_ : F ≤ F'), ((subSlope E F : ℝ) : EReal)
def quotFibreVec (F' : Submodule (𝓞 K) E.carrier) (σ : K →+* ℂ) (x : E.carrier ⧸ F') :
    FibreSpace E.metric σ :=
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun i ↦ fibreVec E.metric σ
      ((exists_linearIndependent_fin (K := K) (E := F')).choose i : E.carrier))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  fibreVec E.metric σ (Submodule.mkQ_surjective F' x).choose -
    (Submodule.span ℂ (Set.range fun i ↦ fibreVec E.metric σ
      ((exists_linearIndependent_fin (K := K) (E := F')).choose i : E.carrier))).starProjection
      (fibreVec E.metric σ (Submodule.mkQ_surjective F' x).choose)
def quotGramDet (F' : Submodule (𝓞 K) E.carrier) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (t : ι → E.carrier ⧸ F') : ℝ :=
  (det (gram ℂ fun i ↦ quotFibreVec E F' σ (t i))).re
def quotDegree (F' : Submodule (𝓞 K) E.carrier) (G : Submodule (𝓞 K) (E.carrier ⧸ F')) : ℝ :=
  Real.log (Nat.card (G ⧸ Submodule.span (𝓞 K)
      (Set.range (exists_linearIndependent_fin (K := K) (E := G)).choose))) -
    (1 / 2) * ∑ σ : K →+* ℂ, Real.log (quotGramDet E F' σ
      (fun i ↦ ((exists_linearIndependent_fin (K := K) (E := G)).choose i : E.carrier ⧸ F')))
def slopeMaxQuot (F' : Submodule (𝓞 K) E.carrier) : EReal :=
  ⨆ (G : Submodule (𝓞 K) (E.carrier ⧸ F')) (_ : G ≠ ⊥),
    ((quotDegree E F' G / ((Module.finrank (𝓞 K) G : ℝ) * Module.finrank ℚ K) : ℝ) : EReal)
end Lattices
def SlopeMaxExtension.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K)
    (F' : Submodule (NumberField.RingOfIntegers K) E.carrier),
    IsSaturated E F' → slopeMax E ≤ max (slopeMaxSub E F') (slopeMaxQuot E F')
def FlagDegreeBound.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (m : ℕ)
    (f : Fin (m + 1) → Submodule (NumberField.RingOfIntegers K) E.carrier),
    Monotone f → (∀ i, IsSaturated E (f i)) →
    (∀ i : Fin (m + 1), Module.finrank (NumberField.RingOfIntegers K) (f i) = (i : ℕ)) →
    ∀ i : Fin (m + 1), ((-((i : ℕ) : ℝ) : ℝ) : EReal) * slopeMax E ≤
      ((-(subDegree E (f i) / Module.finrank ℚ K) : ℝ) : EReal)
section Inhabitants
open NumberField
def yPt : (Σ _ : Unit, PBlk 1 ()) → ℚ := fun _ ↦ 1
def fsLineScaled : HermLine (PBlk 1) :=
  (fsLine 1).tensor (HermLine.ofWeight (fun _ ↦ 1) fun _ _ _ ↦ rfl)
def firstCoordinateLine : Submodule (𝓞 ℚ) (Fin 2 → 𝓞 ℚ) :=
  LinearMap.ker (LinearMap.proj (R := 𝓞 ℚ) (φ := fun _ : Fin 2 ↦ 𝓞 ℚ) 1)
def firstCoordinateLineEquiv : firstCoordinateLine ≃ₗ[𝓞 ℚ] 𝓞 ℚ where
  toFun x := x.1 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun a := ⟨Pi.single 0 a, by
    rw [firstCoordinateLine, LinearMap.mem_ker, LinearMap.proj_apply]; simp⟩
  left_inv x := by
    have hx : x.1 1 = 0 := x.2
    apply Subtype.ext
    funext i
    fin_cases i
    · simp
    · simp [hx]
  right_inv a := by simp
def flagE : Fin 3 → Submodule (𝓞 ℚ) (Fin 2 → 𝓞 ℚ) := ![⊥, firstCoordinateLine, ⊤]
end Inhabitants
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet


