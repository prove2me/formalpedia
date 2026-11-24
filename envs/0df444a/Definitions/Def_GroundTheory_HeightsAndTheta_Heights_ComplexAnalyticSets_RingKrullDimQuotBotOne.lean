-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RingKrullDimQuotBotOne
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RingKrullDimQuotBotOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:42.065806+00:00
-- url     : https://prove2.me/theorems/e41e3248-1b5d-40b1-9b59-b3aca4e75e85
-- title:
--   Ring Krull Dim Quot Bot One
-- statement:
--   Definitions and structural lemmas for Ring Krull Dim Quot Bot One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RingKrullDimQuotBotOne.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSlab
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
open MvPolynomial MeasureTheory Matrix
open scoped ENNReal
noncomputable section
def areaFactor {k m : ℕ} (L : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) : ℝ :=
  √(LinearMap.det (LinearMap.adjoint L ∘ₗ L))
def AreaLinear.Statement : Prop :=
  ∀ (k m : ℕ) (L : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)),
    Function.Injective L → ∀ A : Set (EuclideanSpace ℝ (Fin k)),
      Measure.hausdorffMeasure (k : ℝ) (L '' A) =
        ENNReal.ofReal (areaFactor L) * Measure.hausdorffMeasure (k : ℝ) A
def pairPt {k m : ℕ} (x : EuclideanSpace ℝ (Fin k)) (y : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin k ⊕ Fin m) :=
  WithLp.toLp 2 (Sum.elim (fun i => x i) (fun j => y j))
def graphOver {k m : ℕ} (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m))
    (A : Set (EuclideanSpace ℝ (Fin k))) : Set (EuclideanSpace ℝ (Fin k ⊕ Fin m)) :=
  (fun x => pairPt x (F x)) '' A
def graphDensity {k m : ℕ} (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin k)) : ℝ :=
  √(LinearMap.det (1 + LinearMap.adjoint (fderiv ℝ F x : EuclideanSpace ℝ (Fin k) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin m)) ∘ₗ (fderiv ℝ F x : EuclideanSpace ℝ (Fin k) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin m))))
def AreaGraph.Statement : Prop :=
  ∀ (k m : ℕ) (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m))
    (U A : Set (EuclideanSpace ℝ (Fin k))),
    IsOpen U → ContDiffOn ℝ 1 F U → MeasurableSet A → A ⊆ U →
      Measure.hausdorffMeasure (k : ℝ) (graphOver F A) =
        ∫⁻ x in A, ENNReal.ofReal (graphDensity F x) ∂(Measure.hausdorffMeasure (k : ℝ))
def realForm {d m : ℕ} (M : Matrix (Fin d) (Fin m) ℂ) :
    Matrix (Fin d × Fin 2) (Fin m × Fin 2) ℝ :=
  fun ip jq => ![![(M ip.1 jq.1).re, -(M ip.1 jq.1).im], ![(M ip.1 jq.1).im, (M ip.1 jq.1).re]]
    ip.2 jq.2
def ComplexJacobian.Statement : Prop :=
  ∀ (d m : ℕ) (M : Matrix (Fin d) (Fin m) ℂ),
    (((1 + (realForm M)ᵀ * realForm M).det : ℝ) : ℂ) = (1 + Mᴴ * M).det ^ 2
def minor {d m : ℕ} (M : Matrix (Fin d) (Fin m) ℂ) (I : Finset (Fin d)) (I' : Finset (Fin m))
    (h : I'.card = I.card) : ℂ :=
  (M.submatrix (I.orderEmbOfFin rfl) (I'.orderEmbOfFin h)).det
def CauchyBinetMinors.Statement : Prop :=
  ∀ (d m : ℕ) (M : Matrix (Fin d) (Fin m) ℂ),
    (1 + Mᴴ * M).det = ∑ I : Finset (Fin d), ∑ I' : Finset (Fin m),
      if h : I'.card = I.card then (((‖minor M I I' h‖ ^ 2 : ℝ)) : ℂ) else 0
def coordGraph {n : ℕ} (P : Finset (Fin n)) (Ω : Set (P → ℂ)) (F : (P → ℂ) → Fin n → ℂ) :
    Set (EuclideanSpace ℂ (Fin n)) :=
  {z | (fun i : P => z i) ∈ Ω ∧ ∀ j, j ∉ P → z j = F (fun i : P => z i) j}
def frameProj {n : ℕ} (e : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (z : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 (fun i : I => e.repr z i)
def ProjectionFormula.Statement : Prop :=
  ∀ (n d : ℕ) (P : Finset (Fin n)) (Ω : Set (P → ℂ)) (F : (P → ℂ) → Fin n → ℂ),
    P.card = d → IsOpen Ω → DifferentiableOn ℂ F Ω →
    ∀ (e : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
      (B : Set (EuclideanSpace ℂ (Fin n))), MeasurableSet B →
      Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (coordGraph P Ω F ∩ B) =
        ∑ I ∈ Finset.powersetCard d (Finset.univ : Finset (Fin n)),
          ∫⁻ x : EuclideanSpace ℂ I,
            (({z | z ∈ coordGraph P Ω F ∩ B ∧ frameProj e I z = x}.encard : ℕ∞) : ℝ≥0∞)
            ∂(Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ))
def zeroSet {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) : Set (EuclideanSpace ℂ (Fin n)) :=
  {z | ∀ q ∈ J, eval (fun i => z i) q = 0}
def NullSmaller.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) < d →
      Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (zeroSet J) = 0
open Classical in

def sheetNumber {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] (I : Finset (Fin n)) : ℕ :=
  letI x : I → FractionRing (MvPolynomial (Fin n) ℂ ⧸ J) := fun i =>
    algebraMap _ _ (Ideal.Quotient.mk J (X (i : Fin n)))
  if AlgebraicIndependent ℂ x then
    Module.finrank (IntermediateField.adjoin ℂ (Set.range x))
      (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J))
  else 0
def MassFinite.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime],
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    ∀ (c : EuclideanSpace ℂ (Fin n)) (R : ℝ),
      Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (zeroSet J ∩ Metric.ball c R) ≤
          (∑ I ∈ Finset.powersetCard d (Finset.univ : Finset (Fin n)), (sheetNumber J I : ℝ≥0∞)) *
            Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) R) ∧
        Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (zeroSet J ∩ Metric.ball c R) < ⊤
def PolySublevel.Statement : Prop :=
  ∀ (d : ℕ) (Q : MvPolynomial (Fin d) ℂ), Q ≠ 0 → ∀ R : ℝ, 0 < R →
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ η : ℝ, 0 < η → η ≤ 1 →
      Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ)
          {x : EuclideanSpace ℂ (Fin d) | x ∈ Metric.ball 0 R ∧ ‖eval (fun i => x i) Q‖ ≤ η} ≤
        ENNReal.ofReal (C * η ^ α)
def SlabBound.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → linForm u ∉ W →
      ∃ (π : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin (e + 1)))
        (N : MvPolynomial (Fin (e + 1)) ℂ) (C C' : ℝ), N ≠ 0 ∧
        (∀ y : EuclideanSpace ℂ (Fin n), (∀ q ∈ W, eval (h.pointOf y) q = 0) →
          ‖y‖ ≤ C' * ‖π y‖) ∧
        ∀ y ∈ coneBall h W, ∀ ε : ℝ, 0 < ε → ‖∑ j, u j * h.pointOf y j‖ ≤ ε * ‖y‖ →
          ‖eval (fun i => π y i) N‖ ≤ C * ε
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


