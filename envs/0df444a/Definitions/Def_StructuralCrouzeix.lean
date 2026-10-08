-- Prove2me | Definitions.Def_StructuralCrouzeix
-- name    : StructuralCrouzeix
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:27.084649+00:00
-- url     : https://prove2.me/theorems/842facaf-daa9-4786-a93f-d4a35459f5dc
-- statement:
--   The numerical range of an n×n complex matrix A is the set of values ⟨x, Ax⟩ over unit vectors x in ℂⁿ. A DiskCoordinate for a set U at a point a is a conformal chart: an open set outer containing the closure of U, with an analytic, injective, noncritical map toDisk on outer whose image is open, with an analytic inverse fromDisk, such that the image contains the closed unit disk, toDisk maps U exactly onto the open unit disk, and toDisk(a)=0. An ExteriorCoordinate for U consists of a radius R>1, a nonzero leading coefficient a, a constant b and a function h analytic on the ball of radius R, such that the map t ↦ a t + b + h(1/t) is injective and has nonvanishing derivative on {|t|>1/R}, sends the unit circle onto the frontier of U, sends such t into U exactly when |t|<1, and sends every t with |t|>1 outside the closure of U. For a matrix A, matrixAnalyticEval(A,f) is the functional calculus f(A), built by decomposing into generalized eigenspaces and using the truncated Taylor jet of f at each eigenvalue; completeAnalyticEval(D,F) applies this entrywise to a matrix-valued function F, giving an operator on the tensor (Kronecker) product space. MetricFeasible(T,τ,H) means 1 ≤ H ≤ τ·1 and Tᴴ H T ≤ H in the Loewner order, and IsMinimizing(T,τ,H) means H is feasible for τ and no feasible pair has smaller τ. StrictlyFeasible(T) asks for a Hermitian H and real τ with H−1, τ−H and H−TᴴHT all positive definite. A set U is admissible if it is open, bounded, convex, nonempty, with frontier homeomorphic to the circle, and with a regular analytic boundary parametrization at every boundary point. FullEndpoint is a defined proposition, not an established theorem. It says that for every admissible U, disk coordinates exist at every a in U and an exterior coordinate exists; and for any a in U, disk coordinate f, exterior coordinate G, n>0 and n×n matrix A whose numerical range lies in U, with T = f(A), the matrix T is strictly feasible and there is κ in [1,2] such that minimizers of the feasibility problem at level κ² exist and every such minimizer H has the following properties. With S = √H, A' = S A S⁻¹ and D = S T S⁻¹, H is positive definite, S is invertible, D = f(A'), DᴴD ≤ 1, the spectral radius of D is below 1, and ‖S‖‖S⁻¹‖ = κ, and κ ≤ ‖R‖‖R⁻¹‖ for every invertible R with RTR⁻¹ a contraction. There is also a continuous positive-semidefinite-matrix-valued function Λ on the circle with Haar integral equal to the identity such that, for every m>0 and every v analytic near the closure of U with m×m matrix values, the entrywise calculus of A' on v equals the Haar integral of Λ(t) ⊗ v(boundary point of G at t) and the norm of v(A) is at most κ times the supremum of ‖v(z)‖ over the closure of U.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/StructuralCrouzeix.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/StructuralCrouzeix.lean; bytes 16..7842
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

universe u_61 u_63 u_67 u_83 u_84 u_181

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace CompleteCrouzeix



def numericalRange {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Set ℂ :=
  {z | ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧
    inner ℂ x (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A x) = z}

end CompleteCrouzeix

namespace CompleteCrouzeix
open Set Filter Metric Complex
open scoped Topology


structure DiskCoordinate (U : Set ℂ) (a : ℂ) where
  outer : Set ℂ
  outer_open : IsOpen outer
  closure_subset : closure U ⊆ outer
  toDisk : ℂ → ℂ
  fromDisk : ℂ → ℂ
  analytic_to : AnalyticOnNhd ℂ toDisk outer
  injective_to : InjOn toDisk outer
  noncritical_to : ∀ z ∈ outer, deriv toDisk z ≠ 0
  image_open : IsOpen (toDisk '' outer)
  analytic_from : AnalyticOnNhd ℂ fromDisk (toDisk '' outer)
  inverse_map : MapsTo fromDisk (toDisk '' outer) outer
  left_inverse : ∀ z ∈ outer, fromDisk (toDisk z) = z
  right_inverse : ∀ w ∈ toDisk '' outer, toDisk (fromDisk w) = w
  closedDisk_subset : closedBall 0 1 ⊆ toDisk '' outer
  image_domain : toDisk '' U = ball 0 1
  base_zero : toDisk a = 0

end CompleteCrouzeix

namespace CompleteCrouzeix
open Set Filter Metric Complex
open scoped Topology


def exteriorMap (a b : ℂ) (h : ℂ → ℂ) (t : ℂ) : ℂ := a*t+b+h t⁻¹

structure ExteriorCoordinate (U : Set ℂ) where
  radius : ℝ
  radius_gt : 1 < radius
  leading : ℂ
  constant : ℂ
  regular : ℂ → ℂ
  leading_ne : leading ≠ 0
  analytic_regular : AnalyticOnNhd ℂ regular (ball 0 radius)
  injective : InjOn (exteriorMap leading constant regular) {t | radius⁻¹ < ‖t‖}
  noncritical : ∀ t, radius⁻¹ < ‖t‖ → deriv (exteriorMap leading constant regular) t ≠ 0
  boundary_image : exteriorMap leading constant regular '' sphere 0 1 = frontier U
  interior_iff : ∀ t, radius⁻¹ < ‖t‖ →
    (exteriorMap leading constant regular t ∈ U ↔ t ∈ ball 0 1)
  outside : ∀ t, 1 < ‖t‖ → exteriorMap leading constant regular t ∉ closure U

end CompleteCrouzeix

namespace CompleteCrouzeix
open Polynomial Finset
variable {A : Type u_61} [Ring A] [Algebra ℂ A]

def scalarJetEval (β : ℂ) (N : A) (s : ℕ) (f : ℂ → ℂ) : A :=
  ∑ i ∈ range s, (iteratedDeriv i f β / (i.factorial : ℂ)) • N ^ i

end CompleteCrouzeix

namespace CompleteCrouzeix
open Module Set
open scoped DirectSum
variable {V : Type u_63} [AddCommGroup V] [Module ℂ V] [instFiniteDimensionalℂV : FiniteDimensional ℂ V]

noncomputable def primaryEquiv (T : Module.End ℂ V) :
    V ≃ₗ[ℂ] ⨁ β : ℂ, T.maxGenEigenspace β := by
  classical
  exact (LinearEquiv.ofBijective (DirectSum.coeLinearMap T.maxGenEigenspace)
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      T.independent_maxGenEigenspace T.iSup_maxGenEigenspace_eq_top)).symm

noncomputable def primaryNilpotent (T : Module.End ℂ V) (β : ℂ) :
    Module.End ℂ (T.maxGenEigenspace β) :=
  (T - algebraMap ℂ (Module.End ℂ V) β).restrict
    (fun x hx => T.mapsTo_maxGenEigenspace_of_comm
      (Algebra.mul_sub_algebraMap_commutes T β) β (show x ∈ T.maxGenEigenspace β from hx))

noncomputable def primaryEval (T : Module.End ℂ V) (f : ℂ → ℂ) : Module.End ℂ V :=
  (primaryEquiv T).symm.toLinearMap ∘ₗ
    (DirectSum.lmap fun β => scalarJetEval β (primaryNilpotent T β) (finrank ℂ V) f) ∘ₗ
      (primaryEquiv T).toLinearMap

end CompleteCrouzeix

namespace CompleteCrouzeix
open Filter Topology Set Module
variable {n : Type u_67} [Fintype n] [DecidableEq n]

noncomputable def matrixAnalyticEval (A : Matrix n n ℂ) (f : ℂ → ℂ) : Matrix n n ℂ :=
  Matrix.toLinAlgEquiv'.symm (primaryEval (Matrix.toLinAlgEquiv' A) f)

end CompleteCrouzeix

namespace CompleteCrouzeix
open scoped ENNReal NNReal Matrix.Norms.L2Operator MatrixOrder Kronecker
variable {n : Type u_83} {m : Type u_84} [Fintype n] [DecidableEq n] [instFintypeM : Fintype m] [instDecidableEqM : DecidableEq m]

def completeAnalyticEval (D : Matrix n n ℂ) (F : ℂ → Matrix m m ℂ) :
    Matrix (n×m) (n×m) ℂ :=
  fun i j => matrixAnalyticEval D (fun z => F z i.2 j.2) i.1 j.1

end CompleteCrouzeix

namespace CompleteCrouzeix
open scoped Matrix MatrixOrder
variable {n : Type u_181} [Fintype n] [DecidableEq n] [Nonempty n]

def MetricFeasible (T : Matrix n n ℂ) (τ : ℝ) (H : Matrix n n ℂ) : Prop :=
  1 ≤ H ∧ H ≤ algebraMap ℝ (Matrix n n ℂ) τ ∧ Tᴴ * H * T ≤ H

end CompleteCrouzeix

end

noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Kronecker

namespace StructuralCrouzeix
open CompleteCrouzeix

def RegularAnalyticBoundaryAt (U : Set ℂ) (p : ℂ) : Prop :=
  ∃ χ : ℂ → ℂ, χ 0 = p ∧ AnalyticAt ℂ χ 0 ∧ deriv χ 0 ≠ 0 ∧
    (∀ᶠ z : ℂ in 𝓝 0, χ z ∈ frontier U ↔ z.im = 0)

structure IsAdmissible (U : Set ℂ) : Prop where
  isOpen : IsOpen U
  bounded : Bornology.IsBounded U
  convex : Convex ℝ U
  nonempty : U.Nonempty
  jordan : Nonempty (Circle ≃ₜ ↥(frontier U))
  regular : ∀ p ∈ frontier U, RegularAnalyticBoundaryAt U p

def IsMinimizing {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (τ : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  MetricFeasible T τ H ∧
    ∀ (σ : ℝ) (J : Matrix (Fin n) (Fin n) ℂ),
      MetricFeasible T σ J → τ ≤ σ

def StrictlyFeasible {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ (τ : ℝ) (H : Matrix (Fin n) (Fin n) ℂ), H.IsHermitian ∧
    (H - 1).PosDef ∧
    (algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ) τ - H).PosDef ∧
    (H - Tᴴ * H * T).PosDef

def analyticSupNorm {m : ℕ} (U : Set ℂ)
    (v : ℂ → Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  sSup ((fun z => ‖v z‖) '' closure U)

def boundaryPoint {U : Set ℂ} (G : ExteriorCoordinate U) (t : UnitAddCircle) : ℂ :=
  exteriorMap G.leading G.constant G.regular (t.toCircle : ℂ)

def FullEndpoint : Prop :=
  ∀ (U : Set ℂ), IsAdmissible U →
    (∀ a ∈ U, Nonempty (DiskCoordinate U a)) ∧
    Nonempty (ExteriorCoordinate U) ∧
    ∀ (a : ℂ), a ∈ U → ∀ (f : DiskCoordinate U a) (G : ExteriorCoordinate U),
      ∀ (n : ℕ), 0 < n → ∀ (A : Matrix (Fin n) (Fin n) ℂ),
        numericalRange A ⊆ U →
        let T := matrixAnalyticEval A f.toDisk
        StrictlyFeasible T ∧
        ∃ κ : ℝ, 1 ≤ κ ∧ κ ≤ 2 ∧
          (∃ H : Matrix (Fin n) (Fin n) ℂ, IsMinimizing T (κ ^ 2) H) ∧
          ∀ H : Matrix (Fin n) (Fin n) ℂ, IsMinimizing T (κ ^ 2) H →
            let S := CFC.sqrt H
            let A' := S * A * S⁻¹
            let D := S * T * S⁻¹
            H.PosDef ∧ IsUnit S ∧
            D = matrixAnalyticEval A' f.toDisk ∧
            Dᴴ * D ≤ 1 ∧ spectralRadius ℂ D < 1 ∧
            ‖S‖ * ‖S⁻¹‖ = κ ∧
            (∀ R : Matrix (Fin n) (Fin n) ℂ, IsUnit R →
              (R * T * R⁻¹)ᴴ * (R * T * R⁻¹) ≤ 1 →
              κ ≤ ‖R‖ * ‖R⁻¹‖) ∧
            ∃ Λ : C(UnitAddCircle, Matrix (Fin n) (Fin n) ℂ),
              (∀ t, (Λ t).PosSemidef) ∧
              (∫ t, Λ t ∂AddCircle.haarAddCircle) = 1 ∧
              ∀ (m : ℕ), 0 < m →
                ∀ v : ℂ → Matrix (Fin m) (Fin m) ℂ,
                  AnalyticOnNhd ℂ v (closure U) →
                  completeAnalyticEval A' v =
                    (∫ t, Λ t ⊗ₖ v (boundaryPoint G t) ∂AddCircle.haarAddCircle) ∧
                  ‖completeAnalyticEval A v‖ ≤ κ * analyticSupNorm U v

end StructuralCrouzeix
end

namespace StructuralCrouzeixReference



end StructuralCrouzeixReference
end OAI


