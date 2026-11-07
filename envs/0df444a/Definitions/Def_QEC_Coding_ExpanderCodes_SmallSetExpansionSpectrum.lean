-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
-- name    : QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:31:28.84313+00:00
-- url     : https://prove2.me/theorems/44ff954e-5888-423d-802a-3fe1a669b275
-- title:
--   Small Set Expansion Spectrum
-- statement:
--   Definitions and structural lemmas for Small Set Expansion Spectrum, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSpectrum.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Mathlib.Analysis.InnerProductSpace.Spectrum
set_option autoImplicit false
namespace QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
def HasMeanZeroOperatorBound [Fintype V]
    (M : WeightedGraph V) (spectral : ℝ) : Prop :=
  ∀ g : V → ℝ,
    (∑ v, g v) = 0 →
      (∑ v, (weightedNeighborSum M g v) ^ 2) ≤
        spectral ^ 2 * ∑ v, (g v) ^ 2
noncomputable def complexWeightedNeighborSum [Fintype V]
    (M : WeightedGraph V) (g : V → ℂ) (v : V) : ℂ :=
  ∑ u, (M v u : ℂ) * g u
def HasMeanZeroComplexOperatorBound [Fintype V]
    (M : WeightedGraph V) (spectral : ℝ) : Prop :=
  ∀ g : V → ℂ,
    (∑ v, g v) = 0 →
      (∑ v, ‖complexWeightedNeighborSum M g v‖ ^ 2) ≤
        spectral ^ 2 * ∑ v, ‖g v‖ ^ 2
@[simp] theorem complexWeightedNeighborSum_real
    [Fintype V] (M : WeightedGraph V) (g : V → ℝ) (v : V) :
    complexWeightedNeighborSum M (fun u => (g u : ℂ)) v =
      (weightedNeighborSum M g v : ℂ) := by
  classical
  unfold complexWeightedNeighborSum weightedNeighborSum
  push_cast
  rfl
noncomputable def complexAdjacencyEuclidean [Fintype V]
    (M : WeightedGraph V) :
    EuclideanSpace ℂ V →ₗ[ℂ] EuclideanSpace ℂ V where
  toFun f := WithLp.toLp 2 (fun v =>
    complexWeightedNeighborSum M (fun u => f u) v)
  map_add' f g := by
    apply WithLp.ofLp_injective 2
    funext v
    simp [complexWeightedNeighborSum, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    apply WithLp.ofLp_injective 2
    funext v
    simp only [complexWeightedNeighborSum, PiLp.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _hu
    ring
@[simp] theorem complexAdjacencyEuclidean_apply
    [Fintype V] (M : WeightedGraph V)
    (f : EuclideanSpace ℂ V) (v : V) :
    complexAdjacencyEuclidean M f v =
      complexWeightedNeighborSum M (fun u => f u) v := rfl
theorem complexAdjacencyEuclidean_isSymmetric
    [Fintype V]
    (M : WeightedGraph V) (hSymmetric : IsSymmetric M) :
    (complexAdjacencyEuclidean M).IsSymmetric := by
  classical
  intro f g
  rw [EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct]
  change
    (∑ v, g v * star (∑ u, (M v u : ℂ) * f u)) =
      ∑ u, (∑ v, (M u v : ℂ) * g v) * star (f u)
  simp_rw [star_sum, star_mul, star_natCast]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _hu
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _hv
  rw [hSymmetric]
  ring
noncomputable def constantEuclideanVector [Fintype V] :
    EuclideanSpace ℂ V :=
  WithLp.toLp 2 (fun _ => 1)
@[simp] theorem constantEuclideanVector_apply
    [Fintype V] (v : V) :
    constantEuclideanVector (V := V) v = 1 := rfl
@[simp] theorem inner_constantEuclideanVector
    [Fintype V] (f : EuclideanSpace ℂ V) :
    inner ℂ (constantEuclideanVector (V := V)) f = ∑ v, f v := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ v, f v * star (1 : ℂ)) = ∑ v, f v
  simp
noncomputable def centeredAdjacencyEuclidean [Fintype V]
    (M : WeightedGraph V) (degree : Nat) :
    EuclideanSpace ℂ V →ₗ[ℂ] EuclideanSpace ℂ V :=
  complexAdjacencyEuclidean M -
    (((degree : ℂ) / (Fintype.card V : ℂ)) •
      (InnerProductSpace.rankOne ℂ
        (constantEuclideanVector (V := V))
        (constantEuclideanVector (V := V))).toLinearMap)
theorem centeredAdjacencyEuclidean_isSymmetric
    [Fintype V]
    (M : WeightedGraph V) (degree : Nat)
    (hSymmetric : IsSymmetric M) :
    (centeredAdjacencyEuclidean M degree).IsSymmetric := by
  apply (complexAdjacencyEuclidean_isSymmetric M hSymmetric).sub
  exact (InnerProductSpace.isSymmetric_rankOne_self
    (constantEuclideanVector (V := V))).smul (by simp)
noncomputable def coordinateSum [Fintype V] :
    EuclideanSpace ℂ V →ₗ[ℂ] ℂ where
  toFun f := ∑ v, f v
  map_add' f g := Finset.sum_add_distrib
  map_smul' c f := by simp [Finset.mul_sum]
noncomputable def meanZeroEuclideanSubspace [Fintype V] :
    Submodule ℂ (EuclideanSpace ℂ V) :=
  LinearMap.ker coordinateSum
@[simp] theorem mem_meanZeroEuclideanSubspace_iff
    [Fintype V] (f : EuclideanSpace ℂ V) :
    f ∈ meanZeroEuclideanSubspace ↔ (∑ v, f v) = 0 := by
  rfl
theorem sum_complexWeightedNeighborSum_eq_degree_mul_sum
    [Fintype V]
    (M : WeightedGraph V) (degree : Nat)
    (hSymmetric : IsSymmetric M) (hRegular : IsRegular M degree)
    (g : V → ℂ) :
    ∑ v, complexWeightedNeighborSum M g v = degree * ∑ v, g v := by
  classical
  unfold complexWeightedNeighborSum
  rw [Finset.sum_comm]
  calc
    (∑ u, ∑ v, (M v u : ℂ) * g u) =
        ∑ u, g u * ∑ v, (M u v : ℂ) := by
      apply Finset.sum_congr rfl
      intro u _hu
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _hv
      rw [hSymmetric]
      ring
    _ = ∑ u, g u * degree := by
      apply Finset.sum_congr rfl
      intro u _hu
      congr 1
      exact_mod_cast hRegular u
    _ = degree * ∑ u, g u := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _hu
      ring
noncomputable def meanZeroAdjacency
    [Fintype V]
    (M : WeightedGraph V) (degree : Nat)
    (hSymmetric : IsSymmetric M) (hRegular : IsRegular M degree) :
    meanZeroEuclideanSubspace (V := V) →ₗ[ℂ]
      meanZeroEuclideanSubspace (V := V) :=
  (complexAdjacencyEuclidean M).restrict fun f hf => by
    rw [mem_meanZeroEuclideanSubspace_iff] at hf ⊢
    rw [show (∑ v, complexAdjacencyEuclidean M f v) =
        degree * ∑ v, f v by
      simpa using sum_complexWeightedNeighborSum_eq_degree_mul_sum
        M degree hSymmetric hRegular (fun v => f v),
      hf, mul_zero]
end QEC.Coding.SmallSetExpansion


