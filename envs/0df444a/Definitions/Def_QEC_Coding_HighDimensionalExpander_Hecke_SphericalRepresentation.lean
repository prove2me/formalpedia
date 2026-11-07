-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalRepresentation
-- name    : QEC_Coding_HighDimensionalExpander_Hecke_SphericalRepresentation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:25:17.617848+00:00
-- url     : https://prove2.me/theorems/cfcdcd4b-0c5e-45b8-a240-5bc4ad49a893
-- title:
--   Spherical Representation
-- statement:
--   Definitions and structural lemmas for Spherical Representation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalRepresentation.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeAlgebra
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Irreducible
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_three
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_three
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompoundGeneralLinear_inv_val


set_option autoImplicit false
noncomputable section
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
open MeasureTheory
open scoped ComplexConjugate MatrixGroups LocalTopology
universe u v
def restrictToMaximalCompact
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V) :
    Representation ℂ (maximalCompact k d) V :=
  rho.comp (maximalCompact k d).subtype
def kFixedSubmodule
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V) : Submodule ℂ V :=
  Representation.invariants (restrictToMaximalCompact rho)
def IsSpherical
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V) : Prop :=
  kFixedSubmodule rho ≠ ⊥
def IsSmooth
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V) : Prop :=
  ∀ v : V, ∃ H : Subgroup (HeckeGroup k d),
    IsOpen (H : Set (HeckeGroup k d)) ∧
      v ∈ Representation.invariants (rho.comp H.subtype)
def IsAdmissible
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V) : Prop :=
  ∀ H : Subgroup (HeckeGroup k d),
    IsOpen (H : Set (HeckeGroup k d)) →
      IsCompact (H : Set (HeckeGroup k d)) →
        Module.Finite ℂ (Representation.invariants (rho.comp H.subtype))
def IsStronglyContinuous
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (rho : Representation ℂ (HeckeGroup k d) V) : Prop :=
  ∀ v : V, Continuous (fun g ↦ rho g v)
def IsUnitary
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V) : Prop :=
  ∀ g v w, inner ℂ (rho g v) (rho g w) = inner ℂ v w
def actionLinearIsometry
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hrho : IsUnitary rho) (g : HeckeGroup k d) : V →ₗᵢ[ℂ] V where
  toLinearMap := rho g
  norm_map' x := by
    have hsquare : ‖rho g x‖ ^ 2 = ‖x‖ ^ 2 := by
      calc
        ‖rho g x‖ ^ 2 = Complex.re (inner ℂ (rho g x) (rho g x)) :=
          norm_sq_eq_re_inner (𝕜 := ℂ) (rho g x)
        _ = Complex.re (inner ℂ x x) := congrArg Complex.re (hrho g x x)
        _ = ‖x‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
    nlinarith [norm_nonneg (rho g x), norm_nonneg x]
def matrixCoefficient
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V) (v w : V) :
    HeckeGroup k d → ℂ :=
  fun g ↦ inner ℂ (rho g v) w
def integratedHeckeAction
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (f : HeckeFunction k d) (v : V) : V :=
  ∫ g, f g • rho g v ∂(normalizedLocalHaarMeasure k d)
theorem integrable_integratedHeckeAction
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hrho : IsStronglyContinuous rho)
    (f : HeckeFunction k d) (v : V) :
    Integrable (fun g ↦ f g • rho g v)
      (normalizedLocalHaarMeasure k d) := by
  have hcontinuous : Continuous (fun g ↦ f g • rho g v) :=
    f.continuous.smul (hrho v)
  have hcompact : HasCompactSupport (fun g ↦ f g • rho g v) :=
    f.hasCompactSupport.smul_right
  exact hcontinuous.integrable_of_hasCompactSupport hcompact
def integratedHeckeActionLinear
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hrho : IsStronglyContinuous rho) (f : HeckeFunction k d) :
    V →ₗ[ℂ] V where
  toFun := integratedHeckeAction rho f
  map_add' v w := by
    simp only [integratedHeckeAction, map_add, smul_add]
    exact integral_add
      (integrable_integratedHeckeAction rho hrho f v)
      (integrable_integratedHeckeAction rho hrho f w)
  map_smul' c v := by
    simp only [integratedHeckeAction, map_smul, RingHom.id_apply]
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards with g
    rw [smul_comm]
def heckeL1Norm
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f : HeckeFunction k d) : ℝ :=
  ∫ g, ‖f g‖ ∂normalizedLocalHaarMeasure k d
theorem norm_integratedHeckeAction_le
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hunitary : IsUnitary rho) (f : HeckeFunction k d) (v : V) :
    ‖integratedHeckeAction rho f v‖ ≤ heckeL1Norm f * ‖v‖ := by
  refine (norm_integral_le_integral_norm
    (fun g => f g • rho g v)).trans_eq ?_
  change (∫ g, ‖f g • rho g v‖ ∂normalizedLocalHaarMeasure k d) =
    (∫ g, ‖f g‖ ∂normalizedLocalHaarMeasure k d) * ‖v‖
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with g
  rw [norm_smul]
  congr 1
  exact (actionLinearIsometry rho hunitary g).norm_map v
def integratedHeckeActionContinuousLinear
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hcontinuous : IsStronglyContinuous rho) (hunitary : IsUnitary rho)
    (f : HeckeFunction k d) : V →L[ℂ] V :=
  (integratedHeckeActionLinear rho hcontinuous f).mkContinuous
    (heckeL1Norm f) (norm_integratedHeckeAction_le rho hunitary f)
def fundamentalRepresentationAction
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hcontinuous : IsStronglyContinuous rho) (r : ℕ) : V →ₗ[ℂ] V :=
  integratedHeckeActionLinear rho hcontinuous
    (HeckeFunction.fundamentalHeckeFunction k d r)
def sphericalHeckeEigenvalue
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V)
    (hcontinuous : IsStronglyContinuous rho)
    (f : HeckeFunction k d) (v : V) : ℂ :=
  inner ℂ v (integratedHeckeActionLinear rho hcontinuous f v)
def IsTempered
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V) : Prop :=
  ∃ v w : V, v ≠ 0 ∧ w ≠ 0 ∧
    ∀ epsilon : ℝ, 0 < epsilon →
      MemLp (matrixCoefficient rho v w)
        (ENNReal.ofReal (2 + epsilon)) (normalizedLocalHaarMeasure k d)
def IsIrreducibleUnitarySpherical
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (rho : Representation ℂ (HeckeGroup k d) V) : Prop :=
  Representation.IsIrreducible rho ∧ IsUnitary rho ∧ IsSpherical rho
end QEC.Coding.HighDimensionalExpander.SphericalHecke


