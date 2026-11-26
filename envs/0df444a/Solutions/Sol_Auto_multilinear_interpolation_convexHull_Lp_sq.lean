-- Prove2me | solution 1 for Auto.multilinear_interpolation_convexHull_Lp_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:14:34.158687+00:00
-- url     : https://prove2.me/submissions/4f72a98c-dbc6-43ef-a29b-6e1569412b11

module
public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Definitions.Def_LeanNct_Auto_MultilinearInterpolation
public import Theorems.Thm_Auto_multilinear_interpolation_convexHull_Lp

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
open Auto
namespace Auto
theorem _root_.solution
    {m : ℕ} {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SigmaFinite ν]
    (B : MultilinearMap ℂ (fun _ : Fin (m + 1) ↦ SimpleFunc X ℂ) (Lp ℂ 2 ν))
    (D : ℝ) (hD : 0 < D)
    (S : Set (Fin (m + 1) → ℝ))
    (hSbox : ∀ u ∈ S, ∀ i, 0 < u i ∧ u i ≤ 1)
    (hendpoint : ∀ u ∈ S, ∀ g : Fin (m + 1) → SimpleFunc X ℂ,
      (∀ i, Integrable (g i : X → ℂ) μ) →
        ‖B g‖ₑ ^ 2 ≤ ENNReal.ofReal D * ∏ i,
          eLpNorm (g i : X → ℂ) (multilinearExponentOfReciprocal u i) μ ^ 2)
    (hzero : ∀ (u : Fin (m + 1) → ℝ), (∀ i, 0 < u i ∧ u i ≤ 1) →
      ∀ (g : Fin (m + 1) → SimpleFunc X ℂ) (i : Fin (m + 1)),
        eLpNorm (g i : X → ℂ) (multilinearExponentOfReciprocal u i) μ = 0 →
          ‖B g‖ₑ = 0)
    (u : Fin (m + 1) → ℝ) (hu : u ∈ convexHull ℝ S)
    (g : Fin (m + 1) → SimpleFunc X ℂ)
    (hg : ∀ i, Integrable (g i : X → ℂ) μ) :
    ‖B g‖ₑ ^ 2 ≤ ENNReal.ofReal D * ∏ i,
      eLpNorm (g i : X → ℂ) (multilinearExponentOfReciprocal u i) μ ^ 2 := by
  have hsqrtD : 0 < Real.sqrt D := Real.sqrt_pos.2 hD
  have hcoef : ENNReal.ofReal (Real.sqrt D) ^ 2 = ENNReal.ofReal D := by
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2]
    rw [Real.sq_sqrt hD.le]
  have hprod_sq (w : Fin (m + 1) → ℝ) (r : Fin (m + 1) → SimpleFunc X ℂ) :
      (∏ i, eLpNorm (r i : X → ℂ) (multilinearExponentOfReciprocal w i) μ) ^ 2 =
        ∏ i, eLpNorm (r i : X → ℂ) (multilinearExponentOfReciprocal w i) μ ^ 2 := by
    simpa only using
      (Finset.prod_pow (Finset.univ : Finset (Fin (m + 1))) 2
        (fun i ↦ eLpNorm (r i : X → ℂ) (multilinearExponentOfReciprocal w i) μ)).symm
  have hroot_endpoint : ∀ w ∈ S, ∀ r : Fin (m + 1) → SimpleFunc X ℂ,
      (∀ i, Integrable (r i : X → ℂ) μ) →
        ‖B r‖ₑ ≤ ENNReal.ofReal (Real.sqrt D) * ∏ i,
          eLpNorm (r i : X → ℂ) (multilinearExponentOfReciprocal w i) μ := by
    intro w hw r hr
    apply (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp
    calc
      ‖B r‖ₑ ^ 2 ≤ ENNReal.ofReal D * ∏ i,
          eLpNorm (r i : X → ℂ) (multilinearExponentOfReciprocal w i) μ ^ 2 :=
        hendpoint w hw r hr
      _ = (ENNReal.ofReal (Real.sqrt D) * ∏ i,
          eLpNorm (r i : X → ℂ) (multilinearExponentOfReciprocal w i) μ) ^ 2 := by
        rw [mul_pow, hcoef, hprod_sq]
  have hroot := multilinear_interpolation_convexHull_Lp B (Real.sqrt D) hsqrtD S hSbox
    hroot_endpoint hzero u hu g hg
  calc
    ‖B g‖ₑ ^ 2 ≤ (ENNReal.ofReal (Real.sqrt D) * ∏ i,
        eLpNorm (g i : X → ℂ) (multilinearExponentOfReciprocal u i) μ) ^ 2 :=
      ENNReal.pow_le_pow_left hroot
    _ = ENNReal.ofReal D * ∏ i,
        eLpNorm (g i : X → ℂ) (multilinearExponentOfReciprocal u i) μ ^ 2 := by
      rw [mul_pow, hcoef, hprod_sq]
end Auto
