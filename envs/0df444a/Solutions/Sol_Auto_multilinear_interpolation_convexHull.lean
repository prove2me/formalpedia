-- Prove2me | solution 1 for Auto.multilinear_interpolation_convexHull
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:13:04.340528+00:00
-- url     : https://prove2.me/submissions/8056d59c-c160-4695-bf76-9ba65ee05b8c

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
public import Theorems.Thm_Auto_convexHull_subset_of_binary
public import Theorems.Thm_Auto_multilinear_interpolation_two_endpoint
section
@[expose] public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
namespace Auto
private theorem aux_multilinearExponentOfReciprocal_inv
    {m : ℕ} (u : Fin (m + 1) → ℝ) (i : Fin (m + 1)) (hui : 0 < u i) :
    (multilinearExponentOfReciprocal u i)⁻¹ = ENNReal.ofReal (u i) := by
  rw [multilinearExponentOfReciprocal, ENNReal.ofReal_inv_of_pos hui]
  simp
private theorem aux_one_le_multilinearExponentOfReciprocal
    {m : ℕ} (u : Fin (m + 1) → ℝ) (i : Fin (m + 1))
    (hui : 0 < u i) (hui_one : u i ≤ 1) :
    1 ≤ multilinearExponentOfReciprocal u i := by
  rw [multilinearExponentOfReciprocal, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal ((one_le_inv₀ hui).mpr hui_one)
private theorem aux_reciprocal_box_binary
    {m : ℕ} (u v : Fin (m + 1) → ℝ) (a b : ℝ)
    (hu : ∀ i, 0 < u i ∧ u i ≤ 1) (hv : ∀ i, 0 < v i ∧ v i ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ∀ i, 0 < (a • u + b • v) i ∧ (a • u + b • v) i ≤ 1 := by
  intro i
  change 0 < a * u i + b * v i ∧ a * u i + b * v i ≤ 1
  constructor
  · by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      rw [ha0, hb1]
      simpa using (hv i).1
    · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      exact lt_of_lt_of_le (mul_pos hapos (hu i).1)
        (le_add_of_nonneg_right (mul_nonneg hb (hv i).1.le))
  · calc
      a * u i + b * v i ≤ a * 1 + b * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left (hu i).2 ha)
          (mul_le_mul_of_nonneg_left (hv i).2 hb)
      _ = 1 := by linarith
private theorem aux_multilinearExponentOfReciprocal_interpolation
    {m : ℕ} (u v : Fin (m + 1) → ℝ) (a b : ℝ)
    (hu : ∀ i, 0 < u i ∧ u i ≤ 1) (hv : ∀ i, 0 < v i ∧ v i ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (i : Fin (m + 1)) :
    (multilinearExponentOfReciprocal (a • u + b • v) i)⁻¹ =
      ENNReal.ofReal a * (multilinearExponentOfReciprocal u i)⁻¹ +
        ENNReal.ofReal b * (multilinearExponentOfReciprocal v i)⁻¹ := by
  have hw := aux_reciprocal_box_binary u v a b hu hv ha hb hab i
  rw [aux_multilinearExponentOfReciprocal_inv _ i hw.1,
    aux_multilinearExponentOfReciprocal_inv _ i (hu i).1,
    aux_multilinearExponentOfReciprocal_inv _ i (hv i).1]
  change ENNReal.ofReal (a * u i + b * v i) =
    ENNReal.ofReal a * ENNReal.ofReal (u i) + ENNReal.ofReal b * ENNReal.ofReal (v i)
  rw [ENNReal.ofReal_add (mul_nonneg ha (hu i).1.le) (mul_nonneg hb (hv i).1.le),
    ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb]
section
end
end Auto
end
end

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
    (B : MultilinearMap ℂ (fun _ : Fin (m + 1) ↦ SimpleFunc X ℂ) (Y → ℂ))
    (q : ENNReal) (hq : 1 ≤ q) (A : ℝ) (hA : 0 < A)
    (hB_measurable : ∀ u : Fin (m + 1) → SimpleFunc X ℂ,
      (∀ i, Integrable (u i : X → ℂ) μ) → Measurable (B u))
    (hB_pair_integrable : ∀ (u : Fin (m + 1) → SimpleFunc X ℂ)
      (h : SimpleFunc Y ℂ),
      (∀ i, Integrable (u i : X → ℂ) μ) → Integrable (h : Y → ℂ) ν →
        Integrable (fun y ↦ B u y * h y) ν)
    (S : Set (Fin (m + 1) → ℝ))
    (hSbox : ∀ u ∈ S, ∀ i, 0 < u i ∧ u i ≤ 1)
    (hendpoint : ∀ u ∈ S, ∀ g : Fin (m + 1) → SimpleFunc X ℂ,
      (∀ i, Integrable (g i : X → ℂ) μ) →
        eLpNorm (B g) q ν ≤ ENNReal.ofReal A * ∏ i,
          eLpNorm (g i : X → ℂ) (multilinearExponentOfReciprocal u i) μ)
    (hzero : ∀ (u : Fin (m + 1) → ℝ), (∀ i, 0 < u i ∧ u i ≤ 1) →
      ∀ (g : Fin (m + 1) → SimpleFunc X ℂ) (i : Fin (m + 1)),
        eLpNorm (g i : X → ℂ) (multilinearExponentOfReciprocal u i) μ = 0 →
          eLpNorm (B g) q ν = 0)
    (u : Fin (m + 1) → ℝ) (hu : u ∈ convexHull ℝ S)
    (g : Fin (m + 1) → SimpleFunc X ℂ)
    (hg : ∀ i, Integrable (g i : X → ℂ) μ) :
    eLpNorm (B g) q ν ≤ ENNReal.ofReal A * ∏ i,
      eLpNorm (g i : X → ℂ) (multilinearExponentOfReciprocal u i) μ := by
  let G : Set (Fin (m + 1) → ℝ) := {w | (∀ i, 0 < w i ∧ w i ≤ 1) ∧
    ∀ h : Fin (m + 1) → SimpleFunc X ℂ,
      (∀ i, Integrable (h i : X → ℂ) μ) →
        eLpNorm (B h) q ν ≤ ENNReal.ofReal A *
          eLpNorm (h 0 : X → ℂ) (multilinearExponentOfReciprocal w 0) μ *
            ∏ i : Fin m, eLpNorm (h i.succ : X → ℂ)
              (multilinearExponentOfReciprocal w i.succ) μ}
  have hSsub : S ⊆ G := by
    intro w hw
    refine ⟨hSbox w hw, ?_⟩
    intro h hh
    simpa only [Fin.prod_univ_succ, mul_assoc] using hendpoint w hw h hh
  have hbinary : ∀ x ∈ G, ∀ y ∈ G, ∀ a b : ℝ,
      0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ G := by
    intro x hx y hy a b ha hb hab
    have hxbox : ∀ i, 0 < x i ∧ x i ≤ 1 := hx.1
    have hybox : ∀ i, 0 < y i ∧ y i ≤ 1 := hy.1
    have hwbox : ∀ i, 0 < (a • x + b • y) i ∧ (a • x + b • y) i ≤ 1 :=
      aux_reciprocal_box_binary x y a b hxbox hybox ha hb hab
    refine ⟨hwbox, ?_⟩
    intro h hh
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      have hxy : a • x + b • y = y := by
        ext i
        simp [ha0, hb1]
      simpa only [hxy] using hy.2 h hh
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by linarith
      have hxy : a • x + b • y = x := by
        ext i
        simp [hb0, ha1]
      simpa only [hxy] using hx.2 h hh
    have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hθ : b ∈ Set.Ioo 0 1 := ⟨hbpos, by linarith⟩
    have haeq : a = 1 - b := by linarith
    have hp₀ : ∀ i, 1 ≤ multilinearExponentOfReciprocal x i := by
      intro i
      exact aux_one_le_multilinearExponentOfReciprocal x i (hxbox i).1 (hxbox i).2
    have hp₁ : ∀ i, 1 ≤ multilinearExponentOfReciprocal y i := by
      intro i
      exact aux_one_le_multilinearExponentOfReciprocal y i (hybox i).1 (hybox i).2
    have hp : ∀ i, 1 ≤ multilinearExponentOfReciprocal (a • x + b • y) i := by
      intro i
      exact aux_one_le_multilinearExponentOfReciprocal (a • x + b • y) i
        (hwbox i).1 (hwbox i).2
    have hptop : ∀ i, multilinearExponentOfReciprocal (a • x + b • y) i ≠ ∞ := by
      intro i
      exact ENNReal.ofReal_ne_top
    have hinterp : ∀ i,
        (multilinearExponentOfReciprocal (a • x + b • y) i)⁻¹ =
          ENNReal.ofReal (1 - b) * (multilinearExponentOfReciprocal x i)⁻¹ +
            ENNReal.ofReal b * (multilinearExponentOfReciprocal y i)⁻¹ := by
      intro i
      simpa only [haeq] using
        aux_multilinearExponentOfReciprocal_interpolation x y a b hxbox hybox ha hb hab i
    have hBx : ∀ r : Fin (m + 1) → SimpleFunc X ℂ,
        (∀ i, Integrable (r i : X → ℂ) μ) →
          eLpNorm (B r) q ν ≤ ENNReal.ofReal A * ∏ i,
            eLpNorm (r i : X → ℂ) (multilinearExponentOfReciprocal x i) μ := by
      intro r hr
      simpa only [Fin.prod_univ_succ, mul_assoc] using hx.2 r hr
    have hBy : ∀ r : Fin (m + 1) → SimpleFunc X ℂ,
        (∀ i, Integrable (r i : X → ℂ) μ) →
          eLpNorm (B r) q ν ≤ ENNReal.ofReal A * ∏ i,
            eLpNorm (r i : X → ℂ) (multilinearExponentOfReciprocal y i) μ := by
      intro r hr
      simpa only [Fin.prod_univ_succ, mul_assoc] using hy.2 r hr
    have hzero' : ∀ (r : Fin (m + 1) → SimpleFunc X ℂ) (i : Fin (m + 1)),
        eLpNorm (r i : X → ℂ) (multilinearExponentOfReciprocal (a • x + b • y) i) μ = 0 →
          eLpNorm (B r) q ν = 0 :=
      hzero (a • x + b • y) hwbox
    have hAinterp : Real.rpow A (1 - b) * Real.rpow A b = A := by
      calc
        Real.rpow A (1 - b) * Real.rpow A b = Real.rpow A ((1 - b) + b) :=
          (Real.rpow_add hA _ _).symm
        _ = A := by
          rw [show (1 - b) + b = 1 by ring]
          simp
    simpa only [hAinterp] using
      multilinear_interpolation_two_endpoint B hθ hp₀ hp₁ hp hptop hinterp hq hA hA
        hB_measurable hB_pair_integrable hBx hBy hzero' h hh
  have huG : u ∈ G := convexHull_subset_of_binary hSsub hbinary hu
  simpa only [Fin.prod_univ_succ, mul_assoc] using huG.2 g hg
end Auto
