-- Prove2me | solution 1 for Auto.hasDerivAt_sqrt_curve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:41:00.078429+00:00
-- url     : https://prove2.me/submissions/f9b566e9-1018-4f53-b2b3-c6f73f3a09cc

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_sqrt_sub_posSemidef

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace Auto
theorem _root_.solution {Y : ℝ → Matrix n n ℂ} {Y' : Matrix n n ℂ} {θ₀ η : ℝ} (hη : 0 < η)
    (hpos : ∀ θ, (Y θ - (η : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (hY : ∀ i j, HasDerivAt (fun θ => Y θ i j) (Y' i j) θ₀) :
    ∀ i j, HasDerivAt (fun θ => CFC.sqrt (Y θ) i j) (sylvSol (CFC.sqrt (Y θ₀)) Y' i j) θ₀ := by
  set A : ℝ → Matrix n n ℂ := fun θ => CFC.sqrt (Y θ)
  set A0 := A θ₀
  set X := sylvSol A0 Y'
  have hs : 0 < √η := Real.sqrt_pos.2 hη
  have hAlow : ∀ θ, (A θ - ((√η : ℝ) : ℂ) • (1 : Matrix n n ℂ)).PosSemidef :=
    fun θ => sqrt_sub_posSemidef hη.le (hpos θ)
  have hX := (sylvSol_spec hs (hAlow θ₀) Y').1
  have hAA : ∀ θ, A θ * A θ = Y θ := fun θ =>
    CFC.sqrt_mul_sqrt_self _ (by
      have := (hpos θ).add (Matrix.PosSemidef.smul (Matrix.PosSemidef.one) (by
        exact_mod_cast hη.le : (0 : ℂ) ≤ (η : ℂ)))
      simp only [sub_add_cancel] at this
      exact this.nonneg)
  have hsyl : ∀ θ Z, √(hsSq Z) ≤ √(hsSq (A θ * Z + Z * A0)) / (√η + √η) := fun θ Z =>
    sqrt_hsSq_le_sylvester (by linarith) (hAlow θ) (hAlow θ₀) Z
  have hYc : ∀ i j, Tendsto (fun θ => Y θ i j) (𝓝 θ₀) (𝓝 (Y θ₀ i j)) := fun i j =>
    (hY i j).continuousAt.tendsto
  have hAc : Tendsto (fun θ => √(hsSq (A θ - A0))) (𝓝 θ₀) (𝓝 0) := by
    have hY0 := tendsto_hsSq_sub hYc
    have hb : Tendsto (fun θ => √(hsSq (Y θ - Y θ₀)) / (√η + √η)) (𝓝 θ₀) (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hY0
      simpa using this.div_const (√η + √η)
    refine squeeze_zero (fun θ => Real.sqrt_nonneg _) (fun θ => ?_) hb
    have := hsyl θ (A θ - A0)
    have e : A θ * (A θ - A0) + (A θ - A0) * A0 = Y θ - Y θ₀ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, ← hAA θ, ← hAA θ₀]
      abel
    rwa [e] at this
  have hD : ∀ i j, Tendsto (fun θ => ((θ - θ₀)⁻¹ • (Y θ - Y θ₀)) i j) (𝓝[≠] θ₀) (𝓝 (Y' i j)) := by
    intro i j
    have := (hasDerivAt_iff_tendsto_slope.1 (hY i j))
    refine this.congr fun θ => ?_
    simp [slope_def_module, Matrix.smul_apply, Matrix.sub_apply]
  have hD0 := tendsto_hsSq_sub hD
  have hQ : Tendsto (fun θ => √(hsSq ((θ - θ₀)⁻¹ • (A θ - A0) - X))) (𝓝[≠] θ₀) (𝓝 0) := by
    have hb : Tendsto (fun θ => (√(hsSq ((θ - θ₀)⁻¹ • (Y θ - Y θ₀) - Y')) +
        √(hsSq (A θ - A0)) * √(hsSq X)) / (√η + √η)) (𝓝[≠] θ₀) (𝓝 0) := by
      have h1 := (Real.continuous_sqrt.tendsto 0).comp hD0
      have h2 := (hAc.mono_left (nhdsWithin_le_nhds (s := {θ₀}ᶜ))).mul_const (√(hsSq X))
      have := (h1.add h2).div_const (√η + √η)
      simpa using this
    refine squeeze_zero (fun θ => Real.sqrt_nonneg _) (fun θ => ?_) hb
    set Q := (θ - θ₀)⁻¹ • (A θ - A0)
    have e : A θ * (Q - X) + (Q - X) * A0 = ((θ - θ₀)⁻¹ • (Y θ - Y θ₀) - Y') - (A θ - A0) * X := by
      have e1 : A θ * Q + Q * A0 = (θ - θ₀)⁻¹ • (Y θ - Y θ₀) := by
        simp only [Q, Matrix.mul_smul, Matrix.smul_mul, ← smul_add]
        congr 1
        rw [Matrix.mul_sub, Matrix.sub_mul, ← hAA θ, ← hAA θ₀]
        abel
      rw [Matrix.mul_sub, Matrix.sub_mul, ← hX]
      rw [show A θ * Q - A θ * X + (Q * A0 - X * A0) = (A θ * Q + Q * A0) - (A θ * X + X * A0) by
          abel, e1, Matrix.sub_mul]
      abel
    have h1 := hsyl θ (Q - X)
    rw [e] at h1
    refine h1.trans ?_
    gcongr
    have h3 : √(hsSq (((θ - θ₀)⁻¹ • (Y θ - Y θ₀) - Y') - (A θ - A0) * X)) ≤
        √(hsSq ((θ - θ₀)⁻¹ • (Y θ - Y θ₀) - Y')) + √(hsSq ((A θ - A0) * X)) := by
      set U := (θ - θ₀)⁻¹ • (Y θ - Y θ₀) - Y'
      set V := (A θ - A0) * X
      have hUV := hsRe_comm U V
      have hexp : hsSq (U - V) = hsSq U - 2 * hsRe U V + hsSq V := by
        rw [← hsRe_self, ← hsRe_self U, ← hsRe_self V]
        unfold hsRe
        simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub,
          Complex.sub_re]
        have : ((Vᴴ * U).trace).re = ((Uᴴ * V).trace).re := by
          have := hsRe_comm V U; unfold hsRe at this; exact this
        linarith
      have hcs := abs_hsRe_le U V
      rw [Real.sqrt_le_left (by positivity), hexp]
      have hU := Real.sq_sqrt (hsSq_nonneg U)
      have hV := Real.sq_sqrt (hsSq_nonneg V)
      nlinarith [abs_le.1 hcs, Real.sqrt_nonneg (hsSq U), Real.sqrt_nonneg (hsSq V)]
    refine h3.trans (add_le_add le_rfl ?_)
    rw [← Real.sqrt_mul (hsSq_nonneg _)]
    exact Real.sqrt_le_sqrt (hsSq_mul_le _ _)
  intro i j
  rw [hasDerivAt_iff_tendsto_slope]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun θ => norm_nonneg _) (fun θ => ?_) hQ
  have := norm_entry_le_sqrt_hsSq ((θ - θ₀)⁻¹ • (A θ - A0) - X) i j
  refine le_trans (le_of_eq ?_) this
  simp [slope_def_module, Matrix.smul_apply, Matrix.sub_apply, A, A0]
end Auto
