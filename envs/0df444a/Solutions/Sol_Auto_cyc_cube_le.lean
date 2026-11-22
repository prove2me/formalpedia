-- Prove2me | solution 1 for Auto.cyc_cube_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:31:27.2537+00:00
-- url     : https://prove2.me/submissions/ef38e52d-fa7c-438f-83d5-2495d0d34879

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_matCost_add3_le
public import Theorems.Thm_Auto_matCost_anti
public import Theorems.Thm_Auto_matCost_isometry
public import Theorems.Thm_Auto_norm_cubic_sum_le
public import Theorems.Thm_Auto_blk3_mul
public import Theorems.Thm_Auto_blk3_add
public import Theorems.Thm_Auto_blk3_one
public import Theorems.Thm_Auto_emb2_isometry
public import Theorems.Thm_P2M_Auto_emb2_conj_fromBlocks___8e061604a79b
public import Theorems.Thm_P2M_Auto_emb2_conj_fromBlocks___a5369152ae85
public import Theorems.Thm_P2M_Auto_emb2_conj_fromBlocks___e2a989298a5e
public import Theorems.Thm_Auto_blk3_conjTranspose
public import Theorems.Thm_Auto_rowMat_insert
public import Theorems.Thm_Auto_rowMat_gram
public import Theorems.Thm_Auto_cycMb_isHermitian
public import Theorems.Thm_Auto_cycDb_isHermitian
public import Theorems.Thm_Auto_cyc_sq_bound
public import Theorems.Thm_Auto_trace_cube_eigen
public import Theorems.Thm_Auto_matCost_eigen_sandwich

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1611
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1612
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (W0 W1 W2 D0 D1 D2 : Matrix ι ι ℂ)
namespace Auto
theorem _root_.solution (hD0 : D0.IsHermitian) (hD1 : D1.IsHermitian) (hD2 : D2.IsHermitian) {d : ℝ}
    (hd : 0 ≤ d) (h0 : ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - D0 * D0).PosSemidef)
    (h1 : ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - D1 * D1).PosSemidef)
    (h2 : ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - D2 * D2).PosSemidef) :
    ENNReal.ofReal ‖((blk3 (cycDb D0 D1 D2) * blk3 (cycMb W0 W1 W2)) ^ 3).trace‖ ≤
      ENNReal.ofReal (10 * d) * (matCost ((rowMat W0 W2)ᴴ * rowMat W0 W2) ((rowMat W0 W2)ᴴ * D0 *
      rowMat W0 W2) + matCost ((rowMat W1 W0)ᴴ * rowMat W1 W0) ((rowMat W1 W0)ᴴ * D1 * rowMat W1
      W0) + matCost ((rowMat W2 W1)ᴴ * rowMat W2 W1) ((rowMat W2 W1)ᴴ * D2 * rowMat W2 W1)) := by
  set M := blk3 (cycMb W0 W1 W2)
  set D := blk3 (cycDb D0 D1 D2)
  have hMH : M.IsHermitian := cycMb_isHermitian W0 W1 W2
  have hDH : D.IsHermitian := cycDb_isHermitian D0 D1 D2 hD0 hD1 hD2
  have hDd : ((d ^ 2 : ℝ) • (1 : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) - D * D).PosSemidef :=
    cyc_sq_bound D0 D1 D2 h0 h1 h2
  have hMM : (M * M).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self M
    rwa [hMH.eq] at this
  have hPsum : blk3 (cycP0 (ι := ι)) + blk3 cycP1 + blk3 cycP2 = 1 := by
    rw [← blk3_add, ← blk3_add, ← blk3_one]
    congr 1
    simp [cycP0, cycP1, cycP2, Matrix.one_fin_three]
  have hPSDcompl : ∀ P : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ), (blk3 P)ᴴ = blk3 P →
      blk3 P * blk3 P = blk3 P → (M * M - M * blk3 P * M).PosSemidef := by
    intro P hPH hPP
    have e : M * M - M * blk3 P * M = ((1 - blk3 P) * M)ᴴ * ((1 - blk3 P) * M) := by
      have hG : (1 - blk3 P)ᴴ * (1 - blk3 P) = 1 - blk3 P := by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH, Matrix.sub_mul,
          Matrix.mul_sub, Matrix.mul_sub, hPP, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
        abel
      calc M * M - M * blk3 P * M = M * (1 - blk3 P) * M := by
            rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
        _ = M * ((1 - blk3 P)ᴴ * (1 - blk3 P)) * M := by rw [hG]
        _ = _ := by
            rw [Matrix.conjTranspose_mul, hMH.eq]; simp only [Matrix.mul_assoc]
    rw [e]; exact Matrix.posSemidef_conjTranspose_mul_self _
  have hP0H : (blk3 (cycP0 (ι := ι)))ᴴ = blk3 cycP0 := by
    rw [cycP0, blk3_conjTranspose]; simp
  have hP1H : (blk3 (cycP1 (ι := ι)))ᴴ = blk3 cycP1 := by
    rw [cycP1, blk3_conjTranspose]; simp
  have hP2H : (blk3 (cycP2 (ι := ι)))ᴴ = blk3 cycP2 := by
    rw [cycP2, blk3_conjTranspose]; simp
  have hP0P : blk3 (cycP0 (ι := ι)) * blk3 cycP0 = blk3 cycP0 := by
    rw [← blk3_mul]; congr 1
    apply Matrix.ext
    intro v w
    fin_cases v <;> fin_cases w <;> simp [cycP0, Matrix.mul_fin_three]
  have hP1P : blk3 (cycP1 (ι := ι)) * blk3 cycP1 = blk3 cycP1 := by
    rw [← blk3_mul]; congr 1
    apply Matrix.ext
    intro v w
    fin_cases v <;> fin_cases w <;> simp [cycP1, Matrix.mul_fin_three]
  have hP2P : blk3 (cycP2 (ι := ι)) * blk3 cycP2 = blk3 cycP2 := by
    rw [← blk3_mul]; congr 1
    apply Matrix.ext
    intro v w
    fin_cases v <;> fin_cases w <;> simp [cycP2, Matrix.mul_fin_three]
  have hT0 : M * blk3 cycP0 * M =
      emb2 (ι := ι) 1 2 * ((rowMat W0 W2)ᴴ * rowMat W0 W2) * (emb2 (ι := ι) 1 2)ᴴ := by
    rw [rowMat_gram, emb2_conj_fromBlocks₁₂, ← blk3_mul, ← blk3_mul]
    congr 1
    apply Matrix.ext
    intro v w
    fin_cases v <;> fin_cases w <;>
      simp [cycMb, cycP0, Matrix.mul_fin_three]
  have hK0 : M * blk3 cycP0 * D * M =
      emb2 (ι := ι) 1 2 * ((rowMat W0 W2)ᴴ * D0 * rowMat W0 W2) * (emb2 (ι := ι) 1 2)ᴴ := by
    rw [rowMat_insert, emb2_conj_fromBlocks₁₂, ← blk3_mul, ← blk3_mul, ← blk3_mul]
    congr 1
    apply Matrix.ext
    intro v w
    fin_cases v <;> fin_cases w <;>
      simp [cycMb, cycP0, cycDb, Matrix.mul_fin_three, Matrix.mul_assoc]
  have hT1 : M * blk3 cycP1 * M =
      emb2 (ι := ι) 2 0 * ((rowMat W1 W0)ᴴ * rowMat W1 W0) * (emb2 (ι := ι) 2 0)ᴴ := by
    rw [rowMat_gram, emb2_conj_fromBlocks₂₀, ← blk3_mul, ← blk3_mul]
    congr 1
    apply Matrix.ext
    intro v w
    fin_cases v <;> fin_cases w <;>
      simp [cycMb, cycP1, Matrix.mul_fin_three]
  have hK1 : M * blk3 cycP1 * D * M =
      emb2 (ι := ι) 2 0 * ((rowMat W1 W0)ᴴ * D1 * rowMat W1 W0) * (emb2 (ι := ι) 2 0)ᴴ := by
    rw [rowMat_insert, emb2_conj_fromBlocks₂₀, ← blk3_mul, ← blk3_mul, ← blk3_mul]
    congr 1
    apply Matrix.ext
    intro v w
    fin_cases v <;> fin_cases w <;>
      simp [cycMb, cycP1, cycDb, Matrix.mul_fin_three, Matrix.mul_assoc]
  have hT2 : M * blk3 cycP2 * M =
      emb2 (ι := ι) 0 1 * ((rowMat W2 W1)ᴴ * rowMat W2 W1) * (emb2 (ι := ι) 0 1)ᴴ := by
    rw [rowMat_gram, emb2_conj_fromBlocks₀₁, ← blk3_mul, ← blk3_mul]
    congr 1
    apply Matrix.ext
    intro v w
    fin_cases v <;> fin_cases w <;>
      simp [cycMb, cycP2, Matrix.mul_fin_three]
  have hK2 : M * blk3 cycP2 * D * M =
      emb2 (ι := ι) 0 1 * ((rowMat W2 W1)ᴴ * D2 * rowMat W2 W1) * (emb2 (ι := ι) 0 1)ᴴ := by
    rw [rowMat_insert, emb2_conj_fromBlocks₀₁, ← blk3_mul, ← blk3_mul, ← blk3_mul]
    congr 1
    apply Matrix.ext
    intro v w
    fin_cases v <;> fin_cases w <;>
      simp [cycMb, cycP2, cycDb, Matrix.mul_fin_three, Matrix.mul_assoc]
  have hc : ∀ (P : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ)) (p r : Fin 3) (hpr : p ≠ r) (W V Dv :
      Matrix ι ι ℂ), (blk3 P)ᴴ = blk3 P → blk3 P * blk3 P = blk3 P →
      M * blk3 P * M = emb2 (ι := ι) p r * ((rowMat W V)ᴴ * rowMat W V) * (emb2 (ι := ι) p r)ᴴ →
      M * blk3 P * D * M = emb2 (ι := ι) p r * ((rowMat W V)ᴴ * Dv * rowMat W V) * (emb2 (ι := ι) p
          r)ᴴ →
      matCost (M * M) (M * blk3 P * D * M) ≤
        matCost ((rowMat W V)ᴴ * rowMat W V) ((rowMat W V)ᴴ * Dv * rowMat W V) := by
    intro P p r hpr W V Dv hPH hPP hT hK
    rw [← matCost_isometry (emb2 (ι := ι) p r) (emb2_isometry hpr)
        (Matrix.posSemidef_conjTranspose_mul_self _), ← hT, ← hK]
    exact matCost_anti hMM (Matrix.le_iff.2 (hPSDcompl P hPH hPP)) _
  have e0 := hc _ 1 2 (by decide) W0 W2 D0 hP0H hP0P hT0 hK0
  have e1 := hc _ 2 0 (by decide) W1 W0 D1 hP1H hP1P hT1 hK1
  have e2 := hc _ 0 1 (by decide) W2 W1 D2 hP2H hP2P hT2 hK2
  have hsplit : M * blk3 cycP0 * D * M + M * blk3 cycP1 * D * M + M * blk3 cycP2 * D * M =
      M * D * M := by
    rw [← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.add_mul,
      ← Matrix.mul_add, ← Matrix.mul_add, hPsum, Matrix.mul_one]
  have hb3 := matCost_add3_le (M * M) (M * blk3 cycP0 * D * M) (M * blk3 cycP1 * D * M) (M * blk3
      cycP2 * D * M)
  rw [hsplit] at hb3
  obtain ⟨U, hUdef⟩ : ∃ U, U = hMH.eigenvectorUnitary := ⟨_, rfl⟩
  obtain ⟨m, hmdef⟩ : ∃ m, m = hMH.eigenvalues := ⟨_, rfl⟩
  have hU'U : star (U : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) * U = 1 := Unitary.coe_star_mul_self U
  have hUU : (U : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) *
      star (U : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) = 1 := Unitary.coe_mul_star_self U
  have hMU : M = (U : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) * diagonal (fun i => (m i : ℂ)) *
      star (U : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) := by
    rw [hUdef, hmdef]
    have := hMH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  obtain ⟨Dt, hDtdef⟩ : ∃ Dt, Dt = star (U : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) * D * U :=
    ⟨_, rfl⟩
  have hDU : D = (U : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) * Dt *
      star (U : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) := by
    rw [hDtdef]
    simp only [← Matrix.mul_assoc, hUU, Matrix.one_mul]
    rw [Matrix.mul_assoc, hUU, Matrix.mul_one]
  have hDtH : Dt.IsHermitian := by
    rw [hDtdef, Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose, hDH.eq, Matrix.mul_assoc]
  have hDtd : ((d ^ 2 : ℝ) • (1 : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) - Dt * Dt).PosSemidef := by
    have := hDd.conjTranspose_mul_mul_same (U : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ)
    convert this using 1
    rw [← Matrix.star_eq_conjTranspose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hU'U, hDtdef]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) (star (U : Matrix (Fin 3 × ι) (Fin
        3 × ι) ℂ)), hUU, Matrix.one_mul]
  have hcore := norm_cubic_sum_le m hDtH hd hDtd
  have htr : ((D * M) ^ 3).trace =
      ∑ i, ∑ j, ∑ k, ((m i * m j * m k : ℝ) : ℂ) * Dt i j * Dt j k * Dt k i := by
    rw [hDU, hMU]; exact trace_cube_eigen U m Dt
  rw [htr]
  have hcostQ : matCost (M * M) (M * D * M) = ENNReal.ofReal ((3 / 2) *
      ∑ i, ∑ j, |m i| ^ 2 * |m j| ^ 2 * ‖Dt i j‖ ^ 2 / (|m i| + |m j|)) := by
    rw [hMU, hDtdef]
    exact matCost_eigen_sandwich U m D
  calc ENNReal.ofReal ‖∑ i, ∑ j, ∑ k, ((m i * m j * m k : ℝ) : ℂ) * Dt i j * Dt j k * Dt k i‖
      ≤ ENNReal.ofReal (5 * d * ∑ i, ∑ j, |m i| ^ 2 * |m j| ^ 2 * ‖Dt i j‖ ^ 2 / (|m i| + |m j|)) :=
          ENNReal.ofReal_le_ofReal hcore
    _ = ENNReal.ofReal (10 / 3 * d) * matCost (M * M) (M * D * M) := by
        rw [hcostQ, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
    _ ≤ ENNReal.ofReal (10 / 3 * d) * (3 * (matCost (M * M) (M * blk3 cycP0 * D * M) +
          matCost (M * M) (M * blk3 cycP1 * D * M) + matCost (M * M) (M * blk3 cycP2 * D * M)))
        := by gcongr
    _ ≤ ENNReal.ofReal (10 / 3 * d) * (3 * (
          matCost ((rowMat W0 W2)ᴴ * rowMat W0 W2) ((rowMat W0 W2)ᴴ * D0 * rowMat W0 W2) +
          matCost ((rowMat W1 W0)ᴴ * rowMat W1 W0) ((rowMat W1 W0)ᴴ * D1 * rowMat W1 W0) +
          matCost ((rowMat W2 W1)ᴴ * rowMat W2 W1) ((rowMat W2 W1)ᴴ * D2 * rowMat W2 W1))) := by
        gcongr
    _ = _ := by
        rw [← mul_assoc]
        congr 1
        rw [← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
end Auto
