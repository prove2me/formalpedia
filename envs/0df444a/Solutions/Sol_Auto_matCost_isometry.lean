-- Prove2me | solution 1 for Auto.matCost_isometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:42:16.825733+00:00
-- url     : https://prove2.me/submissions/08419f03-c705-43da-a9af-77c3323a74d5

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT

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
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace Auto
theorem _root_.solution {k : Type*} [Fintype k] [DecidableEq k] (E : Matrix k n ℂ)
    (hE : Eᴴ * E = 1) {T : Matrix n n ℂ} (hT : T.PosSemidef) (K : Matrix n n ℂ) :
    matCost (E * T * Eᴴ) (E * K * Eᴴ) = matCost T K := by
  set S := CFC.sqrt T
  have hSp : S.PosSemidef := (CFC.sqrt_nonneg T).posSemidef
  have hSS : S * S = T := CFC.sqrt_mul_sqrt_self T hT.nonneg
  have hE2 : ∀ (Z : Matrix n n ℂ), Eᴴ * (E * Z) = Z := by
    intro Z; rw [← Matrix.mul_assoc, hE, Matrix.one_mul]
  have hE2k : ∀ (Z : Matrix n k ℂ), Eᴴ * (E * Z) = Z := by
    intro Z; rw [← Matrix.mul_assoc, hE, Matrix.one_mul]
  have hsq : CFC.sqrt (E * T * Eᴴ) = E * S * Eᴴ := by
    have hnn : 0 ≤ E * S * Eᴴ := (hSp.mul_mul_conjTranspose_same E).nonneg
    refine CFC.sqrt_unique ?_ hnn
    simp only [Matrix.mul_assoc, hE2k]
    rw [← Matrix.mul_assoc S S, hSS]
  have hcyc : ∀ (X Y : Matrix n n ℂ), hsRe (E * X * Eᴴ) (E * Y * Eᴴ) = hsRe X Y := by
    intro X Y
    unfold hsRe
    congr 1
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      hE2k]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc, hE, Matrix.mul_one]
  have hEE : ∀ (X Y : Matrix n n ℂ), E * X * Eᴴ * (E * Y * Eᴴ) = E * (X * Y) * Eᴴ := by
    intro X Y
    simp only [Matrix.mul_assoc, hE2k]
  set G : Matrix k k ℂ := 1 - E * Eᴴ
  have hGH : Gᴴ = G := by
    simp only [G, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hGG : G * G = G := by
    simp only [G, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc, hE2k]
    abel
  have hS0 : (S - ((0 : ℝ) : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by simpa using hSp
  apply le_antisymm
  ·
    rw [matCost]
    refine iSup_le fun X => ?_
    refine le_trans ?_ (le_iSup (fun X => ENNReal.ofReal ((3 / 2) * costInt S K X)) (Eᴴ * X * E))
    apply ENNReal.ofReal_le_ofReal
    rw [hsq]
    unfold costInt
    have h1 : hsRe (E * K * Eᴴ) X = hsRe K (Eᴴ * X * E) := by
      unfold hsRe
      congr 1
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    have hq1 : hsRe (Eᴴ * X * E) (S * (Eᴴ * X * E)) ≤ hsRe X (E * S * Eᴴ * X) := by
      set B := Eᴴ * X
      have hnn := re_trace_conj_mul_mul_ge hS0 (B * G)
      simp only [zero_mul] at hnn
      have e1 : hsRe X (E * S * Eᴴ * X) = ((Bᴴ * S * B).trace).re := by
        unfold hsRe; congr 1
        simp only [B, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
      have e2 : hsRe (Eᴴ * X * E) (S * (Eᴴ * X * E)) = ((Bᴴ * S * B * (E * Eᴴ)).trace).re := by
        unfold hsRe; congr 1
        simp only [B, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
        rw [Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]
      have e3 : ((B * G)ᴴ * S * (B * G)).trace = (Bᴴ * S * B).trace - (Bᴴ * S * B * (E * Eᴴ)).trace
          := by
        rw [Matrix.conjTranspose_mul, hGH]
        calc (G * Bᴴ * S * (B * G)).trace = (G * (Bᴴ * S * B * G)).trace := by
              simp only [Matrix.mul_assoc]
          _ = (Bᴴ * S * B * G * G).trace := by rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
          _ = (Bᴴ * S * B * G).trace := by rw [Matrix.mul_assoc _ G G, hGG]
          _ = _ := by simp only [G, Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub]
      rw [e1, e2]
      rw [e3, Complex.sub_re] at hnn
      linarith
    have hq2 : hsRe (Eᴴ * X * E) ((Eᴴ * X * E) * S) ≤ hsRe X (X * (E * S * Eᴴ)) := by
      set C := X * E
      have hnn := re_trace_conj_mul_mul_ge hS0 (G * C)ᴴ
      simp only [zero_mul, Matrix.conjTranspose_conjTranspose] at hnn
      have e1 : hsRe X (X * (E * S * Eᴴ)) = ((Cᴴ * C * S).trace).re := by
        unfold hsRe; congr 1
        simp only [C, Matrix.conjTranspose_mul, Matrix.mul_assoc]
        rw [Matrix.trace_mul_comm Eᴴ]
        simp only [Matrix.mul_assoc]
      have e2 : hsRe (Eᴴ * X * E) ((Eᴴ * X * E) * S) = ((Cᴴ * (E * Eᴴ) * C * S).trace).re := by
        unfold hsRe; congr 1
        simp only [C, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
      have e3 : ((G * C) * S * (G * C)ᴴ).trace = (Cᴴ * C * S).trace - (Cᴴ * (E * Eᴴ) * C * S).trace
          := by
        rw [Matrix.conjTranspose_mul, hGH]
        calc (G * C * S * (Cᴴ * G)).trace = (G * (C * S * Cᴴ * G)).trace := by
              simp only [Matrix.mul_assoc]
          _ = (C * S * Cᴴ * G * G).trace := by rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
          _ = (C * S * Cᴴ * G).trace := by rw [Matrix.mul_assoc _ G G, hGG]
          _ = (G * (C * S * Cᴴ)).trace := Matrix.trace_mul_comm _ _
          _ = _ := by
              simp only [G, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub]
              congr 1
              · rw [Matrix.trace_mul_comm (C * S) Cᴴ]; simp only [C, Matrix.mul_assoc]
              · simp only [Matrix.mul_assoc]
                rw [Matrix.trace_mul_comm Cᴴ]
                simp only [Matrix.mul_assoc]
      rw [e1, e2]
      rw [e3, Complex.sub_re] at hnn
      linarith
    rw [h1]
    nlinarith [hq1, hq2]
  ·
    rw [matCost]
    refine iSup_le fun X => ?_
    refine le_trans (le_of_eq ?_) (le_iSup (fun Y => ENNReal.ofReal ((3 / 2) *
      costInt (CFC.sqrt (E * T * Eᴴ)) (E * K * Eᴴ) Y)) (E * X * Eᴴ))
    rw [hsq]
    unfold costInt
    rw [hcyc, hEE, hEE, hcyc, hcyc]
end Auto
