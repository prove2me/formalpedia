-- Prove2me | solution 1 for Auto.HeatData.S_psd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:46:50.362448+00:00
-- url     : https://prove2.me/submissions/b08acf52-2b1f-44e1-a4a6-32f62dcb0088

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_wGram_posSemidef
public import Theorems.Thm_Auto_gweight_nonneg

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Auto.HeatData
variable (Hd : HeatData ι) (p σ : Fin 3 → ℝ)
namespace Auto.HeatData
theorem _root_.solution (hh : 0 ≤ Hd.h) (hσ : ∀ k, 0 < σ k) (v : Fin 3) (k : Fin 3) :
    (wGram (Hd.Bprev p σ v) (Hd.w p σ k)).PosSemidef ∧ (wGram (Hd.Bnext p σ v) (Hd.w p σ
      k)).PosSemidef :=
  ⟨wGram_posSemidef _ fun i => gweight_nonneg _ hh (hσ k) _ i,
    wGram_posSemidef _ fun i => gweight_nonneg _ hh (hσ k) _ i⟩
end Auto.HeatData
