-- Prove2me | solution 1 for Auto.HeatData.e_mixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:19:05.910625+00:00
-- url     : https://prove2.me/submissions/91bae9e9-5e9a-4a7c-bafd-f7980d9c3d84

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_hasDerivAt_energy_hessian
public import Theorems.Thm_Auto_wGram_posSemidef
public import Theorems.Thm_Auto_wGram_isHermitian
public import Theorems.Thm_Auto_hasDerivAt_wGram
public import Theorems.Thm_Auto_gweight_nonneg
public import Theorems.Thm_Auto_hasDerivAt_gweight_p
public import Theorems.Thm_Auto_HeatData_dw_def
public import Theorems.Thm_Auto_HeatData_fin3_ne_succ
public import Theorems.Thm_Auto_HeatData_fin3_succ_ne_pred
public import Theorems.Thm_Auto_HeatData_Bprev_update
public import Theorems.Thm_Auto_HeatData_S_update_next
public import Theorems.Thm_Auto_HeatData_S_psd

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
theorem _root_.solution (hh : 0 ≤ Hd.h) {η : ℝ} (hη : 0 < η) (hσ : ∀ k, 0 < σ k) (v : Fin 3) :
    HasDerivAt (fun q => tr32 η (Hd.S (Function.update p (v + 1) q) σ v) (Hd.Pprev
      (Function.update p (v + 1) q) σ v)) (Hd.Z p σ η v) (p (v + 1)) := by
  set C := wGram (Hd.Bprev p σ v) (Hd.w p σ (v - 1))
  set B := Hd.Bnext p σ v
  have hC := (S_psd Hd p σ hh hσ v (v - 1)).1
  have hPd : ∀ i j, HasDerivAt (fun q => (C + wGram B (gweight Hd.u Hd.h (σ (v + 1)) q)) i j) (wGram
      B (Hd.dw p σ (v + 1)) i j) (p (v + 1)) := by
    intro i j
    have := (hasDerivAt_wGram B (f := fun q => gweight Hd.u Hd.h (σ (v + 1)) q) (fun k =>
        hasDerivAt_gweight_p Hd.u Hd.h (σ (v + 1)) (p (v + 1)) k) i j).const_add (C i j)
    simpa [dw_def] using this
  have hPpsd : ∀ q, (C + wGram B (gweight Hd.u Hd.h (σ (v + 1)) q)).PosSemidef := fun q =>
    hC.add (wGram_posSemidef B fun i => gweight_nonneg _ hh (hσ _) q i)
  have hPprev : ∀ q, Hd.Pprev (Function.update p (v + 1) q) σ v = Hd.Pprev p σ v := by
    intro q
    rw [Pprev, Pprev, Bprev_update Hd p σ (fin3_ne_succ v).symm, dw_def, dw_def,
      Function.update_of_ne (fin3_succ_ne_pred v).symm]
  have hH := hasDerivAt_energy_hessian (G := fun _ => Hd.Pprev p σ v) (G' := 0) hη hPpsd hPd (fun i
      j => hasDerivAt_const _ _) (wGram_isHermitian _ _)
  have hS0 : Hd.S p σ v = C + wGram B (gweight Hd.u Hd.h (σ (v + 1)) (p (v + 1))) := by
    have := S_update_next Hd p σ hh hσ v (p (v + 1))
    rwa [Function.update_eq_self] at this
  have e1 : (fun q => tr32 η (Hd.S (Function.update p (v + 1) q) σ v) (Hd.Pprev (Function.update p
      (v + 1) q) σ v)) = fun q => (3 / 2) * ((CFC.sqrt (C + wGram B (gweight Hd.u Hd.h (σ (v + 1))
      q) + (η : ℂ) • 1) *
          Hd.Pprev p σ v).trace).re := by
    funext q; rw [tr32, S_update_next Hd p σ hh hσ, hPprev]
  rw [e1]
  refine hH.congr_deriv ?_
  simp [Z, hS0, Pnext, B]
end Auto.HeatData
