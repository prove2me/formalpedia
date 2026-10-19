-- Prove2me | Definitions.Def_QAlgorithms_Defs_BasisCoherence
-- name    : QAlgorithms_Defs_BasisCoherence
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:37:14.649975+00:00
-- url     : https://prove2.me/theorems/a061a519-1e39-4865-89b7-f10f51df87a7
-- title:
--   BasisCoherence
-- statement:
--   BasisCoherence
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\BasisCoherence.lean

import Definitions.Def_QAlgorithms_Defs_Information
noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Coherence

/-- arxiv-1311.0275v3 PDF p.1; arxiv-1311.0275v3 PDF p.3. -/
def l1Coherence {d : ℕ} (rho : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i ≠ j), ‖rho i j‖

/-- Sanity check for the source model (arxiv-1311.0275v3 PDF p.1). -/
example (rho : Matrix (Fin 1) (Fin 1) ℂ) : l1Coherence rho = 0 := by
  simp only [l1Coherence,Fin.sum_univ_one]
  rw [show (Finset.univ.filter fun j : Fin 1 => (0 : Fin 1) ≠ j) = ∅ by decide]
  simp

/-- Sanity check for the source model (arxiv-1311.0275v3 PDF p.1). -/
example : l1Coherence (Matrix.of fun _ _ : Fin 2 => (1/2 : ℂ)) = 1 := by
  simp only [l1Coherence,Fin.sum_univ_two,Matrix.of_apply]
  rw [show (Finset.univ.filter fun j : Fin 2 => (0 : Fin 2) ≠ j) = {1} by decide,
    show (Finset.univ.filter fun j : Fin 2 => (1 : Fin 2) ≠ j) = {0} by decide]
  norm_num

end QAlgorithms.Coherence


