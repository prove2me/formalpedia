-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCLat
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCLat
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T17:13:42.602382+00:00
-- url     : https://prove2.me/theorems/fb2b78a8-5fe4-4677-90a3-d7f556248519
-- title:
--   PBCLat
-- statement:
--   Definitions and structural lemmas for PBCLat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBCLat.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCStmt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantIntegrals
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeSummability
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalConditionsAndQuotientSplitting
import Definitions.Def_Lemmata_GeneralBFactRightSide_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.PBC
open Formalism.FourierDecayAlt Finset Filter Topology NumberField MeasureTheory
open scoped Pointwise
noncomputable section
open Classical
namespace Lat
theorem psi_add {f : ℕ} (a b : crystallineComparison.V f) : crystallineComparison.psi (a + b) = crystallineComparison.psi a * crystallineComparison.psi b := by
  unfold crystallineComparison.psi
  rw [← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp only [Pi.add_apply, map_add]
  ring
theorem psi_zero {f : ℕ} : crystallineComparison.psi (0 : crystallineComparison.V f) = 1 := by simp [crystallineComparison.psi]
def gen (f : ℕ) (R : ℝ) (p : Fin f × Bool) : crystallineComparison.V f :=
  Pi.single p.1 (if p.2 then (R : ℂ) * Complex.I else (R : ℂ))
def kerPsi {f : ℕ} (σ : crystallineComparison.V f) : AddSubgroup (crystallineComparison.V f) where
  carrier := {z | crystallineComparison.psi (σ * z) = 1}
  zero_mem' := by simp [psi_zero]
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [mul_add, psi_add, ha, hb, one_mul]
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have h := psi_add (σ * -a) (σ * a)
    rw [← mul_add, neg_add_cancel, mul_zero, psi_zero, ha, mul_one] at h
    exact h.symm
def eqv (f : ℕ) : (Σ _ : Fin f, Fin 2) ≃ Fin f × Bool :=
  (Equiv.sigmaEquivProd (Fin f) (Fin 2)).trans (Equiv.prodCongr (Equiv.refl _) finTwoEquiv)
def b0 (f : ℕ) : Module.Basis (Fin f × Bool) ℝ (crystallineComparison.V f) :=
  (Pi.basis fun _ : Fin f => Complex.basisOneI).reindex (eqv f)
def bR (f : ℕ) (R : ℝ) (hR : 0 < R) : Module.Basis (Fin f × Bool) ℝ (crystallineComparison.V f) :=
  (b0 f).isUnitSMul (w := fun _ => R) (fun _ => hR.ne'.isUnit)
end Lat
end
end Formalism.FourierDecayAlt.P.PBC


