-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_PhiDiff
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_PhiDiff
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T08:45:06.851023+00:00
-- url     : https://prove2.me/theorems/a7e255a4-d82e-584b-9009-90e9af51b47e
-- title:
--   Phi Diff
-- statement:
--   Definitions and structural lemmas for Phi Diff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/PhiDiff.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NormedSpace
namespace PI.RhsWLim.W
open PI.RhsWLim
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {k r : ℕ}
lemma opBeta_add (q q' : TrE k) (a : Fin k) :
    opBeta k (q + q') a = opBeta k q a + opBeta k q' a := by
  simp only [opBeta, PiLp.add_apply, Complex.ofReal_add]; ring
lemma opBeta_smul (c : ℝ) (q : TrE k) (a : Fin k) :
    opBeta k (c • q) a = (c : ℂ) * opBeta k q a := by
  simp only [opBeta, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul]; ring
def opGenLin (k r : ℕ) : TrE k →ₗ[ℝ] Mat k r where
  toFun := opGen k r
  map_add' q q' := by
    ext i j
    simp only [opGen, Matrix.add_apply]
    split_ifs <;> simp [opBeta_add, star_add]; ring
  map_smul' c q := by
    ext i j
    simp only [opGen, Matrix.smul_apply, RingHom.id_apply]
    split_ifs <;> simp [opBeta_smul, Complex.real_smul, star_mul', Complex.conj_ofReal]; ring
def opGenL (k r : ℕ) : TrE k →L[ℝ] Mat k r := LinearMap.toContinuousLinearMap (opGenLin k r)
@[simp] lemma opGenL_apply (q : TrE k) : opGenL k r q = opGen k r q := rfl
def mvL (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Mat k r →L[ℝ] (Fin (2 * r + k + 1) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M *ᵥ v
      map_add' := fun M N => Matrix.add_mulVec M N v
      map_smul' := fun c M => by simp [Matrix.smul_mulVec] }
@[simp] lemma mvL_apply (v : Fin (2 * r + k + 1) → ℂ) (M : Mat k r) : mvL k r v M = M *ᵥ v := rfl
def psiV (k r : ℕ) (T' : ℝ) (q : TrE k) : Fin (2 * r + k + 1) → ℂ :=
  NormedSpace.exp (opGen k r q) *ᵥ opBase k r T'
def dgn (T' : ℝ) : Option (Fin k × Bool) → ℝ := fun o => match o with
  | none => 1
  | some _ => Real.sqrt T' / Real.sqrt 2
def DL (k : ℕ) (T' : ℝ) : TrE k →L[ℝ] TrE k := LinearMap.toContinuousLinearMap
  { toFun := fun q => (WithLp.equiv 2 (Option (Fin k × Bool) → ℝ)).symm (fun o => dgn T' o * q o)
    map_add' := fun q q' => by ext o; simp [mul_add]
    map_smul' := fun c q => by ext o; simp; ring }
end PI.RhsWLim.W


