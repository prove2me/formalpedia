-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T13:30:52.889493+00:00
-- url     : https://prove2.me/theorems/0d66875d-95b0-4049-8f33-d5badcf4ef8d
-- title:
--   Index Defs
-- statement:
--   Definitions and structural lemmas for Index Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/IndexDefs.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
open NumberField Matrix
namespace PI.UnitaryGroupMassFormula.LCG
def oLat (K : Type) [Field K] [NumberField K] (k : ℕ) : Submodule (𝓞 K) (Fin k → K) :=
  LinearMap.range (LinearMap.compLeft (Algebra.linearMap (𝓞 K) K) (Fin k))
def dualL {K : Type} [Field K] [NumberField K] {k : ℕ} (X : Submodule (𝓞 K) (Fin k → K)) :
    Submodule (𝓞 K) (Fin k → K) where
  carrier := {t | ∀ s ∈ X, s ⬝ᵥ t ∈ (algebraMap (𝓞 K) K).range}
  add_mem' := by
    intro a b ha hb s hs
    rw [Set.mem_setOf_eq] at ha hb
    rw [dotProduct_add]
    exact add_mem (ha s hs) (hb s hs)
  zero_mem' := by
    intro s _
    rw [dotProduct_zero]
    exact zero_mem _
  smul_mem' := by
    intro c t ht s hs
    rw [Set.mem_setOf_eq] at ht
    have h1 := ht (c • s) (X.smul_mem c hs)
    have h2 : s ⬝ᵥ (c • t) = (c • s) ⬝ᵥ t := by
      simp only [dotProduct, Pi.smul_apply, Algebra.smul_def]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [h2]
    exact h1
def DualIdx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (k : ℕ) (X Y : Submodule (𝓞 K) (Fin k → K)), X ≤ Y →
    X.toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0 →
    (dualL Y).toAddSubgroup.relIndex (dualL X).toAddSubgroup ≠ 0 ∧
      (dualL Y).toAddSubgroup.relIndex (dualL X).toAddSubgroup ≤ X.toAddSubgroup.relIndex Y.toAddSubgroup
def DetIdx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (k : ℕ) (N : Matrix (Fin k) (Fin k) K) (Q D : AddSubgroup (Fin k → K)),
    (oLat K k).toAddSubgroup ≤ Q → (oLat K k).toAddSubgroup.relIndex Q ≠ 0 →
    D ≤ (oLat K k).toAddSubgroup → D.relIndex (oLat K k).toAddSubgroup ≠ 0 →
    (∀ r ∈ D, ∃ s ∈ Q, s ᵥ* N = r) →
    |((Algebra.norm ℚ N.det : ℚ) : ℝ)| ≤
      ((oLat K k).toAddSubgroup.relIndex Q : ℝ) * (D.relIndex (oLat K k).toAddSubgroup : ℝ)
def IndexOf : Prop := DualIdx → DetIdx → IndexIneq
end PI.UnitaryGroupMassFormula.LCG


