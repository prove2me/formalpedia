-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_UnitaryOfBlockWMem
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_UnitaryOfBlockWMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:36:22.634098+00:00
-- url     : https://prove2.me/theorems/6a5e07a5-eba7-4645-9a7c-852bf0294014
-- title:
--   Unitary Of Block WMem
-- statement:
--   Definitions and structural lemmas for Unitary Of Block WMem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace PI.HwUniqW
open PI.UpqRep
variable {k r : ℕ}
def InB (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val < r + k
instance instDecInB (i : Fin (2 * r + k + 1)) : Decidable (InB k r i) := by unfold InB; infer_instance
def bl (k r : ℕ) (a : Fin k) : Fin (2 * r + k + 1) := ⟨r + a.val, by omega⟩
def sub (k r : ℕ) (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Matrix (Fin k) (Fin k) ℂ :=
  fun a b => m (bl k r a) (bl k r b)
def FixEW (k r : ℕ) (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  (∀ a : Fin r, m *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ m *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧
    m *ᵥ bvec (wI k r (Fin.last k)) = bvec (wI k r (Fin.last k))
end PI.HwUniqW
end


