-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_IsPositiveDefiniteMatrixCoefficientOfMemAlgA
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_IsPositiveDefiniteMatrixCoefficientOfMemAlgA
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T11:04:38.327951+00:00
-- url     : https://prove2.me/theorems/e767c0a4-e73f-4d21-8e55-d3fac7f679d5
-- title:
--   Is Positive Definite Matrix Coefficient Of Mem Alg A
-- statement:
--   Definitions and structural lemmas for Is Positive Definite Matrix Coefficient Of Mem Alg A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGroupIntegrability/IsPositiveDefiniteMatrixCoefficientOfMemAlgA.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeylForU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_InstCompactUG
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_IsPD_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_IsPD_const
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_IsPD_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_Sep_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_Sep_const
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_Sep_mul
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
namespace PI.UnitaryGroupMassFormula.PolyCoef
open MeasureTheory PI.UpqRep
open scoped InnerProductSpace
lemma Jm_allPos (N : ℕ) : Jm (allPos N) = 1 := by
  simp [Jm, allPos]
lemma mem_Kset_iff {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) :
    g ∈ Kset (allPos N) ↔ g ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  simp [Kset, Jm_allPos]
lemma memK {N : ℕ} (g : UG N) : (g : Matrix (Fin N) (Fin N) ℂ) ∈ Kset (allPos N) :=
  (mem_Kset_iff _).mpr g.2
abbrev muU (N : ℕ) : Measure (UG N) := Measure.haar
section
variable {N : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)} {S : Submodule ℂ H}
def orb (hst : IsKStableOn (allPos N) σ S) (u : S) : UG N → S :=
  fun x => ⟨σ x u, hst _ (memK x) _ u.2⟩
def T (hst : IsKStableOn (allPos N) σ S) (f : C(UG N, ℂ)) (u : S) : S :=
  ∫ x, f x • orb hst u x ∂(muU N)
variable (σ S) in

def Ugood : Submodule ℂ S where
  carrier := {u | ∀ w : H, IsPD (fun h : UG N => ⟪w, σ h (u : H)⟫_ℂ)}
  add_mem' := by
    intro u v hu hv w
    simpa [map_add, inner_add_right] using (hu w).add (hv w)
  zero_mem' := by
    intro w
    simpa using IsPD.const (N := N) 0
  smul_mem' := by
    intro c u hu w
    simpa [map_smul, inner_smul_right] using (IsPD.const c).mul (hu w)
end
end PI.UnitaryGroupMassFormula.PolyCoef


