-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictGen
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictGen
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T13:13:22.359212+00:00
-- url     : https://prove2.me/theorems/6e1cd859-4181-4a03-964b-ea71fa61607b
-- title:
--   Dict Gen
-- statement:
--   Definitions and structural lemmas for Dict Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictGen.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
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
namespace PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
namespace DictGen
variable (I : AutInst)
def lamM (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Submodule (𝓞 I.E) (Fin I.n → I.E) where
  carrier := {v | M *ᵥ iv I v ∈ I.Lf}
  add_mem' := fun {v w} hv hw => by
    have e : iv I (v + w) = iv I v + iv I w := by
      funext i; simp [iv]
    show M *ᵥ iv I (v + w) ∈ I.Lf
    rw [e, Matrix.mulVec_add]
    exact I.Lf.add_mem hv hw
  zero_mem' := by
    have e : iv I (0 : Fin I.n → I.E) = 0 := by
      funext i; simp [iv]
    show M *ᵥ iv I 0 ∈ I.Lf
    rw [e, Matrix.mulVec_zero]
    exact I.Lf.zero_mem
  smul_mem' := fun a v hv => by
    have ha : Formalism.UG.inclE (F := I.F) (Af I.F) ((a : 𝓞 I.E) : I.E) ∈ IntAf I.F I.E :=
      Subring.subset_closure (Or.inl ⟨⟨(a : I.E), a, rfl⟩, rfl⟩)
    have e : iv I (a • v) = Formalism.UG.inclE (F := I.F) (Af I.F) ((a : 𝓞 I.E) : I.E) • iv I v := by
      funext i
      simp [iv, Algebra.smul_def]
    show M *ᵥ iv I (a • v) ∈ I.Lf
    rw [e, Matrix.mulVec_smul]
    exact I.Lf.smul_mem ⟨_, ha⟩ hv
end DictGen
end PIW.AdelClassFin


