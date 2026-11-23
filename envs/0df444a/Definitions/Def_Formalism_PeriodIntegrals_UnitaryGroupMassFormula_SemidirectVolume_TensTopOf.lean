-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_TensTopOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_TensTopOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:09:20.871471+00:00
-- url     : https://prove2.me/theorems/a4f16cc8-e4b6-4040-9b87-71602e423989
-- title:
--   Tens Top Of
-- statement:
--   Definitions and structural lemmas for Tens Top Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/TensTopOf.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolSemiDirect
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolSemiDirect.W.Lc
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct
def AFTop : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    LocallyCompactSpace (AF F) ∧ SecondCountableTopology (AF F) ∧ T2Space (AF F)
def sigL {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) : R ⊗[F] E →ₗ[R] R ⊗[F] E where
  toFun := sigR R σ
  map_add' := fun x y => map_add _ x y
  map_smul' := by
    intro r x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [sigR, TensorProduct.smul_tmul']
    | add x y hx hy => simp_all [smul_add]
end PI.VolSemiDirect.W.Lc


