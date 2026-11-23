-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExistsUnifFv
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExistsUnifFv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:11:32.37247+00:00
-- url     : https://prove2.me/theorems/36dad6d0-53d0-4f66-af83-f75c7543dc01
-- title:
--   Exists Unif Fv
-- statement:
--   Definitions and structural lemmas for Exists Unif Fv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/ExistsUnifFv.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_EventuallySmulSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVDxSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfCo
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensFibV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology Filter
open scoped TensorProduct
section HermMod
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
theorem sigR_algebraMap (σ : E →ₐ[F] E) (t : R) :
    sigR R σ (algebraMap R (R ⊗[F] E) t) = algebraMap R (R ⊗[F] E) t := by
  show (Algebra.TensorProduct.map (AlgHom.id F R) σ) (algebraMap R (R ⊗[F] E) t) =
    algebraMap R (R ⊗[F] E) t
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    map_one]
instance hermSMul (σ : E →ₐ[F] E) (n : ℕ) : SMul R (HermR R σ n) :=
  ⟨fun t S => ⟨t • (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)), by
    intro a b
    have h := S.2 a b
    simp only [Matrix.smul_apply, Algebra.smul_def, map_mul, sigR_algebraMap]
    rw [h]⟩⟩
instance hermModule (σ : E →ₐ[F] E) (n : ℕ) : Module R (HermR R σ n) :=
  Function.Injective.module R (HermR R σ n).subtype Subtype.coe_injective (fun _ _ => rfl)
end HermMod
end PI.VolStabSW


