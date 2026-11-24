-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RedBasicsPf
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RedBasicsPf
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T18:08:43.935938+00:00
-- url     : https://prove2.me/theorems/1c97007b-4947-4511-a725-c9f8aef94c0d
-- title:
--   Red Basics Pf
-- statement:
--   Definitions and structural lemmas for Red Basics Pf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/RedBasicsPf.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix Pointwise
namespace Formalism.L2.SG.Pf.RedBasicsPf
open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin
attribute [local instance] Ideal.Quotient.field
variable (I : AutInst) (w : HeightOneSpectrum (𝓞 I.E))
abbrev RedQ : Type := I.L ⧸ (w.asIdeal • (⊤ : Submodule (𝓞 I.E) I.L))
instance finite_Q : Module.Finite (𝓞 I.E ⧸ w.asIdeal) (RedQ I w) := by
  have : Module.Finite (𝓞 I.E) I.L := Module.Finite.iff_fg.2 I.L_fg
  exact Module.Finite.of_restrictScalars_finite (𝓞 I.E) _ _
end Formalism.L2.SG.Pf.RedBasicsPf


