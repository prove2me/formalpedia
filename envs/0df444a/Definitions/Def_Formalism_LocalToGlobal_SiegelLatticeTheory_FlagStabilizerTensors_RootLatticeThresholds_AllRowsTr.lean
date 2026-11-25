-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_AllRowsTr
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_AllRowsTr
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:45:27.525381+00:00
-- url     : https://prove2.me/theorems/c532ca81-27ea-44b9-8042-4db0fbd9abc1
-- title:
--   All Rows Tr
-- statement:
--   Definitions and structural lemmas for All Rows Tr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/AllRowsTr.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_AllRowsGA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MonoidAlgebra
namespace Formalism.L2.SG.Pf.AllRowsTr
open Formalism.L2.SG.Pf.AllRowsGA
section One
variable {G : Type} [Group G] [Fintype G]
end One
section Prod
variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
def pA (f : ∀ i, MonoidAlgebra ℂ (G i)) : MonoidAlgebra ℂ (∀ i, G i) :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun γ => ∏ i, (f i).coeff (γ i))
end Prod
end Formalism.L2.SG.Pf.AllRowsTr


