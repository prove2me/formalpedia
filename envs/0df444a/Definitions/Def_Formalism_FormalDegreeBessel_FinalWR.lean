-- Prove2me | Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
-- name    : Formalism_FormalDegreeBessel_FinalWR
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T11:36:43.517837+00:00
-- url     : https://prove2.me/theorems/6e32a4bb-04e0-4fff-be62-bae0640f7ffc
-- title:
--   Final WR
-- statement:
--   Definitions and structural lemmas for Final WR, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FinalWR.lean

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRPres
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_AdjointFunctionalHolds
import Definitions.Def_Formalism_YangianSpanCharacter_StatementT
import Theorems.Thm_Formalism_QuantumDeterminants_linear_operators_holds
import Theorems.Thm_Formalism_QuantumDeterminants_preserved_operators_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.QuantumDeterminants
variable {m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
def opEnd (l : Fin m) (i : Fin 6) : Module.End ℂ (WSm m E) where
  toFun f := ⟨opL l i f, preserved_operators_holds m E l i f f.2⟩
  map_add' f g := Subtype.ext (linear_operators_holds m E l i f g 1 f.2 g.2).1
  map_smul' a f := Subtype.ext (linear_operators_holds m E l i f f a f.2 f.2).2
abbrev pEnd (l : Fin m) : Module.End ℂ (WSm m E) := opEnd l 0
abbrev cEnd (l : Fin m) : Module.End ℂ (WSm m E) := opEnd l 1
abbrev ciEnd (l : Fin m) : Module.End ℂ (WSm m E) := opEnd l 2
abbrev pbEnd (l : Fin m) : Module.End ℂ (WSm m E) := opEnd l 3
abbrev cbEnd (l : Fin m) : Module.End ℂ (WSm m E) := opEnd l 4
abbrev cbiEnd (l : Fin m) : Module.End ℂ (WSm m E) := opEnd l 5
end Formalism.QuantumDeterminants


