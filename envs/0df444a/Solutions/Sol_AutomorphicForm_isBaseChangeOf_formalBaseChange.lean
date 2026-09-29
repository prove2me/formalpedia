-- Prove2me | solution 1 for AutomorphicForm.isBaseChangeOf_formalBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/974e149c-0ab2-5f63-be1d-e80c5ec0a9ed

import Mathlib
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isBaseChangeOf_formalBaseChange

open IsDedekindDomain NumberField AutomorphicForm

theorem solution
    (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K)]
    [Algebra.IsIntegral (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K)]
    {R : Type*} [CommRing R] (π : AutomorphicForm.HeckeEigensystem F R) :
    AutomorphicForm.IsBaseChangeOf π (AutomorphicForm.formalBaseChange F K π) :=
  ⟨∅, fun _ _ => ⟨rfl, rfl⟩⟩

end S_AutomorphicForm_isBaseChangeOf_formalBaseChange
end P2MW
export P2MW.S_AutomorphicForm_isBaseChangeOf_formalBaseChange (solution)
