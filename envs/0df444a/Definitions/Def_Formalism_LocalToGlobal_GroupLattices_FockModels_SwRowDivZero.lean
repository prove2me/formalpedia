-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowDivZero
-- name    : Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowDivZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:55:36.723342+00:00
-- url     : https://prove2.me/theorems/dda4dbd5-7e87-4607-bf1d-7f8d846b3055
-- title:
--   Sw Row Div Zero
-- statement:
--   Definitions and structural lemmas for Sw Row Div Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/SwRowDivZero.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.L2.G.Model
open Formalism.GradedWeylDivisibility
variable (R : Type) [CommRing R] {r n : ℕ}
def Dop (a b : Fin r) :
    Derivation R (MvPolynomial (Fin r × Fin n) R) (MvPolynomial (Fin r × Fin n) R) :=
  mkDerivation R fun v => if v.1 = b then X (a, v.2) else 0
def DL (a b : Fin r) : Module.End R (MvPolynomial (Fin r × Fin n) R) := (Dop R a b).toLinearMap
end Formalism.L2.G.Model


