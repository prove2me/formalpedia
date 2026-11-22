-- Prove2me | Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableOf
-- name    : Formalism_GaloisIrreducibility_NoSolvableOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:07:41.099791+00:00
-- url     : https://prove2.me/theorems/1b9268c2-483b-42ab-b187-815abf77632f
-- title:
--   No Solvable Of
-- statement:
--   Definitions and structural lemmas for No Solvable Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/NoSolvableOf.lean

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GaloisIrreducibility
def LemmaAOf : Prop := OrbitSubSum → RestrictRoots → LemmaA
def IrredOf : Prop := LemmaA → Irred
def ShareNOf : Prop := ShareBound → ShareN
def NoSolvableOf : Prop :=
  PowerPCycle → PrimitiveOfPCycle → JordanPrime → AltNotSolvable → NoSolvableTransitive
def BBOf : Prop := FewLargeParts → BBAtMostThree
end Formalism.GaloisIrreducibility


