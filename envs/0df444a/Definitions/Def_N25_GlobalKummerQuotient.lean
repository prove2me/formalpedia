-- Prove2me | Definitions.Def_N25_GlobalKummerQuotient
-- name    : N25_GlobalKummerQuotient
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:05.305257+00:00
-- url     : https://prove2.me/theorems/799e1d4d-5fc9-4d28-90b6-94b7e1326f08
-- title:
--   Projection of division cocycles to the cyclotomic quotient
-- statement:
--   Defines the cocycle obtained by composing a division-point cocycle in $V$ with the quotient $V↠F_{71}(1)$ supplied by the fixed $K_2$ filtration. It is the multiplicative-line Kummer class used in the global descent.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_GlobalKummerSequence
set_option autoImplicit false
noncomputable section
namespace N25.GlobalKummer
local instance instL_N25_GlobalKummerQuotient_23397f : Fact (Nat.Prime 71) := ⟨by decide⟩

/-- The actual division-point cocycle followed by the literal K2 quotient. -/
def quotientDivisionCocycle (hPhi : PhiFiveZero) (K2 : K2Rows)
    (P : ↥M) (Q : J) (hQ : piEnd Q = (P : J)) :
    groupCohomology.cocycles₁ cyclotomicRep :=
  groupCohomology.mapCocycles₁ (MonoidHom.id Gal) (kernelQuotient hPhi K2)
    (divisionCocycle hPhi P Q hQ)
end N25.GlobalKummer


