-- Prove2me | Definitions.Def_N25_LocalFiveCondition
-- name    : N25_LocalFiveCondition
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:38.399831+00:00
-- url     : https://prove2.me/theorems/20d46c83-4923-4ecd-a256-512866c922a1
-- title:
--   Local $71$-divisibility condition at $5$
-- statement:
--   Defines the proposition that the local fixed-point group $M_5$ has a finite-index subgroup on which multiplication by $71$ is surjective. This is the precise local condition used to remove the prime-$5$ obstruction in the Kummer descent.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_LocalCarrier
import Definitions.Def_N25_LocalFiveArithmetic
namespace N25
/-- Finite-index multiplication-by-71 surjectivity on the literal local carrier. -/
def N5Surj : Prop := LocalFive.FiniteQuotientSurj ↥M5 71
end N25


