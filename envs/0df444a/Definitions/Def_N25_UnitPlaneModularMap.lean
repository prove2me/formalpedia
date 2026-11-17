-- Prove2me | Definitions.Def_N25_UnitPlaneModularMap
-- name    : N25_UnitPlaneModularMap
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:22:25.252594+00:00
-- url     : https://prove2.me/theorems/8aba77d5-05fa-431f-b908-e90a9347a603
-- title:
--   Modular-unit inputs for the unit-plane map
-- statement:
--   This is an import-only interface collecting the unit-plane function-field evaluation machinery together with the selected level-$25$ modular units, their algebraic relation, and the required transcendence input. It introduces no new mathematical object; its role is to provide a stable assembly point for the modular map from the plane model.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitPlaneFieldPointLift
import Definitions.Def_N25_Endgame
/-! The existing plane-field evaluation and the specified modular-unit inputs. -/


