-- Prove2me | Definitions.Def_N25_FiniteBaseFunctionFields
-- name    : N25_FiniteBaseFunctionFields
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:10:51.782123+00:00
-- url     : https://prove2.me/theorems/19e626fb-da45-42d4-bc66-eb0d91af2663
-- title:
--   Level-$25$ modular function fields in characteristics $2$ and $3$
-- statement:
--   Introduces abbreviations for the level-$25$ modular function fields over the prime fields $𝔽_2$ and $𝔽_3$. They are the finite-characteristic carriers used for the good reductions at $2$ and $3$ and for the ensuing place-count computations.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_Endgame
/-! The base modular function fields of level 25 over the prime fields of characteristic two and three. -/
noncomputable section
namespace N25.Endgame

/-- The level-25 modular function field over `ZMod 2`. -/
abbrev F₂25 := FBase (ZMod 2)
/-- The level-25 modular function field over `ZMod 3`. -/
abbrev F₃25 := FBase (ZMod 3)

end N25.Endgame


