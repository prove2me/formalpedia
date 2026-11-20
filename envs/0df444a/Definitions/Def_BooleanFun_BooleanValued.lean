-- Prove2me | Definitions.Def_BooleanFun_BooleanValued
-- name    : BooleanFun_BooleanValued
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T19:04:15.128915+00:00
-- url     : https://prove2.me/theorems/ab87df8d-6ef3-404d-bdc3-09f1aa552ea2
-- title:
--   Boolean Valued
-- statement:
--   Definitions and structural lemmas for Boolean Valued, from Joris Roos and contributors's pinned Boolean functions and Arrow’s theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean

import Definitions.Def_BooleanFun_Basic
set_option autoImplicit false
noncomputable section
namespace BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
structure BooleanValued (f : BooleanFunc n) : Prop where
  one_or_neg_one : ∀ x, f x = 1 ∨ f x = -1
namespace BV
section DegreeOne
end DegreeOne
section Distance
abbrev distance (f g : BooleanFunc n) : ℝ :=
  𝐄 (fun x ↦ oneOn (f x ≠ g x))
end Distance
section BLR
abbrev acceptanceProbabilityBLR (f : BooleanFunc n) : ℝ :=
  𝐄 <| fun x ↦ 𝐄 <| fun y ↦ oneOn <| (f x) * (f y) = f (x + y)
end BLR
end BV
end BooleanFun


