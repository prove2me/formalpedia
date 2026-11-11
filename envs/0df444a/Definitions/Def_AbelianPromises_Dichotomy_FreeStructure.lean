-- Prove2me | Definitions.Def_AbelianPromises_Dichotomy_FreeStructure
-- name    : AbelianPromises_Dichotomy_FreeStructure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:11:25.423821+00:00
-- url     : https://prove2.me/theorems/3d8090e5-a356-4beb-b8f6-d45cdbd91d9b
-- title:
--   The Boolean 1-in-3 free structure
-- statement:
--   The published Boolean 1-in-3 relation has tuples (1,0,0), (0,1,0), and (0,0,1). Its three tuples are enumerated by the position of their unique 1. The general published freeStructure is specialized to this relation, listing Boolean 1 before 0 as the variable enumeration. Thus its binary operations satisfy the exact source identities
--   $$
--   f_1(x,y)=g(x,y,y),\quad f_2(x,y)=g(y,x,y),\quad f_3(x,y)=g(y,y,x)
--   $$
--   for a ternary g in the minion. This reuses the general free-structure definition instead of defining a second construction. Theorem 4.15 is obtained by specializing the existing Open correspondence theorem to this generator and target 1-in-3; it is not posed again.
-- source:
--   Tamio-Vesa Nakajima, Zephyr Verwimp, Stanislav Živný, Abelian embeddings make useful promises: approximation of detrivialised equations, STOC 2027 submission #967 (October 2026), printed p. 12 (PDF p. 13), Definition 4.14

import Mathlib
import Definitions.Def_AbelianPromises_Dichotomy_Algebra
import Definitions.Def_AlgebraicPCSP_OneInThree_Structures

set_option autoImplicit false

namespace AbelianPromises.Dichotomy

open PCSPBLPAff.Symmetric
open AlgebraicPCSP.Theory

/-- Use the published Boolean relation, with exactly one coordinate equal to 1. -/
abbrev oneInThree := AlgebraicPCSP.OneInThree.oneInThree

/-- Enumerate its three tuples by the position of their unique 1. -/
def oneInThreeEnumeration : Fin 3 ≃ oneInThree.rel () where
  toFun j := ⟨if j = 0 then ![1,0,0] else if j = 1 then ![0,1,0] else ![0,0,1], by
    fin_cases j <;> simp [oneInThree, AlgebraicPCSP.OneInThree.oneInThree,
      AlgebraicPCSP.OneInThree.ternaryStruct]⟩
  invFun t := if t.val 0 = 1 then 0 else if t.val 1 = 1 then 1 else 2
  left_inv j := by fin_cases j <;> decide
  right_inv t := by
    apply Subtype.ext
    rcases t.property with h | h | h <;> simp [h]

/-- The existing general free structure specialized to the source's generator 1-in-3.
The enumeration lists Boolean 1 before 0, so the minors are g(x,y,y), g(y,x,y),
and g(y,y,x), exactly as in Definition 4.14. -/
def freeOneInThree {A B : Type} (M : Minion A B) :
    Relation {f // f ∈ M.mem 2} :=
  freeStructure M oneInThree (Equiv.swap (0 : Fin 2) 1)
    (fun _ => 3) (fun _ => oneInThreeEnumeration)

end AbelianPromises.Dichotomy


