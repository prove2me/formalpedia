-- Prove2me | Definitions.Def_JailletLu_IsAdmissibleOrder
-- name    : JailletLu_IsAdmissibleOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:19:21.841113+00:00
-- url     : https://prove2.me/theorems/5edca8bf-f4f5-4086-b348-0171f5a21a84
-- title:
--   Admissible orders of the interested advertisers
-- statement:
--   For each impression type $i$, the list construction of §5.3 lists the advertisers interested in $i$ as $a_1,\dots,a_k$. An **admissible order** assigns to every type $i$ a list without repetitions that contains exactly the dummy $a_d$ (adjacent to every type) and every advertiser $a$ with $a\sim i$.
--
--   **Formalization Note** The paper does not fix the order; the theorems of the mission quantify over every admissible order.
-- source:
--   Jaillet and Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.3, p. 13

import Mathlib

namespace JailletLu

/-- **Admissible orders of the interested advertisers.**
Jaillet and Lu, *Online Stochastic Matching: New Algorithms with Better Bounds*, accepted
manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.3, p. 13: "Assume a_1, ..., a_k are the advertisers interested in i."

`IsAdmissibleOrder E ord` says that for every impression type `i`, the list `ord i` enumerates,
without repetition, exactly the advertisers interested in `i`: the dummy `none` (= `a_d`, which has
an edge to every type) and every `some a` with `(a, i) ∈ E`.

**Formalization Note.** The paper does not fix the order `a_1, …, a_k`; the theorems of the
mission hold for every admissible order (a reading of the paper). -/
def IsAdmissibleOrder {A I : Type*} (E : Set (A × I)) (ord : I → List (Option A)) : Prop :=
  ∀ i, (ord i).Nodup ∧ ∀ b : Option A, b ∈ ord i ↔ (b = none ∨ ∃ a, b = some a ∧ (a, i) ∈ E)

end JailletLu


