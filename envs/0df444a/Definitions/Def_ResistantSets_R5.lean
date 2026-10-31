-- Prove2me | Definitions.Def_ResistantSets_R5
-- name    : ResistantSets_R5
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:27:08.69267+00:00
-- url     : https://prove2.me/theorems/0f429fc1-ec34-4371-858d-e49fd588ebe0
-- title:
--   The sporadic set $R_5=R\ast\{0\}$
-- statement:
--   Let
--   $$
--   R=\Big\{\textstyle\sum_{i=1}^d e_i,\ \mathbf 1^4-\sum_{i=1}^d e_i : d\in[4]\Big\}=\{1000,1100,1110,1111,0111,0011,0001,0000\}\subseteq\{0,1\}^4 .
--   $$
--   The sporadic set is
--   $$
--   R_5=R\ast\{0\}=(R\times\{0\})\cup(\overline R\times\{1\})\subseteq\{0,1\}^5 .
--   $$
--
--   $R_5$ is the single exceptional set of the classification theorem.
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, p.6, §1.2 (R and R₅)

import Mathlib
import Definitions.Def_ResistantSets_reflProd

namespace ResistantSets

/-- The set `R = {Σ_{i=1}^d eᵢ, 1⁴ − Σ_{i=1}^d eᵢ : d ∈ [4]} ⊆ {0,1}⁴` (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), §1.2, p.6), i.e.
`{1000, 1100, 1110, 1111, 0111, 0011, 0001, 0000}`. `Σ_{i=1}^d eᵢ` is the point whose first
`d` coordinates are `1` (indices `i < d`). -/
def Rfour : Finset (Fin 4 → Bool) :=
  Finset.univ.filter fun x => ∃ d : Fin 5, 1 ≤ d.val ∧
    (x = (fun i => decide (i.val < d.val)) ∨ x = (fun i => !decide (i.val < d.val)))

/-- **The sporadic set `R₅`** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), §1.2, p.6): `R₅ := R ∗ {0} ⊆ {0,1}⁵`, the reflective
product of `R` (`Rfour`) with `{0} ⊆ {0,1}¹`, that is `(R × {0}) ∪ (R̄ × {1})`. -/
def R5 : Finset (Fin 5 → Bool) :=
  reflProd (n₁ := 4) (n₂ := 1) Rfour ({fun _ => false} : Finset (Fin 1 → Bool))

end ResistantSets


