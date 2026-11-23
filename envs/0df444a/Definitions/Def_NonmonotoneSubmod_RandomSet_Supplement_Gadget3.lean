-- Prove2me | Definitions.Def_NonmonotoneSubmod_RandomSet_Supplement_Gadget3
-- name    : NonmonotoneSubmod_RandomSet_Supplement_Gadget3
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:14:25.749223+00:00
-- url     : https://prove2.me/theorems/e97e61d0-45f2-4bc0-ba14-ba1adc57aaeb
-- title:
--   Theorem 4.3 proof — the six-element parity gadget
-- statement:
--   There are three true/false pairs, one for the $X$ position and two ordered $Y$ positions. An $X$ singleton has value $1$, and a $Y$ singleton has value $1/2$. Sets smaller than three have the sum of their singleton values, except the pair containing both $X$ labels has value $1$. Sets larger than three have the value of their complement. For sets of size three,
--   $$g_b(S)=\begin{cases}2&\text{valid and satisfying parity }b,\\1&\text{valid and failing parity }b,\\2&\text{invalid with exactly one }X\text{ label},\\3/2&\text{invalid with both or neither }X\text{ label}.\end{cases}$$
--
--   This specifies all 64 entries for either right-hand bit. It is the local proof object in the reduction for Theorem 4.3, not a replacement for that theorem. The definition makes no assumption that the unproved gadget properties hold.
--
--   **Formalization Note** Position zero is the $X$ variable; positions one and two are the ordered $Y$ variables. Complement is taken in the six-element local ground set; all values are exact rationals.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4):1133–1153, 2011, DOI 10.1137/090779346; p. 1147, proof of Theorem 4.3, eight bullet points

import Mathlib
import Definitions.Def_NonmonotoneSubmod_RandomSet_Supplement_Gadget4
open Classical

namespace NonmonotoneSubmod.RandomSet.Supplement

/-- Values on sets of size less than three, including the weak X pair. -/
def gadget3Small (S : Finset (Fin 3 × Bool)) : ℚ :=
  if S = {(0, false), (0, true)} then 1
  else ∑ i ∈ S, if i.1 = 0 then (1 : ℚ) else 1 / 2

/-- Complete six-element table in the proof of Theorem 4.3, p.1147.
Position 0 is in X; positions 1 and 2 are the ordered Y variables. -/
noncomputable def gadget3 (rhs : Bool) (S : Finset (Fin 3 × Bool)) : ℚ :=
  if S.card < 3 then gadget3Small S
  else if 3 < S.card then gadget3Small Sᶜ
  else if ValidSelection S then
    if selectionParity S = rhs then 2 else 1
  else if (S.filter (fun i => i.1 = 0)).card = 1 then 2
  else 3 / 2


end NonmonotoneSubmod.RandomSet.Supplement


