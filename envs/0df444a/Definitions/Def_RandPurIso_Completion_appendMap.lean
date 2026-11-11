-- Prove2me | Definitions.Def_RandPurIso_Completion_appendMap
-- name    : RandPurIso_Completion_appendMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:28:59.736296+00:00
-- url     : https://prove2.me/theorems/7d924fad-0845-43fe-b55e-e4f63fc7bdc2
-- title:
--   Append map $\mathrm{App}^{(t)}_{x,y}$
-- statement:
--   $\mathrm{App}^{(t)}_{x,y}|\vec x,\vec y\rangle=|(\vec x,x),(\vec y,y)\rangle$, a map $\mathcal R_t\to\mathcal R_{t+1}$ appending $x$ to the input word and $y$ to the output word.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, §3.4, p. 23

import Mathlib
import Definitions.Def_RandPurIso_Completion_PRSt
open Matrix

namespace RandPurIso.Completion

/-- **Append map** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, §3.4, p. 23): `App^{(t)}_{x,y} |x⃗, y⃗⟩ = |(x⃗, x), (y⃗, y)⟩`, a map
`R_t → R_{t+1}`. -/
def appendMap (N t : ℕ) (x y : Fin N) : Matrix (Rt N (t + 1)) (Rt N t) ℂ :=
  fun r' r => if r'.1 = Fin.snoc (α := fun _ => Fin N) r.1 x ∧
      r'.2 = Fin.snoc (α := fun _ => Fin N) r.2 y then 1 else 0

end RandPurIso.Completion


