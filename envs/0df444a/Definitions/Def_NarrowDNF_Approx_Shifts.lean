-- Prove2me | Definitions.Def_NarrowDNF_Approx_Shifts
-- name    : NarrowDNF_Approx_Shifts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:26.666744+00:00
-- url     : https://prove2.me/theorems/0f61f084-e5c2-42b5-aaf6-7ebd76d4ed05
-- title:
--   Slice shifts and ordered finite shift sequences
-- statement:
--   For a coordinate $i$, write $v_0,v_1$ for the two slices of a Boolean function $v$. The upper and lower shifts are
--   $$(U_iv)_0=v_0,\quad(U_iv)_1=v_0\lor v_1,\qquad
--   (L_iv)_0=v_0\land v_1,\quad(L_iv)_1=v_1.$$
--   Coordinate monotonicity means $v(x^{i\leftarrow0})\le v(x^{i\leftarrow1})$ for every $x$. An ordered finite list of coordinate/choice pairs applies these transformations from left to right, with false denoting upper and true denoting lower. Its lower-coordinate set is the union of all coordinates with a lower choice, allowing repetitions and the empty list.
--
--   The list preserves the order of operations. No commutativity or random-choice property is assumed in the deterministic sequence interface; probabilities appear explicitly in the theorems.
-- source:
--   Chenghua Liu, Boning Meng, STOC 2027 submission #1509 (October 2026), Section 3, pp. 5–7 (PDF pp. 6–8), before Lemmas 3.1 and 3.2

import Definitions.Def_NarrowDNF_Approx_Activation

namespace NarrowDNF.Approx

/-- Slice-defined upper shift: v₀ stays fixed and v₁ becomes v₀ ∨ v₁. -/
def upper {n : ℕ} (i : Fin n) (v : Cube n → Bool) (x : Cube n) : Bool :=
  if x i then v (Function.update x i false) || v (Function.update x i true)
  else v (Function.update x i false)

/-- Slice-defined lower shift: v₀ becomes v₀ ∧ v₁ and v₁ stays fixed. -/
def lower {n : ℕ} (i : Fin n) (v : Cube n → Bool) (x : Cube n) : Bool :=
  if x i then v (Function.update x i true)
  else v (Function.update x i false) && v (Function.update x i true)

def CoordinateMonotone {n : ℕ} (v : Cube n → Bool) (i : Fin n) : Prop :=
  ∀ x, v (Function.update x i false) ≤ v (Function.update x i true)

/-- Ordered finite sequence: false denotes an upper shift, true a lower shift. -/
def applyShifts {n : ℕ} (s : List (Fin n × Bool)) (v : Cube n → Bool) : Cube n → Bool :=
  s.foldl (fun u t => if t.2 then lower t.1 u else upper t.1 u) v

/-- Repeated occurrences contribute only once to the union of lower coordinates. -/
def lowerCoordinates {n : ℕ} (s : List (Fin n × Bool)) : Finset (Fin n) :=
  (s.filterMap (fun t => if t.2 then some t.1 else none)).toFinset

end NarrowDNF.Approx


