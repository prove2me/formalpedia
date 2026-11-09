-- Prove2me | Definitions.Def_WatsonPseudodeterminism_MASeparation_Gadget
-- name    : WatsonPseudodeterminism_MASeparation_Gadget
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:23:50.569011+00:00
-- url     : https://prove2.me/theorems/94bbf6d4-2f2a-4c17-bad1-318477684f45
-- title:
--   The inner-product gadget and its coordinatewise lift
-- statement:
--   For a block length $h$, a block is a binary vector of length $h$. Define the inner-product gadget and its $m$-coordinate lift by
--
--   $$g(x,y)=\left(\sum_{j=1}^h x_jy_j\right)\bmod2,\qquad g^m(x,y)_i=g(x_i,y_i).$$
--
--   The gadget length at size $n$ is $h(n)=100\lceil\log_2n\rceil$, represented by `100 * Nat.clog 2 n`. This is the integral reading of the paper's $100\log n$. Coordinate indices are zero-based in Lean; all sums still cover the full block. At $h=0$ the inner product is zero. These definitions are shared by the separating function, balance statements, and the packing lemma.
-- source:
--   Thomas Watson, STOC 2027 submission #13 (October 2026), §2.2, p. 7 (S, g and g^m); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/13.pdf

import Mathlib

namespace WatsonPseudodeterminism.MASeparation

abbrev Block (h : ℕ) := Fin h → Bool
abbrev BlockInput (h m : ℕ) := Fin m → Block h

/-- §2.2, p. 7: integer block length, rounding log₂ n upward. -/
def gadgetLength (n : ℕ) : ℕ := 100 * Nat.clog 2 n

/-- The inner-product-mod-two gadget, including the empty inner product. -/
def gadget {h : ℕ} (x y : Block h) : Bool :=
  decide ((∑ i : Fin h, if x i && y i then 1 else 0 : ℕ) % 2 = 1)

/-- Coordinatewise lifting g^m. -/
def gadgetPower {h m : ℕ} (x y : BlockInput h m) : Fin m → Bool :=
  fun i => gadget (x i) (y i)

end WatsonPseudodeterminism.MASeparation


