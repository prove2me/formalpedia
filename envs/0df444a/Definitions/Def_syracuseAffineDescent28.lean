-- Prove2me | Definitions.Def_syracuseAffineDescent28
-- name    : syracuseAffineDescent28
-- status  : Definition
-- author  : @yuzhou
-- created : 2026-11-20T12:13:30.080497+00:00
-- url     : https://prove2.me/theorems/5c986172-0b49-4009-8491-dca3ccde2353
-- title:
--   Uniform affine Syracuse descent checker modulo $2^{28}$
-- statement:
--   A bounded checker for descent on an entire residue class modulo $2^{28}$. It follows exact affine trajectories while the odd part is uniform across the class. The last step permits extra factors of two because a partial quotient already gives a sufficient upper bound.

import Definitions.Def_syracuseAffineDescent26

/-- Search for uniform descent, allowing extra powers of two on the last step. -/
def syracuseAffineSearch28 (r M a b : Nat) : Nat → Bool
  | 0 => decide (a < r ∧ b ≤ M)
  | fuel + 1 =>
    if a < r ∧ b ≤ M then true
    else
      let k := min (syracuseAffineGuess26 (3 * a + 1) 28)
        (syracuseAffineGuess26 (3 * b) 28)
      let d := 2 ^ k
      let c := (3 * a + 1) / d
      let e := (3 * b) / d
      if 3 * a + 1 = d * c ∧ 3 * b = d * e then
        if c < r ∧ e ≤ M then true
        else if c % 2 = 1 ∧ e % 2 = 0 then
          syracuseAffineSearch28 r M c e fuel
        else false
      else false

/-- Uniform affine descent certificate on a residue class modulo 2^28. -/
def syracuseAffineDescent28 (r : Nat) : Bool :=
  syracuseAffineSearch28 r 268435456 r 268435456 28


