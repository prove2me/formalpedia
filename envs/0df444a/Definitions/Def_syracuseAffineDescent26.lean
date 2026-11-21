-- Prove2me | Definitions.Def_syracuseAffineDescent26
-- name    : syracuseAffineDescent26
-- status  : Definition
-- author  : @yuzhou
-- created : 2026-11-20T12:08:46.337685+00:00
-- url     : https://prove2.me/theorems/61f60144-35fd-4c8e-9f8c-8277af67add1
-- title:
--   Uniform affine Syracuse descent checker modulo $2^{26}$
-- statement:
--   A bounded checker for descent on an entire residue class modulo $2^{26}$. It follows exact affine trajectories while the odd part is uniform across the class. It succeeds when the final intercept is smaller and the coefficient is no larger.

/-- Bounded extraction of the trailing factors of two in the constant term. -/
def syracuseAffineGuess26 (a : Nat) : Nat → Nat
  | 0 => 0
  | fuel + 1 =>
    if a % 2 = 0 then 1 + syracuseAffineGuess26 (a / 2) fuel else 0

/-- Check for strict descent from the affine family with intercept r and modulus M.
Each exact transition preserves an odd output for every parameter. -/
def syracuseAffineSearch26 (r M a b : Nat) : Nat → Bool
  | 0 => decide (a < r ∧ b ≤ M)
  | fuel + 1 =>
    if a < r ∧ b ≤ M then true
    else
      let k := syracuseAffineGuess26 (3 * a + 1) 26
      let d := 2 ^ k
      let c := (3 * a + 1) / d
      let e := (3 * b) / d
      if 3 * a + 1 = d * c ∧ 3 * b = d * e ∧ c % 2 = 1 ∧ e % 2 = 0 then
        syracuseAffineSearch26 r M c e fuel
      else false

/-- Uniform affine descent certificate on a residue class modulo 2^26. -/
def syracuseAffineDescent26 (r : Nat) : Bool :=
  syracuseAffineSearch26 r 67108864 r 67108864 26


