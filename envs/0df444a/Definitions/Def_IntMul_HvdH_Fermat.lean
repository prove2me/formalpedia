-- Prove2me | Definitions.Def_IntMul_HvdH_Fermat
-- name    : IntMul_HvdH_Fermat
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-12T04:09:39.1243+00:00
-- url     : https://prove2.me/theorems/c4d070e9-9192-41de-94f4-762848f7a8b0
-- title:
--   Negacyclic multiplication via one product modulo 2^{nP}+1

import Definitions.Def_IntMul_HvdH_KronMul

/-! Negacyclic multiplication through one multiplication modulo a Fermat-type number
`F = 2^{nP} + 1`: evaluate at `y = 2^P` (so `y^n ≡ -1`), multiply modulo `F`, take the balanced
residue and read `n` balanced base-`2^P` digits. -/

namespace IntMul.HvdH

/-- The residue of `x` modulo `F` in `(-F/2, F/2]`. -/
def balMod (F x : ℤ) : ℤ :=
  let c := x % F
  if F < 2 * c then c - F else c

/-- Negacyclic product of two length-`n` coefficient lists via one product modulo `2^{nP} + 1`.
The middle step `(A * B) % F` with `0 ≤ A, B < F` is the Fermat-ring multiplication. -/
def fermatNegaMul (P n : ℕ) (u v : List ℤ) : List ℤ :=
  let B : ℤ := 2 ^ P
  let F : ℤ := B ^ n + 1
  kunpack B n (balMod F ((kpack B u % F) * (kpack B v % F) % F))

end IntMul.HvdH


