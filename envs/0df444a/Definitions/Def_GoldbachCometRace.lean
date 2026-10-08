-- Prove2me | Definitions.Def_GoldbachCometRace
-- name    : GoldbachCometRace
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-05T09:04:32.903782+00:00
-- url     : https://prove2.me/theorems/bfca25cf-20c2-4ff0-a00a-28d1d16f4a7b
-- title:
--   Prime race counts and delta_q at scale n
-- statement:
--   Defines `analysisScale`, `primeCountTo`, `primeCountInClass`, and `delta_q` with scale `x = n` per docs/goldbach-comet/CONVENTIONS.md.
-- source:
--   docs/goldbach-comet/LAYER3-NEXT.md

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Rat.Defs

import Definitions.Def_GoldbachComet
import Definitions.Def_GoldbachCometImprint

set_option autoImplicit false

namespace GoldbachCometImprint

open GoldbachComet

/-- Scale parameter for π(x) and class counts: **`x = n`** (see `CONVENTIONS.md`). -/
def analysisScale (n : ℕ) : ℕ := n

/-- Primes `p` with `p ≤ x`. -/
def primesUpTo (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter Nat.Prime

/-- Prime counting function `π(x)`. -/
def primeCountTo (x : ℕ) : ℕ :=
  (primesUpTo x).card

/-- Primes `p ≤ x` with `p ≡ a (mod q)`. -/
def primeCountInClass (q a x : ℕ) : ℕ :=
  ((primesUpTo x).filter fun p => p % q = a).card

/-- Class excess over the uniform benchmark `π(x)/(q-1)` (requires `1 < q` in applications). -/
def delta_q (q a x : ℕ) : ℚ :=
  (primeCountInClass q a x : ℚ) - (primeCountTo x : ℚ) / (q - 1)

theorem primeCountInClass_le_primeCountTo {q a x : ℕ} :
    primeCountInClass q a x ≤ primeCountTo x := by
  unfold primeCountInClass primeCountTo primesUpTo
  refine Finset.card_le_card ?_
  intro p hp
  simp [Finset.mem_filter] at hp ⊢
  exact hp.1

theorem delta_q_at_scale (q a n : ℕ) : delta_q q a (analysisScale n) =
    (primeCountInClass q a n : ℚ) - (primeCountTo n : ℚ) / (q - 1) := by
  rfl

end GoldbachCometImprint


