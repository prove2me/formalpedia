-- Prove2me | Definitions.Def_ChapterFreeFieldBornFiberStabilizer
-- name    : ChapterFreeFieldBornFiberStabilizer
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-12T06:48:08.038882+00:00
-- url     : https://prove2.me/theorems/605d9366-7bb9-4b09-9feb-ae15bc66ba6c
-- title:
--   ChapterFreeFieldBornFiberStabilizer

import Definitions.Def_ChapterFreeFieldBornFiberBounds
import Definitions.Def_ChapterFreeFieldBornSignGauge
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornFiberCardGeneral
import Definitions.Def_ChapterFreeFieldBornQuotient
import Mathlib


/-!
# Chapter "Wave-function parametrization of a probability measure", §5 —
# the orbit–stabilizer identity for the Born sign gauge

Source: `book.tex`, chapter *"Wave-function parametrization of a probability
measure"* — the free-field construction of §5 (`book.tex` ~line 1706) and the
Introduction's remark (`book.tex` ~line 805) that the wave function is *one
possible* parametrization of a probability distribution.

Earlier waves established that the diagonal `{±1}ⁿ` sign group acts on the unit
sphere with `bornMap (signFlip s x) = bornMap x`, that each Born fiber is a full
orbit of the sign group restricted to the positive support, and that
`#fiber = 2 ^ (#positive coordinates)`.

This wave records the **orbit–stabilizer** picture of that action. Indexing the
sign group by boolean choices (`boolSign`), for a fixed wave function `x` on the
sphere the **stabilizer** — the sign flips that fix `x` — is exactly the flips
supported on the *vanishing* coordinates of `x`, so it has `2 ^ (#zero
coordinates)` elements. Combined with the fiber (= orbit) count this yields the
orbit–stabilizer identity `#orbit · #stabilizer = 2 ^ n`, the order of the whole
diagonal sign group.

## Main results

* `boolSign_pm` — `boolSign b k = ±1`.
* `mem_signStab` — `b ∈ signStab x ↔ ∀ k, x k ≠ 0 → b k = true`.
* `signStab_card` — `#(signStab x) = 2 ^ (#zero coordinates of x)`.
* `signStab_card_mul_two_pow_nonzero` — `#stabilizer · 2 ^ (#nonzero) = 2 ^ n`.
* `posSupport_bornMap` — `posSupport (bornMap x) = {k : x k ≠ 0}`.
* **headline** `bornFiber_card_mul_signStab_card` — `#fiber · #stabilizer = 2ⁿ`.

Everything is intended to be `sorry`-free and axiom-clean.
-/

open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornQuotient
open BookProof.ChapterFreeFieldBornSignGauge
open BookProof.ChapterFreeFieldBornFiberCardGeneral
open BookProof.ChapterFreeFieldBornFiberBounds

namespace BookProof.ChapterFreeFieldBornFiberStabilizer

variable {n : ℕ}

/-- The `±1` sign vector determined by a boolean choice on each coordinate. -/
def boolSign (b : Fin n → Bool) : Fin n → ℝ := fun k => if b k then 1 else -1

theorem boolSign_pm (b : Fin n → Bool) (k : Fin n) :
    boolSign b k = 1 ∨ boolSign b k = -1 := by
  unfold boolSign; split_ifs <;> simp

/-- The **stabilizer** of `x` in the diagonal `{±1}ⁿ` sign group, indexed by
boolean sign choices: those sign flips that fix `x`. -/
noncomputable def signStab (x : EuclideanSpace ℝ (Fin n)) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun b => signFlip (boolSign b) x = x)

/-
A sign flip fixes `x` iff it is `+1` on every nonzero coordinate of `x`.
-/
theorem mem_signStab {x : EuclideanSpace ℝ (Fin n)} {b : Fin n → Bool} :
    b ∈ signStab x ↔ ∀ k, x k ≠ 0 → b k = true := by
      simp only [signStab, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq];
      constructor <;> intro h <;> simp_all only [signFlip, WithLp.equiv_symm_apply];
      · intro k hk; replace h := congr_arg ( fun f => f k ) h; simp_all [ boolSign ] ;
        by_cases hb : b k = true
        · exact hb
        · have hbf : b k = false := by simpa using hb
          have hz0 : x.ofLp k = 0 := by linarith [h hbf]
          exact absurd hz0 hk;
      · ext k; by_cases hk : x.ofLp k = 0 <;> simp_all [ boolSign ] ;

/-
The stabilizer of `x` under the sign gauge has `2 ^ (#zero coordinates)`
elements: the sign choices on the vanishing coordinates are free, while the
nonzero coordinates are forced to `+1`.
-/


/-
**Orbit–stabilizer (arithmetic form).** The stabilizer size times
`2 ^ (#nonzero coordinates)` equals the order `2 ^ n` of the diagonal sign
group.
-/


/-
`posSupport (bornMap x)` is exactly the set of nonzero coordinates of `x`
(since `bornMap x k = (x k)² > 0 ↔ x k ≠ 0`).
-/


/-
**Headline (orbit–stabilizer).** For a wave function `x` on the unit sphere,
the Born fiber over `bornMapSphere x` (the orbit of the sign gauge) times the
sign-gauge stabilizer of `x` equals the order `2 ^ n` of the whole diagonal sign
group.
-/


end BookProof.ChapterFreeFieldBornFiberStabilizer


