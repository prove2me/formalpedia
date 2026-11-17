-- Prove2me | Definitions.Def_CosDensity_Supplement_WordStreamAlg
-- name    : CosDensity_Supplement_WordStreamAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:16:29.043466+00:00
-- url     : https://prove2.me/theorems/d33545b6-053d-4625-b50c-cc3afcdd9abd
-- title:
--   One-pass streaming algorithms measured in real words
-- statement:
--   A **real-word one-pass streaming algorithm** has a persistent random seed, a mutable state, an initialization map that may depend on the stream length, a transition map that may also depend on the zero-based stream position, and an optional real output. The optional output records the explicit `OVERFLOW` outcome of Algorithms 1 and 2.
--
--   The algorithm uses at most $w$ words when its full mutable state injects into $\mathbb R^w$. Thus every memory configuration can be represented by $w$ real scalars, while the random seed is public and is not charged as memory.
--
--   This is the word-space model used by the paper's upper bounds; it is deliberately separate from the finite-state bit model used by the lower bounds.
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), §3, p.12 (PDF p.13), and Theorems 4.1, 4.3, 5.2, 6.1, 7.3

import Definitions.Def_CosDensity_StreamAlg

open MeasureTheory

namespace CosDensity.Supplement

set_option autoImplicit false

/-!
# One-pass streaming algorithms measured in real words

Q. Zhang, *Frequency Moments Beyond Equality: Streaming Cosine Density Moments*,
arXiv:2609.06925 (held version, sha256 f4d4df22…), §3, p.12 (PDF p.13), and the
upper bounds in Theorems 4.1, 4.3, 5.2, 6.1 and 7.3.

**Formalization Note.** The paper counts one input coordinate or one intermediate real scalar as
one word. Accordingly, a state using `w` words is required to inject into `Fin w → ℝ`. This rules
out hiding extra information in an unaccounted state type while retaining the paper's ideal-real word
model. The random seed is persistent and free, as in the base mission's bit-space model. An output of
`none` represents the explicit `OVERFLOW` outcome of Algorithms 1 and 2.
-/

/-- A randomized one-pass algorithm whose complete mutable state is representable by `words` real
scalars. The transition may depend on the total length and the zero-based stream position. -/
structure WordStreamAlg (E : Type*) where
  Seed : Type
  seedMeasurable : MeasurableSpace Seed
  measure : @Measure Seed seedMeasurable
  isProbability : @IsProbabilityMeasure Seed seedMeasurable measure
  State : Type
  words : ℕ
  encode : State → (Fin words → ℝ)
  encode_injective : Function.Injective encode
  init : Seed → ℕ → State
  step : Seed → ℕ → ℕ → E → State → State
  out : Seed → ℕ → State → Option ℝ

namespace WordStreamAlg

variable {E : Type*}

/-- Process a suffix beginning at zero-based position `t`. -/
def runFrom (A : WordStreamAlg E) (omega : A.Seed) (n : ℕ) : ℕ → List E → A.State → A.State
  | _, [], s => s
  | t, x :: xs, s => runFrom A omega n (t + 1) xs (A.step omega n t x s)

/-- Final mutable state after one sequential pass. -/
def run (A : WordStreamAlg E) (omega : A.Seed) (P : List E) : A.State :=
  runFrom A omega P.length 0 P (A.init omega P.length)

/-- The final estimate, or `none` if the algorithm reports overflow. -/
def estimate (A : WordStreamAlg E) (omega : A.Seed) (P : List E) : Option ℝ :=
  A.out omega P.length (run A omega P)

/-- Inner-probability success, using the bundled probability space. -/
def Succeeds (A : WordStreamAlg E) (good : A.Seed → Prop) (c : ENNReal) : Prop :=
  @CosDensity.SucceedsWP A.Seed A.seedMeasurable A.measure good c

end WordStreamAlg

end CosDensity.Supplement


