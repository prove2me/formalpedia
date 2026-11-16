-- Prove2me | Definitions.Def_GPTIP632_Classical_Supplement_BinaryComparison
-- name    : GPTIP632_Classical_Supplement_BinaryComparison
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:13:47.552444+00:00
-- url     : https://prove2.me/theorems/688f1c04-a256-482e-838c-86bdb4afe004
-- title:
--   Binary fractions, the comparison promise problem and the largest accepted fraction
-- statement:
--   A bit string $t=t_1\cdots t_m$ denotes the exact rational $\bar t=\sum_{j=1}^m t_j2^{-j}$, with the first bit most significant. For a real number $v$, define the comparison promise problem on nonempty strings by
--
--   $$L_{v,\mathrm{yes}}=\{t: \bar t+|t|^{-2}\le v\},\qquad L_{v,\mathrm{no}}=\{t:v\le\bar t-|t|^{-2}\}.$$
--
--   A total Boolean function $D$ decides this promise when it accepts every yes-instance and rejects every no-instance. For $m\ge1$, let $w_m$ be the greatest binary fraction of an accepted string of length $m$, or zero if none is accepted. The numerator is a finite natural-number maximum, and $w_m$ is stored as an exact rational with denominator $2^m$. Its output encoding retains exactly $m$ most-significant-first bits, including leading zeros.
--
--   These objects are the comparison problem and approximation sequence used in Lemma G.2. No effectiveness of $D$ is built into this definition.
-- source:
--   Kishor Bharti, Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical Theories, STOC 2027 submission #632 (October 2026), source.pdf SHA-256 ebbc45027e7a3b48cbfb1a2deb89e9a7d8374373b23763680b948fda16cf4da7, p.32 (PDF p.34), §G.1; p.33 (PDF p.35), Lemma G.2

import Mathlib
import Definitions.Def_GPTIP632_Classical_Protocol

namespace GPTIP632.Classical.Supplement

/-- The integer whose most-significant-first binary digits are `t`. -/
def binaryNumerator (t : List Bool) : ℕ :=
  t.foldl (fun a b => 2 * a + b.toNat) 0

/-- The binary fraction `0.t₁…tₘ`, as an exact rational. §G.1, p.32 (PDF p.34). -/
def binaryFraction (t : List Bool) : ℚ :=
  (binaryNumerator t : ℚ) / 2 ^ t.length

/-- The promise problem `L_v` of §G.1. Empty strings are excluded on both sides. -/
def comparisonProblem (v : ℝ) : KTUnitary.Synth.PromiseProblem :=
  ({t | 0 < t.length ∧ (binaryFraction t : ℝ) + 1 / (t.length : ℝ) ^ 2 ≤ v},
   {t | 0 < t.length ∧ v ≤ (binaryFraction t : ℝ) - 1 / (t.length : ℝ) ^ 2})

/-- Correctness of a total Boolean decision function on the promise of `L_v`. -/
def DecidesComparison (D : List Bool → Bool) (v : ℝ) : Prop :=
  (∀ t ∈ (comparisonProblem v).1, D t = true) ∧
  (∀ t ∈ (comparisonProblem v).2, D t = false)

/-- Numerator of the greatest accepted `m`-bit binary fraction; zero when none is accepted.
`Finset.sup` on naturals is the finite maximum with bottom `0`. -/
def acceptedNumerator (D : List Bool → Bool) (m : ℕ) : ℕ :=
  ((strings m).filter (fun t => D t)).sup binaryNumerator

/-- `w_m` of Lemma G.2, as a rational with denominator `2^m`. -/
def acceptedMaximum (D : List Bool → Bool) (m : ℕ) : ℚ :=
  (acceptedNumerator D m : ℚ) / 2 ^ m

/-- The `m` binary digits of `w_m`, most significant first, retaining leading zeros. -/
def acceptedDigits (D : List Bool → Bool) (m : ℕ) : List Bool :=
  ((List.range m).map (fun j => Nat.testBit (acceptedNumerator D m) j)).reverse

end GPTIP632.Classical.Supplement


