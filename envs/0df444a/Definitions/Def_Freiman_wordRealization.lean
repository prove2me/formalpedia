-- Prove2me | Definitions.Def_Freiman_wordRealization
-- name    : Freiman_wordRealization
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T10:06:17.028234+00:00
-- url     : https://prove2.me/theorems/e20e93a4-0469-4521-9516-fb7c25ea0e29
-- title:
--   Word occurrences and separated block copies
-- statement:
--   Define occurrence and avoidance of a finite digit block, a finite alphabet condition, eventual membership in the alphabet $\{1,2,3\}$, and coordinatewise convergence for two-sided words. For a nonnegative integer $N$, separated copies concatenate the windows of radii $N,N+1,\ldots$, inserting the digit $2$ between successive windows and filling the negative positions with $2$. The beginning of window $j$ is $j(2N+j+1)$. BackgroundOrShift records the two kinds of limits distinguished in the report: a shift of the original word or a word on $\{1,2,3\}$. These are only definitions; existence, classification and spectral realization are separate open targets.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.1 (local words), §1.4 (forbidden block 31313), and §1.6, Theorem 1.9 (found:separated-peaks), explicit copied-block construction and its two cases.

import Definitions.Def_Freiman_symbolicMarkovSpectrum
import Mathlib.Analysis.Real.Sqrt

namespace Freiman

def MatchesBlock (a : ℤ → ℕ+) (w : List ℕ) (i : ℤ) : Prop :=
  ∀ k : ℕ, k < w.length → (a (i + (k : ℤ)) : ℕ) = w.getD k 0

def AvoidsBlock (a : ℤ → ℕ+) (w : List ℕ) : Prop :=
  ∀ i : ℤ, ¬ MatchesBlock a w i

def HasFiniteAlphabet (a : ℤ → ℕ+) : Prop :=
  ∃ M : ℕ, ∀ i : ℤ, (a i : ℕ) ≤ M

def EventuallyThree (a : ℤ → ℕ+) : Prop :=
  ∃ N : ℕ, ∀ i : ℤ, N ≤ i.natAbs → (a i : ℕ) ≤ 3

def CoordinateLimit (A : ℕ → ℤ → ℕ+) (a : ℤ → ℕ+) : Prop :=
  ∀ i : ℤ, ∀ᶠ j in Filter.atTop, A j i = a i

def copyStart (N j : ℕ) : ℕ := j * (2 * N + j + 1)

def SeparatedCopies (a b : ℤ → ℕ+) (N : ℕ) : Prop :=
  (∀ i : ℤ, i < 0 → (b i : ℕ) = 2) ∧
  (∀ j k : ℕ, k ≤ 2 * (N + j) →
    b ((copyStart N j + k : ℕ) : ℤ) = a ((k : ℤ) - ((N + j : ℕ) : ℤ))) ∧
  (∀ j : ℕ, (b ((copyStart N j + 2 * (N + j) + 1 : ℕ) : ℤ) : ℕ) = 2)

def BackgroundOrShift (a y : ℤ → ℕ+) : Prop :=
  (∃ s : ℤ, ∀ i : ℤ, y i = a (s + i)) ∨
  (∀ i : ℤ, (y i : ℕ) ≤ 3)

end Freiman


