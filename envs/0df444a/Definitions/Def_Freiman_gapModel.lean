-- Prove2me | Definitions.Def_Freiman_gapModel
-- name    : Freiman_gapModel
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T10:37:36.466752+00:00
-- url     : https://prove2.me/theorems/47bd2d62-4e8b-4fec-9225-0b1fcdb51f81
-- title:
--   Marked words, rational cylinders and explicit gap extremizers
-- statement:
--   Exact source marked words A and B, rational thresholds, reflection and physical-word matching, rational cylinder endpoint arithmetic, and the explicit eventually periodic extremizers. These definitions assert no theorem and leave the existing spectra and cfValue unchanged.
-- source:
--   Freiman Hall ray report, m3.tex, m3_maximum.tex, m3_minimum.tex; certificates/gap

import Mathlib.Data.Rat.Cast.Order
import Definitions.Def_Freiman_symbolicMarkovSpectrum
import Definitions.Def_Freiman_prefixEval
import Definitions.Def_Freiman_gapThreshold
import Definitions.Def_Freiman_cF

namespace Freiman

noncomputable def gapWindow : ℝ := 2263914769 / 500000000
noncomputable def gapCap : ℝ := 4527829567 / 1000000000
def gapDigits (a : ℤ → ℕ+) : Prop := ∀ i, (a i : ℕ) ≤ 4
def gapCapped (a : ℤ → ℕ+) : Prop := ∀ i, localValue a i ≤ gapCap
def gapReflect (a : ℤ → ℕ+) : ℤ → ℕ+ := fun i => a (-i)

structure GapState where
  word : List ℕ+
  centre : ℕ
  deriving DecidableEq, Inhabited

def gapReverse (s : GapState) : GapState := ⟨s.word.reverse, s.word.length - 1 - s.centre⟩
def gapMatch (a : ℤ → ℕ+) (i : ℤ) (s : GapState) : Prop :=
  s.centre < s.word.length ∧
  ∀ n : ℕ, n < s.word.length → a (i + (n : ℤ) - (s.centre : ℤ)) = s.word[n]!
def gapSeedA : GapState := ⟨[3,3,1,1,2,1,3,1,3,4,3,1,3,1,3,4,4],9⟩
def gapSeedB : GapState := ⟨[3,1,1,2,3,4,4,3,2,2],5⟩
def gapReduced (a : ℤ → ℕ+) (i : ℤ) : Prop :=
  gapMatch a i gapSeedA ∨ gapMatch a i (gapReverse gapSeedA) ∨
  gapMatch a i gapSeedB ∨ gapMatch a i (gapReverse gapSeedB)

def gapRatPrefix : List ℕ+ → ℚ → ℚ
  | [], x => x
  | d :: w, x => 1 / ((d : ℕ) + gapRatPrefix w x)
def gapRatLower (w : List ℕ+) : ℚ := min (gapRatPrefix w (1/5)) (gapRatPrefix w (5/6))
def gapRatUpper (w : List ℕ+) : ℚ := max (gapRatPrefix w (1/5)) (gapRatPrefix w (5/6))
def gapCylinderLower (w : List ℕ+) (j : ℕ) : ℚ :=
  (w[j]! : ℕ) + gapRatLower ((w.take j).reverse) + gapRatLower (w.drop (j+1))
def gapCylinderUpper (w : List ℕ+) (j : ℕ) : ℚ :=
  (w[j]! : ℕ) + gapRatUpper ((w.take j).reverse) + gapRatUpper (w.drop (j+1))

def gapEventuallyPeriodic (u v : List ℕ+) : ℕ → ℕ+ := fun n =>
  if n < u.length then u[n]! else v[(n-u.length) % v.length]!
def gapJoin (l r : ℕ → ℕ+) : ℤ → ℕ+ := fun i =>
  if i = 0 then 4 else if i < 0 then l ((-i-1).toNat) else r ((i-1).toNat)
def gapALeft : ℕ → ℕ+ := gapEventuallyPeriodic [3,1,3,1,2,1,1,3,3] [3,1,3,1,2,1]
def gapARight : ℕ → ℕ+ := gapEventuallyPeriodic [3,1,3,1,3] [4,4,4,3,2,3]
def gapBLeft : ℕ → ℕ+ := gapEventuallyPeriodic [3,2,1,1] [3,1,3,1,2,1]
def gapBRight : ℕ → ℕ+ := gapEventuallyPeriodic [4,3,2,2] [3,1,3,1,2,1]
def gapExtremizerA : ℤ → ℕ+ := gapJoin gapALeft gapARight
def gapExtremizerB : ℤ → ℕ+ := gapJoin gapBLeft gapBRight

def gapAvoids (a : ℤ → ℕ+) (w : List ℕ+) : Prop :=
  (∀ i, ¬ gapMatch a i ⟨w,0⟩) ∧ (∀ i, ¬ gapMatch a i ⟨w.reverse,0⟩)
def gapMaximumForbidden : List (List ℕ+) :=
  [[1,4],[2,4],[3,4,3,3],[4,4,4,3,4],[3,3,4,4,4],[1,3,1,3,1,3],
   [3,4,4,3,3],[4,4,4,3,2,1],[4,4,4,3,2,2],[3,1,3,1,3,3,3],[2,3,4,3]]
def gapMinimumForbidden : List (List ℕ+) := [[1,4],[2,4],[1,3,1,3,1,3],[2,3,1,3,1,3]]

def gapLocalWindow (a : ℤ → ℕ+) (i : ℤ) (radius : ℕ) : List ℕ+ :=
  (List.range (2*radius+1)).map (fun n => a (i+(n : ℤ)-(radius : ℤ)))
def gapARepresentatives : List ℤ :=
  (List.range 37).map (fun n => (n : ℤ)-20) |>.filter (fun i => i != 0)
def gapBRepresentatives : List ℤ :=
  (List.range 29).map (fun n => (n : ℤ)-14) |>.filter (fun i => i != 0)

def gapLeftTail (a : ℤ → ℕ+) : ℕ → ℕ+ := fun n => a (-(n : ℤ)-1)
def gapRightTail (a : ℤ → ℕ+) : ℕ → ℕ+ := fun n => a ((n : ℤ)+1)
def gapSameBefore (b c : ℕ → ℕ+) (n : ℕ) : Prop := ∀ k, k < n → b k = c k
def gapUpperDigit (b c : ℕ → ℕ+) (n : ℕ) : Prop := if Even n then c n ≤ b n else b n ≤ c n
def gapLowerDigit (b c : ℕ → ℕ+) (n : ℕ) : Prop := if Even n then b n ≤ c n else c n ≤ b n
def gapMaximumAdmissible (a : ℤ → ℕ+) : Prop :=
  (∀ w ∈ gapMaximumForbidden, gapAvoids a w) ∧ gapAvoids a [3,3,4]
def gapMinimumAdmissible (a : ℤ → ℕ+) : Prop := ∀ w ∈ gapMinimumForbidden, gapAvoids a w
noncomputable def gapPeriodSValue : ℝ := (2*Real.sqrt 462-29)/53
noncomputable def gapPeriodTValue : ℝ := (Real.sqrt 243542-430)/269

end Freiman


