-- Prove2me | Definitions.Def_Freiman_gapCertificate
-- name    : Freiman_gapCertificate
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T10:39:07.853436+00:00
-- url     : https://prove2.me/theorems/84ba95d0-504c-4245-a958-c32c10572acc
-- title:
--   Finite four-digit partition certificate semantics
-- statement:
--   A finite inductive four-child certificate type; separate predicates for complete child coverage, exact numerical and combinatorial leaf checks, and applicability of previously established table rows. The reduction outcome keeps its distinguished-height window assumption explicitly.
-- source:
--   Freiman Hall ray report, m3.tex, m3_maximum.tex, m3_minimum.tex; certificates/gap

import Definitions.Def_Freiman_gapModel
namespace Freiman

structure GapRow where
  state : GapState
  bound : ℚ
  deriving DecidableEq, Inhabited

inductive GapReason where
  | above (j : ℕ)
  | below
  | prior (r : ℕ)
  | upperRow (r : ℕ)
  | terminal
  deriving DecidableEq, Inhabited

inductive GapTree where
  | leaf (s : GapState) (r : GapReason)
  | split (s : GapState) (left : Bool) (one two three four : GapTree)

def gapRoot : GapTree → GapState
  | .leaf s _ => s
  | .split s _ _ _ _ _ => s

def gapLeaves : GapTree → List (GapState × GapReason)
  | .leaf s r => [(s,r)]
  | .split _ _ a b c d => gapLeaves a ++ gapLeaves b ++ gapLeaves c ++ gapLeaves d

def gapExtend (s : GapState) (left : Bool) (d : ℕ+) : GapState :=
  if left then ⟨d :: s.word, s.centre+1⟩ else ⟨s.word ++ [d],s.centre⟩

def gapCoverage : GapTree → Prop
  | .leaf s _ => s.centre < s.word.length
  | .split s left a b c d => s.centre < s.word.length ∧
      gapRoot a = gapExtend s left 1 ∧ gapRoot b = gapExtend s left 2 ∧
      gapRoot c = gapExtend s left 3 ∧ gapRoot d = gapExtend s left 4 ∧
      gapCoverage a ∧ gapCoverage b ∧ gapCoverage c ∧ gapCoverage d

inductive GapMode where
  | forbidden
  | upper (cut : ℚ)
  | reduction

def gapModeOutcome (mode : GapMode) (a : ℤ → ℕ+) (i : ℤ) : Prop :=
  match mode with
  | .forbidden => False
  | .upper c => localValue a i < (c : ℝ)
  | .reduction => gapWindow < localValue a i → gapReduced a i

def gapAlignedContains (s v : GapState) : Prop :=
  ∃ k : ℕ, (s.word.drop k).take v.word.length = v.word ∧ s.centre = k+v.centre

def gapWordContains (s : GapState) (w : List ℕ+) : Prop :=
  ∃ k : ℕ, (s.word.drop k).take w.length = w

def gapBelowCheck (mode : GapMode) (x : ℚ) : Prop :=
  match mode with
  | .forbidden => False
  | .upper c => x ≤ c
  | .reduction => x ≤ 2263914769 / 500000000

-- The row lists are parameters: a lower proof may use only its preceding rows;
-- the upper certificates use neither table, and forcing uses all validated rows.
def gapLeafCheck (lower upper : List GapRow) (mode : GapMode)
    (s : GapState) (r : GapReason) : Prop :=
  match r with
  | .above j => j < s.word.length ∧ 4527829567 / 1000000000 ≤ gapCylinderLower s.word j
  | .below => gapBelowCheck mode (gapCylinderUpper s.word s.centre)
  | .prior n => n < lower.length ∧ (lower[n]!).state.word ≠ [] ∧
      (gapWordContains s (lower[n]!).state.word ∨ gapWordContains s (lower[n]!).state.word.reverse)
  | .upperRow n => n < upper.length ∧ (upper[n]!).state.centre < (upper[n]!).state.word.length ∧ gapBelowCheck mode (upper[n]!).bound ∧
      (gapAlignedContains s (upper[n]!).state ∨ gapAlignedContains s (gapReverse (upper[n]!).state))
  | .terminal => mode = .reduction ∧
      (gapAlignedContains s gapSeedA ∨ gapAlignedContains s (gapReverse gapSeedA) ∨
       gapAlignedContains s gapSeedB ∨ gapAlignedContains s (gapReverse gapSeedB))

def gapChecks (lower upper : List GapRow) (mode : GapMode) (t : GapTree) : Prop :=
  ∀ sr ∈ gapLeaves t, gapLeafCheck lower upper mode sr.1 sr.2

def gapLowerValid (a : ℤ → ℕ+) (rows : List GapRow) : Prop :=
  ∀ row ∈ rows, gapAvoids a row.state.word

def gapUpperValid (a : ℤ → ℕ+) (rows : List GapRow) : Prop :=
  ∀ row ∈ rows, ∀ i,
    (gapMatch a i row.state ∨ gapMatch a i (gapReverse row.state)) → localValue a i < (row.bound : ℝ)

def GapCertificateSoundness : Prop :=
  ∀ (lower upper : List GapRow) (mode : GapMode) (tree : GapTree)
    (a : ℤ → ℕ+) (i : ℤ),
    gapDigits a → gapCapped a → gapLowerValid a lower → gapUpperValid a upper →
    gapCoverage tree → gapChecks lower upper mode tree → gapMatch a i (gapRoot tree) →
    gapModeOutcome mode a i

end Freiman


