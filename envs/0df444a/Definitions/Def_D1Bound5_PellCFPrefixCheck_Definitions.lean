-- Prove2me | Definitions.Def_D1Bound5_PellCFPrefixCheck_Definitions
-- name    : D1Bound5_PellCFPrefixCheck_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:31:50.654125+00:00
-- url     : https://prove2.me/theorems/deff27e5-5a6b-4296-b961-009b129b31a4
-- title:
--   Pell CFPrefix Check
-- statement:
--   All seven fields are integers. `pp,qq` are the preceding convergent; `p,q` are the current one. No real arithmetic occurs in the certificate. The named objects in this bundle include `PellCFState`, `PellCFState.Q`, `PellCFState.a`, `PellCFState.m`, `PellCFState.p`, `PellCFState.pp`, `PellCFState.q`, `PellCFState.qq` and 16 further declarations.
-- source:
--   D1Bound5/PellCFPrefixCheck.lean, lines 5-15, SHA-256 a5468d17d5b8fd8febaae9f486b606a6148827a88a3b76dca5782d036662adba; D1Bound5/PellCFPrefixCheck.lean, lines 17-17, SHA-256 a5468d17d5b8fd8febaae9f486b606a6148827a88a3b76dca5782d036662adba; D1Bound5/PellCFPrefixCheck.lean, lines 19-23, SHA-256 a5468d17d5b8fd8febaae9f486b606a6148827a88a3b76dca5782d036662adba; D1Bound5/PellCFPrefixCheck.lean, lines 25-27, SHA-256 a5468d17d5b8fd8febaae9f486b606a6148827a88a3b76dca5782d036662adba; D1Bound5/PellCFPrefixCheck.lean, lines 29-31, SHA-256 a5468d17d5b8fd8febaae9f486b606a6148827a88a3b76dca5782d036662adba; D1Bound5/PellCFPrefixCheck.lean, lines 33-34, SHA-256 a5468d17d5b8fd8febaae9f486b606a6148827a88a3b76dca5782d036662adba; D1Bound5/PellCFPrefixCheck.lean, lines 36-37, SHA-256 a5468d17d5b8fd8febaae9f486b606a6148827a88a3b76dca5782d036662adba; D1Bound5/PellCFPrefixCheck.lean, lines 39-40, SHA-256 a5468d17d5b8fd8febaae9f486b606a6148827a88a3b76dca5782d036662adba; D1Bound5/PellCFPrefixCheck.lean, lines 42-43, SHA-256 a5468d17d5b8fd8febaae9f486b606a6148827a88a3b76dca5782d036662adba; D1Bound5/PellCFPrefixCheck.lean, lines 45-48, SHA-256 a5468d17d5b8fd8febaae9f486b606a6148827a88a3b76dca5782d036662adba; D1Bound5/PellCFPrefixCheck.lean, lines 50-52, SHA-256 a5468d17d5b8fd8febaae9f486b606a6148827a88a3b76dca5782d036662adba; D1Bound5/PellCFPrefixCheck.lean, lines 54-58, SHA-256 a5468d17d5b8fd8febaae9f486b606a6148827a88a3b76dca5782d036662adba; D1Bound5/PellCFPrefixCheck.lean, lines 106-108, SHA-256 a5468d17d5b8fd8febaae9f486b606a6148827a88a3b76dca5782d036662adba. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

section
namespace D1Bound5

/-- All seven fields are integers. `pp,qq` are the preceding convergent;
`p,q` are the current one. No real arithmetic occurs in the certificate. -/
structure PellCFState where
  m : ℤ
  Q : ℤ
  a : ℤ
  pp : ℤ
  p : ℤ
  qq : ℤ
  q : ℤ
  deriving DecidableEq, Repr

def pellCFInit (a0 : ℤ) : PellCFState := ⟨0,1,a0,1,a0,0,1⟩

def pellCFStep (d a0 : ℤ) (s : PellCFState) : PellCFState :=
  let m := s.Q*s.a-s.m
  let Q := (d-m^2)/s.Q
  let a := (a0+m)/Q
  ⟨m,Q,a,s.p,a*s.p+s.pp,s.q,a*s.q+s.qq⟩

def pellCFAt (d a0 : ℤ) : PellCFState → ℕ → PellCFState
  | s,0 => s
  | s,n+1 => pellCFAt d a0 (pellCFStep d a0 s) n

def pellCFTrace (d a0 : ℤ) : PellCFState → ℕ → List PellCFState
  | s,0 => [s]
  | s,n+1 => s :: pellCFTrace d a0 (pellCFStep d a0 s) n

def PellCFStateGood (a0 : ℤ) (s : PellCFState) : Prop :=
  0 < s.Q ∧ s.a*s.Q ≤ a0+s.m ∧ a0+s.m < (s.a+1)*s.Q

def PellCFTransitionGood (d a0 : ℤ) (s : PellCFState) : Prop :=
  s.Q*(pellCFStep d a0 s).Q = d-(pellCFStep d a0 s).m^2

instance (a0 : ℤ) (s : PellCFState) : Decidable (PellCFStateGood a0 s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance (d a0 : ℤ) (s : PellCFState) : Decidable (PellCFTransitionGood d a0 s) :=
  inferInstanceAs (Decidable (_ = _))

def pellCFCheckFrom (d a0 : ℤ) : PellCFState → ℕ → Bool
  | s,0 => decide (PellCFStateGood a0 s)
  | s,n+1 => decide (PellCFStateGood a0 s ∧ PellCFTransitionGood d a0 s) &&
      pellCFCheckFrom d a0 (pellCFStep d a0 s) n

def pellCFPrefixCheck (d a0 : ℤ) (N : ℕ) : Bool :=
  decide (0 ≤ a0 ∧ a0^2 < d ∧ d < (a0+1)^2) &&
    pellCFCheckFrom d a0 (pellCFInit a0) N

/-- The actual finite output, computed rather than postulated. -/
def pellCFSolutions (d a0 X : ℤ) (N : ℕ) : List (ℤ × ℤ) :=
  (pellCFTrace d a0 (pellCFInit a0) N).filterMap fun s =>
    if 0 < s.p ∧ 0 < s.q ∧ s.p ≤ X ∧ s.p^2-d*s.q^2=2
      then some (s.p,s.q) else none







noncomputable def pellRealTail (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n+1 => pellRealTail (Int.fract x)⁻¹ n



















end D1Bound5
end


