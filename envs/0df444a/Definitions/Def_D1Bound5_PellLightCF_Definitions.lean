-- Prove2me | Definitions.Def_D1Bound5_PellLightCF_Definitions
-- name    : D1Bound5_PellLightCF_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:01:34.645328+00:00
-- url     : https://prove2.me/theorems/9f57d38f-6e24-4cef-84fb-9d272488b72b
-- title:
--   Pell Light CF
-- statement:
--   All seven fields are integers. `pp,qq` are the preceding convergent; `p,q` are the current one. No real arithmetic occurs in the certificate. The named objects in this bundle include `PellLightCFState`, `PellLightCFState.Q`, `PellLightCFState.a`, `PellLightCFState.m`, `PellLightCFState.p`, `PellLightCFState.pp`, `PellLightCFState.q`, `PellLightCFState.qq` and 16 further declarations.
-- source:
--   D1Bound5/PellLightCF.lean, lines 5-15, SHA-256 666a6f9458e71d18a3787829dd76ef5c88fcd282724ebcf75d0c850485de22ae; D1Bound5/PellLightCF.lean, lines 17-17, SHA-256 666a6f9458e71d18a3787829dd76ef5c88fcd282724ebcf75d0c850485de22ae; D1Bound5/PellLightCF.lean, lines 19-23, SHA-256 666a6f9458e71d18a3787829dd76ef5c88fcd282724ebcf75d0c850485de22ae; D1Bound5/PellLightCF.lean, lines 25-27, SHA-256 666a6f9458e71d18a3787829dd76ef5c88fcd282724ebcf75d0c850485de22ae; D1Bound5/PellLightCF.lean, lines 29-31, SHA-256 666a6f9458e71d18a3787829dd76ef5c88fcd282724ebcf75d0c850485de22ae; D1Bound5/PellLightCF.lean, lines 33-34, SHA-256 666a6f9458e71d18a3787829dd76ef5c88fcd282724ebcf75d0c850485de22ae; D1Bound5/PellLightCF.lean, lines 36-37, SHA-256 666a6f9458e71d18a3787829dd76ef5c88fcd282724ebcf75d0c850485de22ae; D1Bound5/PellLightCF.lean, lines 39-40, SHA-256 666a6f9458e71d18a3787829dd76ef5c88fcd282724ebcf75d0c850485de22ae; D1Bound5/PellLightCF.lean, lines 42-43, SHA-256 666a6f9458e71d18a3787829dd76ef5c88fcd282724ebcf75d0c850485de22ae; D1Bound5/PellLightCF.lean, lines 45-48, SHA-256 666a6f9458e71d18a3787829dd76ef5c88fcd282724ebcf75d0c850485de22ae; D1Bound5/PellLightCF.lean, lines 50-52, SHA-256 666a6f9458e71d18a3787829dd76ef5c88fcd282724ebcf75d0c850485de22ae; D1Bound5/PellLightCF.lean, lines 54-58, SHA-256 666a6f9458e71d18a3787829dd76ef5c88fcd282724ebcf75d0c850485de22ae; D1Bound5/PellLightCF.lean, lines 60-65, SHA-256 666a6f9458e71d18a3787829dd76ef5c88fcd282724ebcf75d0c850485de22ae. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init

section
namespace D1Bound5

/-- All seven fields are integers. `pp,qq` are the preceding convergent;
`p,q` are the current one. No real arithmetic occurs in the certificate. -/
structure PellLightCFState where
  m : Int
  Q : Int
  a : Int
  pp : Int
  p : Int
  qq : Int
  q : Int
  deriving DecidableEq, Repr

def pellLightCFInit (a0 : Int) : PellLightCFState := ⟨0,1,a0,1,a0,0,1⟩

def pellLightCFStep (d a0 : Int) (s : PellLightCFState) : PellLightCFState :=
  let m := s.Q*s.a-s.m
  let Q := (d-m^2)/s.Q
  let a := (a0+m)/Q
  ⟨m,Q,a,s.p,a*s.p+s.pp,s.q,a*s.q+s.qq⟩

def pellLightCFAt (d a0 : Int) : PellLightCFState → Nat → PellLightCFState
  | s,0 => s
  | s,n+1 => pellLightCFAt d a0 (pellLightCFStep d a0 s) n

def pellLightCFTrace (d a0 : Int) : PellLightCFState → Nat → List PellLightCFState
  | s,0 => [s]
  | s,n+1 => s :: pellLightCFTrace d a0 (pellLightCFStep d a0 s) n

def PellLightCFStateGood (a0 : Int) (s : PellLightCFState) : Prop :=
  0 < s.Q ∧ s.a*s.Q ≤ a0+s.m ∧ a0+s.m < (s.a+1)*s.Q

def PellLightCFTransitionGood (d a0 : Int) (s : PellLightCFState) : Prop :=
  s.Q*(pellLightCFStep d a0 s).Q = d-(pellLightCFStep d a0 s).m^2

instance (a0 : Int) (s : PellLightCFState) : Decidable (PellLightCFStateGood a0 s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance (d a0 : Int) (s : PellLightCFState) : Decidable (PellLightCFTransitionGood d a0 s) :=
  inferInstanceAs (Decidable (_ = _))

def pellLightCFCheckFrom (d a0 : Int) : PellLightCFState → Nat → Bool
  | s,0 => decide (PellLightCFStateGood a0 s)
  | s,n+1 => decide (PellLightCFStateGood a0 s ∧ PellLightCFTransitionGood d a0 s) &&
      pellLightCFCheckFrom d a0 (pellLightCFStep d a0 s) n

def pellLightCFPrefixCheck (d a0 : Int) (N : Nat) : Bool :=
  decide (0 ≤ a0 ∧ a0^2 < d ∧ d < (a0+1)^2) &&
    pellLightCFCheckFrom d a0 (pellLightCFInit a0) N

/-- The actual finite output, computed rather than postulated. -/
def pellLightCFSolutions (d a0 X : Int) (N : Nat) : List (Int × Int) :=
  (pellLightCFTrace d a0 (pellLightCFInit a0) N).filterMap fun s =>
    if 0 < s.p ∧ 0 < s.q ∧ s.p ≤ X ∧ s.p^2-d*s.q^2=2
      then some (s.p,s.q) else none

/-- All three original finite-prefix obligations, with the exact ordered
magnitude list. The bridge supplies their unchanged mathematical meanings. -/
def pellLightFiniteCheck (d a0 X : Int) (N : Nat) (magnitudes : List Int) : Bool :=
  pellLightCFPrefixCheck d a0 N &&
    (decide (X < (pellLightCFAt d a0 (pellLightCFInit a0) N).p) &&
      decide ((pellLightCFSolutions d a0 X N).map (fun uv => uv.1^2-1) = magnitudes))

end D1Bound5
end


