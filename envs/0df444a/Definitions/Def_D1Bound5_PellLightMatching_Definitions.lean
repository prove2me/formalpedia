-- Prove2me | Definitions.Def_D1Bound5_PellLightMatching_Definitions
-- name    : D1Bound5_PellLightMatching_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:24:28.669636+00:00
-- url     : https://prove2.me/theorems/895aa93b-d887-4031-8e16-7d6fc036678a
-- title:
--   Pell Light Matching
-- statement:
--   Definitions for pell light matching in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `PellLightSquareMasks`, `PellLightSquareMasks.k`, `PellLightSquareMasks.ordinary`, `PellLightSquareMasks.scaled`, `instDecidableEqPellLightSquareMasks`, `instDecidableEqPellLightSquareMasks.decEq`, `instReprPellLightSquareMasks`, `instReprPellLightSquareMasks.repr` and 7 further declarations.
-- source:
--   D1Bound5/PellLightMatching.lean, lines 5-9, SHA-256 3ac624524aca77968a148009c6a760dcc5c6aecfa02aa6a1652c7bf7443543c6; D1Bound5/PellLightMatching.lean, lines 11-12, SHA-256 3ac624524aca77968a148009c6a760dcc5c6aecfa02aa6a1652c7bf7443543c6; D1Bound5/PellLightMatching.lean, lines 14-16, SHA-256 3ac624524aca77968a148009c6a760dcc5c6aecfa02aa6a1652c7bf7443543c6; D1Bound5/PellLightMatching.lean, lines 18-20, SHA-256 3ac624524aca77968a148009c6a760dcc5c6aecfa02aa6a1652c7bf7443543c6; D1Bound5/PellLightMatching.lean, lines 22-22, SHA-256 3ac624524aca77968a148009c6a760dcc5c6aecfa02aa6a1652c7bf7443543c6; D1Bound5/PellLightMatching.lean, lines 24-27, SHA-256 3ac624524aca77968a148009c6a760dcc5c6aecfa02aa6a1652c7bf7443543c6; D1Bound5/PellLightMatching.lean, lines 29-38, SHA-256 3ac624524aca77968a148009c6a760dcc5c6aecfa02aa6a1652c7bf7443543c6; D1Bound5/PellLightMatching.lean, lines 40-45, SHA-256 3ac624524aca77968a148009c6a760dcc5c6aecfa02aa6a1652c7bf7443543c6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init

section
namespace D1Bound5

structure PellLightSquareMasks where
  k : Nat
  ordinary : Nat
  scaled : Nat
deriving DecidableEq, Repr

def pellLightScalarMaskBool (k mask : Nat) (z : Int) : Bool :=
  mask.testBit ((z % Int.ofNat (k + 1)).toNat)

def pellLightScalarMaskValidBool (c : Int) (k mask : Nat) : Bool :=
  (List.range (k + 1)).all fun r =>
    pellLightScalarMaskBool k mask (c * Int.ofNat r * Int.ofNat r)

def PellLightSquareMasks.validBool (d : Int) (m : PellLightSquareMasks) : Bool :=
  pellLightScalarMaskValidBool 1 m.k m.ordinary &&
    pellLightScalarMaskValidBool d m.k m.scaled

def pellLightDefaultMasks : PellLightSquareMasks := ⟨0, 1, 1⟩

def pellLightSelectMasks : List PellLightSquareMasks → Nat → PellLightSquareMasks
  | [], _ => pellLightDefaultMasks
  | m :: _, 0 => m
  | _ :: ms, n + 1 => pellLightSelectMasks ms n

def pellLightPairChecks (ms : List PellLightSquareMasks) (x : Int) :
    List Int → List (Nat × Nat) → Bool
  | [], [] => true
  | y :: ys, w :: ws =>
      let p := pellLightSelectMasks ms w.1
      let n := pellLightSelectMasks ms w.2
      ((!pellLightScalarMaskBool p.k p.ordinary (x*y+1)) &&
        (!pellLightScalarMaskBool n.k n.scaled (x*y-1))) &&
        pellLightPairChecks ms x ys ws
  | _, _ => false

def pellLightMatchingCheck (ms : List PellLightSquareMasks) :
    List Int → List (List (Nat × Nat)) → Bool
  | [], [] => true
  | x :: xs, ws :: wss =>
      pellLightPairChecks ms x xs ws && pellLightMatchingCheck ms xs wss
  | _, _ => false

end D1Bound5
end


