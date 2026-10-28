-- Prove2me | Definitions.Def_D1Bound5_PellMatchingCheck_Definitions
-- name    : D1Bound5_PellMatchingCheck_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:31:36.053517+00:00
-- url     : https://prove2.me/theorems/a78b75c0-b2e7-470b-8692-5f261553b7cd
-- title:
--   Pell Matching Check
-- statement:
--   A mask accepting every residue of c times an integral square. Modulus k+1 is always nonzero, including for the harmless default mask. The named objects in this bundle include `PellScalarMaskValid`, `instDecidablePellScalarMaskValid`, `pellScalarMaskBool`, `PellSquareMasks`, `PellSquareMasks.k`, `PellSquareMasks.ordinary`, `PellSquareMasks.scaled`, `instDecidableEqPellSquareMasks` and 16 further declarations.
-- source:
--   D1Bound5/PellMatchingCheck.lean, lines 7-10, SHA-256 c1c0284d3cb9fe91ae3599a7d1d28cf05b2201c8cbaef193b20c1b2b5f4ccfa0; D1Bound5/PellMatchingCheck.lean, lines 12-14, SHA-256 c1c0284d3cb9fe91ae3599a7d1d28cf05b2201c8cbaef193b20c1b2b5f4ccfa0; D1Bound5/PellMatchingCheck.lean, lines 16-17, SHA-256 c1c0284d3cb9fe91ae3599a7d1d28cf05b2201c8cbaef193b20c1b2b5f4ccfa0; D1Bound5/PellMatchingCheck.lean, lines 26-31, SHA-256 c1c0284d3cb9fe91ae3599a7d1d28cf05b2201c8cbaef193b20c1b2b5f4ccfa0; D1Bound5/PellMatchingCheck.lean, lines 33-34, SHA-256 c1c0284d3cb9fe91ae3599a7d1d28cf05b2201c8cbaef193b20c1b2b5f4ccfa0; D1Bound5/PellMatchingCheck.lean, lines 36-38, SHA-256 c1c0284d3cb9fe91ae3599a7d1d28cf05b2201c8cbaef193b20c1b2b5f4ccfa0; D1Bound5/PellMatchingCheck.lean, lines 40-40, SHA-256 c1c0284d3cb9fe91ae3599a7d1d28cf05b2201c8cbaef193b20c1b2b5f4ccfa0; D1Bound5/PellMatchingCheck.lean, lines 52-57, SHA-256 c1c0284d3cb9fe91ae3599a7d1d28cf05b2201c8cbaef193b20c1b2b5f4ccfa0; D1Bound5/PellMatchingCheck.lean, lines 68-79, SHA-256 c1c0284d3cb9fe91ae3599a7d1d28cf05b2201c8cbaef193b20c1b2b5f4ccfa0; D1Bound5/PellMatchingCheck.lean, lines 106-112, SHA-256 c1c0284d3cb9fe91ae3599a7d1d28cf05b2201c8cbaef193b20c1b2b5f4ccfa0; D1Bound5/PellMatchingCheck.lean, lines 136-138, SHA-256 c1c0284d3cb9fe91ae3599a7d1d28cf05b2201c8cbaef193b20c1b2b5f4ccfa0; D1Bound5/PellMatchingCheck.lean, lines 140-142, SHA-256 c1c0284d3cb9fe91ae3599a7d1d28cf05b2201c8cbaef193b20c1b2b5f4ccfa0; D1Bound5/PellMatchingCheck.lean, lines 193-201, SHA-256 c1c0284d3cb9fe91ae3599a7d1d28cf05b2201c8cbaef193b20c1b2b5f4ccfa0; D1Bound5/PellMatchingCheck.lean, lines 203-209, SHA-256 c1c0284d3cb9fe91ae3599a7d1d28cf05b2201c8cbaef193b20c1b2b5f4ccfa0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.List.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

section
namespace D1Bound5

/-- A mask accepting every residue of c times an integral square.  Modulus
k+1 is always nonzero, including for the harmless default mask. -/
def PellScalarMaskValid (c : ℤ) (k mask : ℕ) : Prop :=
  ∀ r : ZMod (k+1), mask.testBit (((c : ZMod (k+1))*r*r).val) = true

instance (c : ℤ) (k mask : ℕ) : Decidable (PellScalarMaskValid c k mask) := by
  unfold PellScalarMaskValid
  infer_instance

def pellScalarMaskBool (k mask : ℕ) (z : ℤ) : Bool :=
  mask.testBit ((z : ZMod (k+1)).val)



/-- Ordinary-square and d-times-square masks for a single modulus. -/
structure PellSquareMasks where
  k : ℕ
  ordinary : ℕ
  scaled : ℕ
deriving DecidableEq, Repr

def PellSquareMasks.Valid (d : ℤ) (m : PellSquareMasks) : Prop :=
  PellScalarMaskValid 1 m.k m.ordinary ∧ PellScalarMaskValid d m.k m.scaled

instance (d : ℤ) (m : PellSquareMasks) : Decidable (m.Valid d) := by
  unfold PellSquareMasks.Valid
  infer_instance

def pellDefaultMasks : PellSquareMasks := ⟨0,1,1⟩



/-- Out-of-range witness indices use a mask that accepts everything. Thus
an invalid witness cannot make the graph checker accept a false rejection. -/
def pellSelectMasks : List PellSquareMasks → ℕ → PellSquareMasks
  | [], _ => pellDefaultMasks
  | m::_, 0 => m
  | _::ms, n+1 => pellSelectMasks ms n



/-- One witness for each sign of the product.  A positive edge would require
xy+1 to be a square, while an opposite-sign edge requires xy-1=d*r^2. -/
def pellPairChecks (ms : List PellSquareMasks) (x : ℤ) :
    List ℤ → List (ℕ × ℕ) → Bool
  | [], [] => true
  | y::ys, w::ws =>
      let p := pellSelectMasks ms w.1
      let n := pellSelectMasks ms w.2
      ((!pellScalarMaskBool p.k p.ordinary (x*y+1)) &&
        (!pellScalarMaskBool n.k n.scaled (x*y-1))) &&
        pellPairChecks ms x ys ws
  | _, _ => false



/-- The triangular witness array checks every unordered pair of distinct
positions. The empty-list cases enforce exact certificate lengths. -/
def pellMatchingCheck (ms : List PellSquareMasks) :
    List ℤ → List (List (ℕ × ℕ)) → Bool
  | [], [] => true
  | x::xs, ws::wss => pellPairChecks ms x xs ws && pellMatchingCheck ms xs wss
  | _, _ => false



/-- Rational-square criterion in the fixed imaginary quadratic field. -/
def PellIntegerSquare (d n : ℤ) : Prop :=
  (∃ r : ℤ, r*r = n) ∨ (∃ r : ℤ, -d*r*r = n)

/-- Membership preserves both signs, without identifying opposite entries. -/
def PellSignedMember (xs : List ℤ) (z : ℤ) : Prop :=
  ∃ x ∈ xs, z = x ∨ z = -x





/-- Executable graph data together with its kernel certificates. Magnitude
completeness comes separately from the proved continued-fraction prefix. -/
structure PellMatchingCertificate (d : ℤ) where
  magnitudes : List ℤ
  masks : List PellSquareMasks
  witnesses : List (List (ℕ × ℕ))
  masks_valid : ∀ m ∈ masks, m.Valid d
  checked : pellMatchingCheck masks magnitudes witnesses = true
  large : ∀ x ∈ magnitudes, 2 ≤ x

def pellEmptyMatchingCertificate (d : ℤ) : PellMatchingCertificate d where
  magnitudes := []
  masks := []
  witnesses := []
  masks_valid := by simp
  checked := rfl
  large := by simp



end D1Bound5
end


