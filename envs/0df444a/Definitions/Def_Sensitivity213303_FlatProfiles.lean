-- Prove2me | Definitions.Def_Sensitivity213303_FlatProfiles
-- name    : Sensitivity213303_FlatProfiles
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T21:59:59.050187+00:00
-- url     : https://prove2.me/theorems/e86225a3-ea17-4bbf-b59a-b5b515d9db97
-- title:
--   A flattened coordinate layout and binary lookup tables for profiles
-- statement:
--   Valid A/B/M/P/D coordinates are assigned explicit natural-number offsets by flatIndex. A NatTable is a binary tree whose internal nodes route an index by a cut value and whose leaves hold constant natural values. profileOfTable interprets such a tree as a sensitivity profile by looking up each coordinate’s offset. This separates the semantic coordinate names from the compact representation used by finite arithmetic certificates.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module FlatProfiles; source SHA256 276bf0aa1b00665f06233efe8838114a174b78aa763035615b6412c63cde2a61.

/- Compressed numerical profile layout and a complete coordinate checker.
The interpretation is always the named semantic A/B/M/P/D coordinate. -/
import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_NumericExpressions
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring
namespace ThreeBoundFullProfile
end ThreeBoundFullProfile
namespace ThreeBoundProfiles
end ThreeBoundProfiles


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThreeBoundNumeric
open ThreeBoundProfiles ThreeBoundFullProfile

def valid {n : ℕ} : Coord n → Prop
  | .a i j | .b i j => i ≤ j
  | .m i j => i ≤ j ∧ j.val+1<n
  | .p j l => j<l
  | .d i j l => i≤j ∧ j<l

instance {n : ℕ} (c : Coord n) : Decidable (valid c) := by cases c <;> unfold valid <;> infer_instance









def aIndex (n i j : ℕ) : ℕ := i*(2*n+1-i)/2+(j-i)
def bIndex (n i j : ℕ) : ℕ := n*(n+1)/2+aIndex n i j
def mIndex (n i j : ℕ) : ℕ := n*(n+1)+j*(j+1)/2+i
def pIndex (n j l : ℕ) : ℕ := n*(n+1)+n*(n-1)/2+j*(2*n-1-j)/2+(l-j-1)
def dIndex (n i j l : ℕ) : ℕ :=
  2*n*n+((List.range j).map fun k=>(k+1)*(n-k-1)).sum+i*(n-j-1)+(l-j-1)

def flatIndex {n : ℕ} : Coord n → ℕ
  | .a i j => aIndex n i.val j.val
  | .b i j => bIndex n i.val j.val
  | .m i j => mIndex n i.val j.val
  | .p j l => pIndex n j.val l.val
  | .d i j l => dIndex n i.val j.val l.val



/-- A balanced lookup tree gives logarithmic kernel reduction for certificates. -/
inductive NatTable where
  | leaf : ℕ → NatTable
  | branch : ℕ → NatTable → NatTable → NatTable

def NatTable.get : NatTable → ℕ → ℕ
  | .leaf v, _ => v
  | .branch cut left right, i => if i < cut then left.get i else right.get i

def profileOfTable (n : ℕ) (v : NatTable) : Profile n := fun c=>v.get (flatIndex c)











end ThreeBoundNumeric


