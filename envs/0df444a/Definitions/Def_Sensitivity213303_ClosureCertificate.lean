-- Prove2me | Definitions.Def_Sensitivity213303_ClosureCertificate
-- name    : Sensitivity213303_ClosureCertificate
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:02:51.563622+00:00
-- url     : https://prove2.me/theorems/065be76e-0b3a-4c1a-830d-0e64206b8c98
-- title:
--   A proof-carrying instruction graph for profile closure
-- statement:
--   A closure certificate consists of nodes carrying a profile coordinate, a natural value and a reason: an input value or a permitted closure rule applied to earlier nodes. Binary tables locate nodes and output pointers. The checks verify each node’s rule, numerical inequality and dependency positions, and verify which node supplies each output coordinate. The instruction combiner uses addition for a union bound, maximum for a partition bound, and the selected source value for a one-source rule. Soundness converts a checked graph into an upper profile.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module ClosureCertificate; source SHA256 bc6b5758158196e25c384f9b6d527a2e020b577675a25c6d2a48edc187cf4af5.

/- A small trusted checker for exact closure certificates.

Each node cites either an input bound or one of the already proved semantic
closure rules, with references strictly earlier in the finite program. The
checker validates coordinates and integer inequalities. A successful check
therefore proves a semantic upper profile for every natural scaling of the
input. No executable output is used as an unverified premise. -/
import Definitions.Def_Sensitivity213303_ClosureHomogeneity
import Definitions.Def_Sensitivity213303_FlatProfiles
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
set_option maxHeartbeats 3000000

namespace ThreeBoundNumeric.ClosureCertificate
open ThreeBoundProfiles ThreeBoundFullProfile

variable {n : ℕ}

def source₀ : Rule n → Coord n
  | .aCond i j _ => .a (next i) j
  | .aTarget i j _ => .a i (prev j)
  | .bTarget i j _ => .b (next i) j
  | .bCond i j _ => .b i (prev j)
  | .mFromB i j _ _ => .b i j
  | .mTarget i j _ _ => .m (next i) j
  | .pFromA j l _ => .a (next j) l
  | .pTarget j l _ => .p j (prev l)
  | .dFromMP i j l _ _ => .m i j
  | .dDown i j l _ _ => .d (next i) j l
  | .dUp i j l _ _ => .d i j (prev l)
  | .bPartition i j _ _ => .b i (next j)
  | .aPartition j l _ => .a j l

def source₁ (r : Rule n) : Coord n :=
  match r with
  | .dFromMP _ j l _ _ => .p j l
  | .bPartition i j _ _ => .m i j
  | .aPartition j l _ => .p j l
  | _ => source₀ r

def combine : Rule n → ℕ → ℕ → ℕ
  | .dFromMP .., x, y => x+y
  | .bPartition .., x, y => max x y
  | .aPartition .., x, y => max x y
  | _, x, _ => x





inductive Reason (n : ℕ) where
  | input
  | step : Rule n → ℕ → ℕ → Reason n

structure Node (n : ℕ) where
  coord : Coord n
  value : ℕ
  reason : Reason n

inductive Table (α : Type) where
  | leaf : α → Table α
  | branch : ℕ → Table α → Table α → Table α

def Table.get {α : Type} : Table α → ℕ → α
  | .leaf v, _ => v
  | .branch cut left right, i => if i<cut then left.get i else right.get i

inductive PointerTable where
  | identity
  | fixed : ℕ → PointerTable
  | branch : ℕ → PointerTable → PointerTable → PointerTable

def PointerTable.get : PointerTable → ℕ → ℕ
  | .identity, i => i
  | .fixed v, _ => v
  | .branch cut left right, i => if i<cut then left.get i else right.get i

def checkNode (input : Profile n) (nodes : ℕ → Node n) (k : ℕ) : Bool :=
  let node := nodes k
  match node.reason with
  | .input => input node.coord ≤ node.value
  | .step r a b =>
      node.coord = r.target ∧ a<k ∧ b<k ∧
      (nodes a).coord = source₀ r ∧ (nodes b).coord = source₁ r ∧
      combine r (nodes a).value (nodes b).value ≤ node.value







def checkInterval (p : ℕ → Bool) (a b : ℕ) : Bool :=
  (interval a b).all p





def checkOutputAt (nodes : ℕ → Node n) (count : ℕ)
    (outIndex : Coord n → ℕ) (output : Profile n) (coord : Coord n) : Bool :=
  let k := outIndex coord
  k<count ∧ (nodes k).coord=coord ∧ (nodes k).value≤output coord







end ThreeBoundNumeric.ClosureCertificate


