-- Prove2me | Definitions.Def_Sensitivity213981Formal_ClosureCertificate
-- name    : Sensitivity213981Formal_ClosureCertificate
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T20:42:41.031302+00:00
-- url     : https://prove2.me/theorems/218905c3-2068-42bc-939c-ad73342ba4b6
-- title:
--   Closure Certificate — sensitivity certificate definitions
-- statement:
--   The definitions for Closure Certificate in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundNumeric.ClosureCertificate.source₁`, `ThreeBoundNumeric.ClosureCertificate.combine`, `ThreeBoundNumeric.ClosureCertificate.Reason`, `ThreeBoundNumeric.ClosureCertificate.Node`, `ThreeBoundNumeric.ClosureCertificate.Table`, `ThreeBoundNumeric.ClosureCertificate.Table.get`, `ThreeBoundNumeric.ClosureCertificate.PointerTable`, `ThreeBoundNumeric.ClosureCertificate.PointerTable.get`, `ThreeBoundNumeric.ClosureCertificate.checkNode`, `ThreeBoundNumeric.ClosureCertificate.checkNodes`, `ThreeBoundNumeric.ClosureCertificate.source₀`, `ThreeBoundNumeric.ClosureCertificate.checkInterval`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ClosureCertificate.lean, lines 1–252.

import Definitions.Def_Sensitivity213981Formal_ClosureHomogeneity
import Definitions.Def_Sensitivity213981Formal_FlatProfiles
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section
/- A small trusted checker for exact closure certificates.

Each node cites either an input bound or one of the already proved semantic
closure rules, with references strictly earlier in the finite program. The
checker validates coordinates and integer inequalities. A successful check
therefore proves a semantic upper profile for every natural scaling of the
input. No executable output is used as an unverified premise. -/


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
  | .branch cut left right, i => if i< cut then left.get i else right.get i

inductive PointerTable where
  | identity
  | fixed : ℕ → PointerTable
  | branch : ℕ → PointerTable → PointerTable → PointerTable

def PointerTable.get : PointerTable → ℕ → ℕ
  | .identity, i => i
  | .fixed v, _ => v
  | .branch cut left right, i => if i< cut then left.get i else right.get i

def checkNode (input : Profile n) (nodes : ℕ → Node n) (k : ℕ) : Bool :=
  let node := nodes k
  match node.reason with
  | .input => input node.coord ≤  node.value
  | .step r a b =>
      node.coord = r.target ∧ a< k ∧ b< k ∧
      (nodes a).coord = source₀ r ∧ (nodes b).coord = source₁ r ∧
      combine r (nodes a).value (nodes b).value ≤  node.value

def checkNodes (input : Profile n) (nodes : ℕ → Node n) (count : ℕ) : Bool :=
  (List.range count).all (checkNode input nodes)





def checkInterval (p : ℕ → Bool) (a b : ℕ) : Bool :=
  (interval a b).all p









def checkOutput (nodes : ℕ → Node n) (count : ℕ)
    (outIndex : Coord n → ℕ) (output : Profile n) : Bool :=
  (validCoords n).all fun coord =>
    let k := outIndex coord
    k< count ∧ (nodes k).coord=coord ∧ (nodes k).value≤ output coord



end ThreeBoundNumeric.ClosureCertificate



end
end Sensitivity213981Formal


