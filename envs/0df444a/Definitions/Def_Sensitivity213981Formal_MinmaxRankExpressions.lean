-- Prove2me | Definitions.Def_Sensitivity213981Formal_MinmaxRankExpressions
-- name    : Sensitivity213981Formal_MinmaxRankExpressions
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:05:22.263751+00:00
-- url     : https://prove2.me/theorems/02d7e23d-944f-4d30-a776-016cfd7fe46c
-- title:
--   Minmax Rank Expressions — sensitivity certificate definitions
-- statement:
--   The definitions for Minmax Rank Expressions in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundMinmaxRank.rawBExpr`, `ThreeBoundMinmaxRank.rankMTerm`, `ThreeBoundMinmaxRank.rawMExpr`, `ThreeBoundMinmaxRank.Entry`, `ThreeBoundMinmaxRank.accepted`, `ThreeBoundMinmaxRank.capacityHeight`, `ThreeBoundMinmaxRank.need`, `ThreeBoundMinmaxRank.rankBTerm`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MinmaxRankExpressions.lean, lines 1–72.

import Definitions.Def_Sensitivity213981Formal_MinmaxExpressions
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankProfileBounds
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section
/- Exact-rank B/M arithmetic for monotone min/max target curves.
Capacity is encoded as the largest accepted tier plus one; zero means none. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000

namespace ThreeBoundMinmaxRank
open ThreeBoundNumeric ThreeBoundFullProfile ThreeBoundRankProfiles

abbrev Entry := ThreeBoundMinmaxNumeric.Entry

def accepted (e : Entry) (d x y : ℕ) : Bool := e.lowerAt d≤ x ∧ e.upperAt d≤ y

def capacityHeight (e : Entry) (x y : ℕ) : ℕ :=
  (Finset.range (e.tolerance+1)).sup fun d => if accepted e d x y then d+1 else 0

def need (n : ℕ) (e : Entry) (other d : ℕ) : ℕ :=
  if e.lowerAt d≤ other then if e.upperAt d≤ other then e.lowerAt d else e.upperAt d else n

def rankBTerm (n degree : ℕ) (a c : Entry) (x y : ℕ) : Expr n :=
  let hb := capacityHeight c x y
  if hb=0 then 0 else
    let db := hb-1
    let ha := capacityHeight a x y
    let need0 := need n a y db
    let need1 := need n a x db
    if need0≤ x ∧ need1≤ y then
      downRankExpr n need0 x+downRankExpr n need1 y+
        if ha=hb ∧ db≤ degree then (degree-db)*aExpr n c.guard a.guard else 0
    else 0

def rawBExpr (n degree : ℕ) (a c : Entry) : Expr n :=
  Expr.maximum ((List.range n).flatMap fun x => (interval x n).map fun y => rankBTerm n degree a c x y)

def rankMTerm (n degree : ℕ) (a c d : Entry) (x y : ℕ) : Expr n :=
  let hb := capacityHeight c x y
  if hb=0 then 0 else
    let db := hb-1
    let hc := capacityHeight d x y
    if degree< hc then 0 else
      let gap := hc-db
      if d.guard=c.guard ∧ 0< gap then 0 else
        let ha := capacityHeight a x y
        let need0 := need n a y db
        let need1 := need n a x db
        if need0≤ x ∧ need1≤ y then
          let target := downRankExpr n need0 x+downRankExpr n need1 y
          if ha=hb ∧ db≤ degree then
            if degree-db< gap then 0 else
              target+(degree-db-gap)*aExpr n c.guard a.guard+
                gap*min (aExpr n c.guard a.guard) (plusExpr n d.guard c.guard a.guard)
          else target
        else 0

def rawMExpr (n degree : ℕ) (a c d : Entry) : Expr n :=
  Expr.maximum ((List.range n).flatMap fun x => (interval x n).map fun y => rankMTerm n degree a c d x y)





end ThreeBoundMinmaxRank




end
end Sensitivity213981Formal


