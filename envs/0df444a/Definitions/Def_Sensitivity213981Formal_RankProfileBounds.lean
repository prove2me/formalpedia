-- Prove2me | Definitions.Def_Sensitivity213981Formal_RankProfileBounds
-- name    : Sensitivity213981Formal_RankProfileBounds
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T18:36:35.061157+00:00
-- url     : https://prove2.me/theorems/292e4f42-9c85-4bc6-91ea-97c8d09b6073
-- title:
--   Rank Profile Bounds — sensitivity certificate definitions
-- statement:
--   The definitions for Rank Profile Bounds in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundRankProfiles.downRankExpr`, `ThreeBoundRankProfiles.jointRankExpr`, `ThreeBoundRankProfiles.RankState`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RankProfileBounds.lean, lines 1–107.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_Sensitivity213981Formal_Supplement_MinmaxLocal
import Definitions.Def_Sensitivity213981Formal_Supplement_NumericExpressions
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
/- Exact child-rank bounds, derived from the actual nested Boolean family.
These are the local profile inequalities used by the min/max rank oracle. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

namespace ThreeBoundRankProfiles
open OAI.Paper320 ThreeBoundProfiles ThreeBoundFullProfile ThreeBoundNumeric
open scoped Classical
noncomputable section
variable {n : ℕ} {I : Type} [Fintype I]

def RankState (F : Fin n → (I → Bool) → Bool) (x : I → Bool) (r : Fin n) : Prop :=
  ∀ i : Fin n, F i x = true ↔ i ≤  r









def downRankExpr (n g r : ℕ) : Expr n :=
  if r+1 <  n then mExpr n g r else bExpr n g r







def jointRankExpr (n g r k : ℕ) : Expr n :=
  min (dExpr n g r k) (pExpr n r k + downRankExpr n g r)





end
end ThreeBoundRankProfiles





end
end Sensitivity213981Formal


