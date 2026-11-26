-- Prove2me | Definitions.Def_NisanRonen_Rounding_checkedColumns
-- name    : NisanRonen_Rounding_checkedColumns
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-26T05:53:15.248834+00:00
-- url     : https://prove2.me/theorems/2ccfda7f-3aac-485e-9214-a30c3fde7041
-- title:
--   Binary input and output representations for the bounded scheduling dynamic program
-- statement:
--   A checked column stores its processing times in machine order if each time is within the fixed cap. A column that exceeds the cap is represented by a missing value. The scheduler rejects a list with a missing column and otherwise decodes the columns and runs the bounded dynamic program. A machine index is encoded in unary, and the sequence of assignments uses the standard framed list encoding.
-- source:
--   Nisan and Ronen (2001), Algorithmic Mechanism Design, §5.6, p. 192, https://doi.org/10.1006/game.1999.0790. Auxiliary representations for the TM2 implementation of the exact rounded-instance solver.

import Definitions.Def_NisanRonen_Rounding_boundedLoadDP
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Bits
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Option
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Unary

namespace NisanRonen.Rounding

open Turing.MultiTapeTM

/-- Unary encoding for a machine index. -/
def encAgent (n : ℕ) : Fin n ↪ List Bool :=
  ⟨fun i => encUnary i.val, fun _ _ h => Fin.ext (encUnary.injective h)⟩

/-- A binary encoding of a list of bounded-column checks. Each successful check stores its
column as a list of naturals. Each failed check records an empty option. -/
def encCheckedColumns : List (Option (List ℕ)) ↪ List Bool :=
  encList (encOption (encList encNat))

/-- Check the cap and serialize the values of one column in machine order. -/
def checkColumn {n : ℕ} (cap : ℕ) (column : Fin n → ℕ) : Option (List ℕ) :=
  if ∀ i, column i ≤ cap then some (List.ofFn column) else none

/-- The dynamic program on a list of column checks. Missing columns cause immediate rejection. -/
def solveCheckedColumns (n cap : ℕ) (columns : List (Option (List ℕ))) : List (Fin n) :=
  if columns.all Option.isSome then
    boundedLoadDP cap (columns.map fun col i => (((col.getD [])[i.val]?).getD 0))
  else
    []

end NisanRonen.Rounding


