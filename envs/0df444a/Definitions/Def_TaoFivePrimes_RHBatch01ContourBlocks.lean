-- Prove2me | Definitions.Def_TaoFivePrimes_RHBatch01ContourBlocks
-- name    : TaoFivePrimes_RHBatch01ContourBlocks
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T18:01:47.938668+00:00
-- url     : https://prove2.me/theorems/ee15439c-3ac2-421f-9e2a-05f79ccab70b
-- title:
--   Compositional interface for finite guarded contour blocks
-- statement:
--   A block consists of a list of the existing arithmetic-guarded cell records, its necessary length proof, correct global edge/index enumeration and exact oriented logarithm numerator sum. The append constructor proves these structural fields by list concatenation. Contains no certificate data and asserts no block exists; no analytic, winding, zero-count or RH conclusion.
-- source:
--   Existing Platt Fourier contour certificates DOI10.1090/mcom/3198. Attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHBatch01ContourArithmeticV2
set_option autoImplicit false
namespace RHBatch01ContourBlocks
noncomputable def coordinates (p : RHBatch01ContourArithmeticV2.Record×Nat) : Bool :=
 decide (p.1.edge=(if p.2<4096 then 0 else if p.2<4224 then 1 else if p.2<8320 then 2 else 3) ∧
  p.1.index=(if p.2<4096 then p.2 else if p.2<4224 then p.2-4096 else if p.2<8320 then p.2-4224 else p.2-8320))
noncomputable def signedTotal (rs : List RHBatch01ContourArithmeticV2.Record) : Int :=
 (rs.map (fun r=>if r.edge<2 then r.log128.2 else -r.log128.2)).sum
structure Block (start count : Nat) (total : Int) where
 records : List RHBatch01ContourArithmeticV2.Record
 length_eq : records.length=count
 coordinates_eq : (records.zipIdx start).all coordinates=true
 total_eq : signedTotal records=total
noncomputable def append {start n m : Nat} {A B : Int}
 (a : Block start n A) (b : Block (start+n) m B) : Block start (n+m) (A+B) where
 records := a.records++b.records
 length_eq := by simp only[List.length_append,a.length_eq,b.length_eq]
 coordinates_eq := by
  rw[List.zipIdx_append,List.all_append,a.coordinates_eq]
  simpa only[a.length_eq,Bool.true_and] using b.coordinates_eq
 total_eq := by
  simp only[signedTotal,List.map_append,List.sum_append]
  exact congrArg₂ (fun x y:Int=>x+y) a.total_eq b.total_eq
end RHBatch01ContourBlocks
noncomputable def TaoFivePrimes_RHBatch01ContourBlocks : Nat := 8448


