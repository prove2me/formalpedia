-- Prove2me | Definitions.Def_ConstrainedCorrelationRepulsion_Main_Supplement_Scan
-- name    : ConstrainedCorrelationRepulsion_Main_Supplement_Scan
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:04:06.445181+00:00
-- url     : https://prove2.me/theorems/54df4015-aae6-454e-98df-6769666165d0
-- title:
--   Direct costed universal-row clique extraction
-- statement:
--   Let $D$ be an edge-deletion bitmap for $G\vee K_t$. The extraction scans every new universal vertex's surviving row, retaining its original vertices and maintaining their count. It keeps the first row with largest count. In a valid cluster graph, a surviving universal row is exactly that universal vertex's cluster restricted to $V(G)$, so this is the source's choice of a cluster meeting the universal clique.
--
--   The scan returns a bitmap, its computed population count and a computed word-operation count. Each old-vertex iteration charges twelve operations for address arithmetic, deletion-bit lookup, testing, bitmap writing, counting and loop control; each row initializes in three operations and its comparison/pointer retention costs eight. The outer scan initializes in three operations and explicitly reads/writes each output bit in three operations. Thus its recorded cost is
--
--   $$3+t(12n+11)+3n.$$
--
--   The bitmap has random-access word memory semantics; it is not charged as a linked list. No claimed complexity, optimum, output-clique certificate or desired bound is supplied as input. The clique property and the universal quadratic bound are obligations of Lemma 7.4. The empty bitmap is the specified fallback when $t=0$, a case excluded by that lemma.
--
--   Differences from the source:
--   - encoding: choose a largest old-vertex intersection among clusters meeting $U$ → scan surviving universal rows with first-maximal tie breaking; reason: these rows are exactly those clusters on valid deletion inputs, and the direct procedure has explicit word costs.
-- source:
--   Yixin Cao, Ying Xu, STOC 2027 submission #869 (October 2026), Lemma 7.4 and proof, printed p.36 (PDF p.37)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Supplement_Graphs

namespace ConstrainedCorrelationRepulsion.Main.Supplement

open Classical

/-- A scan accumulator: a bitmap, its maintained population counter, and the executed word
operations. The counter and work are computed by the scan, not supplied as certificates. -/
structure RowScan (n : ℕ) where
  bitmap : Fin n → Bool
  size : ℕ
  work : ℕ

/-- One row of the surviving adjacency matrix, restricted to old vertices. Since the row
vertex is universal, the surviving bit is exactly the complement of the deletion bit.
Charge address arithmetic, input read, test, bitmap store, increment and loop control.
Bitmap access/update is random-access word memory, not a linked-list implementation. -/
noncomputable def scanRow (n t : ℕ) (D : Finset (Sym2 (Fin (n+t)))) (u : Fin t) : RowScan n :=
  (List.finRange n).foldl (fun a v =>
    let old : Fin (n+t) := ⟨v.val, by omega⟩
    let new : Fin (n+t) := ⟨n+u.val, by omega⟩
    let keep := decide (s(old,new) ∉ D)
    {bitmap := Function.update a.bitmap v keep,
     size := a.size + if keep then 1 else 0,
     work := a.work + 12})
    {bitmap := fun _ => false, size := 0, work := 3}

/-- Scan all universal rows, keeping the first row of maximum old-vertex population.
The row pointer is retained in constant time; rows occupy fresh n-word storage.
On a valid deletion set, a closed-neighborhood row is already a whole component, so no
repeated twin moves or general connectivity search is needed. -/
noncomputable def gatherScan (n t : ℕ) (D : Finset (Sym2 (Fin (n+t)))) : RowScan n :=
  let best : RowScan n := (List.finRange t).foldl (fun a u =>
    let row := scanRow n t D u
    {bitmap := if a.size < row.size then row.bitmap else a.bitmap,
     size := max a.size row.size,
     work := a.work + row.work + 8})
    {bitmap := fun _ => false, size := 0, work := 3}
  /- Read and write the output bitmap explicitly. -/
  (List.finRange n).foldl (fun a v =>
    {bitmap := Function.update a.bitmap v (best.bitmap v),
     size := best.size, work := a.work + 3})
    {bitmap := fun _ => false, size := best.size, work := best.work}

/-- Mathematical decoding of the output bitmap (not a further optimization procedure). -/
noncomputable def extractedClique (n t : ℕ) (D : Finset (Sym2 (Fin (n+t)))) :
    Finset (Fin n) :=
  Finset.univ.filter (fun v => (gatherScan n t D).bitmap v = true)

end ConstrainedCorrelationRepulsion.Main.Supplement


