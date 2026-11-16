-- Prove2me | Definitions.Def_UnaryParityLifting_Exact_Supplement_sinkDAG
-- name    : UnaryParityLifting_Exact_Supplement_sinkDAG
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:45:10.194813+00:00
-- url     : https://prove2.me/theorems/f620b37b-f732-4c3f-8d3b-671b4ead582f
-- title:
--   The binary Sink-of-DAG CNF and lifted length
-- statement:
--   Let h=n². There are h² successor pointers, each with b=ceil(log₂(h+1)) bits, null code 0 and target names 1,…,h. The formula contains range clauses excluding each unused code, the disjunction making the distinguished (1,1) pointer nonnull, unit clauses making every last-row pointer null, and, for each internal pointer and k∈[h], the implication that pointer value k forces the next-row target pointer to be nonnull. These are actual clauses over the bit variables.
--
--   $$N(n)=h^2\lceil\log_2(h+1)\rceil,\qquad L_n=|\mathrm{SoD}_{n^2}\circ g|.$$
--
--   The grid bits are renamed bijectively to Fin N for the unchanged published lift. The lifted length is the fixed binary CNF length, including variable names, rather than a variable or clause count. The intended family has n≥1; n=0 is defined as an empty grid and excluded from the assertions.
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), canonical source.pdf SHA256 088f9b64d3926dd700996884111b97c94806141880e07004f529211a40c0619b; citation_basis: published (submission artifact, no acceptance claim), pp.16–17, §5.1.1; p.18, §5.2; p.19, equation (6.1)

import Definitions.Def_UnaryParityLifting_Exact_Supplement_encoding
import Definitions.Def_LiftSAParity_lift

noncomputable section
open Classical
open scoped BigOperators

namespace UnaryParityLifting.Exact.Supplement

def gridSide (n : ℕ) : ℕ := n ^ 2
def pointerBits (h : ℕ) : ℕ := Nat.clog 2 (h + 1)
abbrev GridBit (h : ℕ) := Fin h × Fin h × Fin (pointerBits h)
/-- Actual variable count: h² ceil(log₂(h+1)), h=n². -/
def baseVariables (n : ℕ) : ℕ := Fintype.card (GridBit (gridSide n))
/-- Clause excluding one pointer value (little-endian binary). -/
def forbidPointer (h : ℕ) (r c : Fin h) (k : ℕ) : LiftSAParity.Clause (GridBit h) :=
  Finset.univ.image (fun j : Fin (pointerBits h) => ((r,c,j), !Nat.testBit k j.val))
def activePointer (h : ℕ) (r c : Fin h) : LiftSAParity.Clause (GridBit h) :=
  Finset.univ.image (fun j : Fin (pointerBits h) => ((r,c,j), true))
/-- Range clauses, active source, null last row, and active successors. -/
def gridCNF (h : ℕ) : LiftSAParity.CNF (GridBit h) :=
  (Finset.univ.biUnion fun r : Fin h => Finset.univ.biUnion fun c : Fin h =>
    ((Finset.range (2 ^ pointerBits h)).filter (fun k => h < k)).image (forbidPointer h r c)) ∪
  ((Finset.univ.filter (fun r : Fin h => r.val = 0)).biUnion fun r =>
    (Finset.univ.filter (fun c : Fin h => c.val = 0)).image (activePointer h r)) ∪
  ((Finset.univ.filter (fun r : Fin h => r.val + 1 = h)).biUnion fun r =>
    Finset.univ.biUnion fun c : Fin h =>
      Finset.univ.image (fun j : Fin (pointerBits h) => ({((r,c,j), false)} : LiftSAParity.Clause (GridBit h)))) ∪
  (Finset.univ.biUnion fun r : Fin h => Finset.univ.biUnion fun s : Fin h =>
    if s.val = r.val + 1 then
      Finset.univ.biUnion fun c : Fin h =>
        Finset.univ.image (fun k : Fin h => forbidPointer h r c (k.val + 1) ∪ activePointer h s k)
    else ∅)
/-- Rename the concrete bit grid to Fin N for the immutable lift interface. -/
def sinkDAG (n : ℕ) : LiftSAParity.CNF (Fin (baseVariables n)) :=
  (gridCNF (gridSide n)).image (fun C =>
    C.image (fun l => ((Fintype.equivFin (GridBit (gridSide n))) l.1, l.2)))
def liftedSink {m : ℕ} (g : (Fin m → Bool) → Bool) (n : ℕ) :=
  LiftSAParity.lift (sinkDAG n) g
def liftedLength {m : ℕ} (g : (Fin m → Bool) → Bool) (n : ℕ) : ℕ :=
  cnfBits (liftedSink g n)

end UnaryParityLifting.Exact.Supplement


