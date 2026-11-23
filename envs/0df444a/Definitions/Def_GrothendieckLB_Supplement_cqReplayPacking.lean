-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_cqReplayPacking
-- name    : GrothendieckLB_Supplement_cqReplayPacking
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T19:32:45.292209+00:00
-- url     : https://prove2.me/theorems/30a7b1e2-48e1-43c7-873a-a6c107ecaa1e
-- title:
--   Paged integer encoding for Hermite coefficient witnesses
-- statement:
--   Signed endpoints are stored using a common bit width within each table, with direct-address pages of 32 machine-independent natural numerals. The projections recover individual interval endpoints used by the recurrence checks.
-- source:
--   Independent integer replay of the cubic–quintic Hermite coefficient calculation in Saha et al., arXiv:2608.11158v2, (13) and Appendix C.1.

import Definitions.Def_GrothendieckLB_Supplement_cqNonlinearHeadCheck
import Mathlib.Tactic.Eval

open GrothendieckLB.Supplement.CQHeadArithmetic
namespace GrothendieckLB.Supplement.CQHeadCertificate

def encode (x : ℤ) : ℕ := if x < 0 then 2*x.natAbs-1 else 2*x.natAbs

def decode (n : ℕ) : ℤ := if n%2=0 then (n/2:ℕ) else -((n/2+1:ℕ):ℤ)

def numeral (width : ℕ) (field : ℕ → ℤ) (n : ℕ) : ℕ :=
  (List.range n).foldr (fun i acc => encode (field i)+(acc <<< width)) 0

def vfield (x : MomentCombination) (k : ℕ) : ℤ :=
  match k with | 0 => x.e0.lo | 1 => x.e0.hi | 2 => x.e2.lo | 3 => x.e2.hi | 4 => x.e4.lo | _ => x.e4.hi

/-- Integer data in two-level pages. Each field occupies at most one large numeral when its own precision exceeds the page packing threshold. -/
structure Packed where
  width : ℕ
  pages : Array (Array ℕ)
  deriving Lean.ToExpr, Inhabited, DecidableEq

def fieldsInBlock (w stride batch : ℕ) := max 1 (min (stride*batch) (4096/w))

def packed (n stride batch : ℕ) (f : ℕ → ℕ → ℤ) : Packed :=
  let w := (List.range n).foldl (fun mx i => (List.range stride).foldl
    (fun m k => max m (encode (f i k)).log2) mx) 0 + 1
  let k := fieldsInBlock w stride batch
  let len := (n*stride+k-1)/k
  let block (a : ℕ) := if k=1 then encode (f (a/stride) (a%stride)) else
    numeral w (fun j => let i := a*k+j; f (i/stride) (i%stride)) k
  ⟨w,tab ((len+31)/32) fun p => tab (min 32 (len-32*p)) fun j => block (32*p+j)⟩

def getN (p : Packed) (stride batch n k : ℕ) : ℤ :=
  let f := fieldsInBlock p.width stride batch
  let i := n*stride+k
  let a := i/f
  let v := entry 0 (entry #[] p.pages (a/32)) (a%32)
  if f=1 then decode v else decode ((v >>> (p.width*(i%f))) % (2^p.width))

def packA (par : ℕ) (xs : Array MomentCombination) : Packed :=
  packed ((xs.size+1-par)/2) 6 8 fun i k => vfield (entry zeroCombination xs (2*i+par)) k

def getA (p : Packed) (par i : ℕ) : MomentCombination :=
  if i%2=par then
    let f := getN p 6 8 (i/2)
    ⟨⟨f 0,f 1⟩,⟨f 2,f 3⟩,⟨f 4,f 5⟩⟩
  else zeroCombination

def packB (par : ℕ) (xs : Array Interval) : Packed :=
  packed ((xs.size+1-par)/2) 2 16 fun i k =>
    let x := entry zeroInterval xs (2*i+par)
    if k=0 then x.lo else x.hi

def getB (p : Packed) (par i : ℕ) : Interval :=
  if i%2=par then ⟨getN p 2 16 (i/2) 0,getN p 2 16 (i/2) 1⟩ else zeroInterval

end GrothendieckLB.Supplement.CQHeadCertificate


