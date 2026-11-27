-- Prove2me | Definitions.Def_SingleExpBisect_Main_ChargedChildConvolution
-- name    : SingleExpBisect_Main_ChargedChildConvolution
-- status  : Definition
-- author  : @Soh Kumabe
-- created : 2026-11-27T02:38:32.308551+00:00
-- url     : https://prove2.me/theorems/9ae2dbfb-56cb-4a5e-8eb4-949f540e317d
-- title:
--   Sparse child convolution with explicit arithmetic and table-probe counts
-- statement:
--   For a bag assignment and a list of child tables, select matching signatures, add signed exponent offsets and convolve with duplicate-key accumulation. Return the requested rational coefficient and the number of charged probes and arithmetic operations.
-- source:
--   Kumabe, Single-Exponential Algorithm for Minimum Bisection, STOC project #803, Section 3, Lemmas 3.1 and 3.4–3.6.

import Mathlib
import Definitions.Def_SingleExpBisect_Main_Encodings
import Definitions.Def_SingleExpBisect_Main_Graphs
set_option autoImplicit false

namespace SingleExpBisect.Convolution
open SingleExpBisect.Main MinBisectFPT

abbrev Entry (n : ℕ) := (Var n →₀ ℕ) × ℚ

structure Degrees where
  x : ℤ
  aux : ℤ
  w : ℤ
  deriving DecidableEq, Repr

def degreesAdd (a b : Degrees) : Degrees := ⟨a.x+b.x,a.aux+b.aux,a.w+b.w⟩

def wDegree (c : ℤ) : Degrees := ⟨0,0,c⟩

abbrev CoeffEntry := Degrees × ℚ

abbrev SparseChild (n : ℕ) := Finset (Fin n) × ℤ × List (Entry n)

def selectDegrees {n : ℕ} (P : Finset (Fin n)) (L : List (Entry n)) : List CoeffEntry :=
  L.filterMap fun (e,c) =>
    if ∀ v : Fin n, e (.y v) = if v ∈ P then 1 else 0 then
      some (⟨(e .x:ℤ),(e .x':ℤ),(e .w:ℤ)⟩,c)
    else none

def multiplyDegrees (A B : List CoeffEntry) : List CoeffEntry :=
  A.flatMap fun a => B.map fun b => (degreesAdd a.1 b.1,a.2*b.2)

end SingleExpBisect.Convolution

namespace SingleExpBisect.Sparse
variable {K : Type} [DecidableEq K]

abbrev Table (K : Type) := List (K × ℚ)

def insertEntry (q : K × ℚ) : Table K → Table K × ℕ
  | [] => ([q],1)
  | p::s => if q.1=p.1 then ((p.1,p.2+q.2)::s,1) else
      let (t,n) := insertEntry q s
      (p::t,n+1)

def absorb (input : Table K) (acc : Table K × ℕ) : Table K × ℕ :=
  input.foldl (fun v q => let z := insertEntry q v.1; (z.1,v.2+3+z.2)) acc

end SingleExpBisect.Sparse

namespace SingleExpBisect.Sparse
variable {K : Type} [DecidableEq K] (add : K → K → K)

def products (x y : Table K) : Table K := x.flatMap fun a => y.map (fun b => (add a.1 b.1,a.2*b.2))

def multiply (x y : Table K) := absorb (products add x y) ([],x.length+1)

def layers (x : Table K) : List (Table K) → Table K × ℕ
  | [] => (x,0)
  | y::ys => let z := multiply add x y
             let out := layers z.1 ys
             (out.1,z.2+out.2)

end SingleExpBisect.Sparse

namespace SingleExpBisect.Convolution
open SingleExpBisect.Main MinBisectFPT SingleExpBisect.Sparse

abbrev ShiftFactor := ℤ × Table Degrees

def shifted {n : ℕ} (s : SparseChild n) : ShiftFactor :=
  (-s.2.1,multiplyDegrees [(wDegree (-s.2.1),1)] (selectDegrees s.1 s.2.2))

def testDigits {n : ℕ} (P : Finset (Fin n)) (e : Var n →₀ ℕ) : List (Fin n) → Bool × ℕ
  | [] => (true,1)
  | v::vs => if e (.y v) = (if v∈P then 1 else 0) then
             let t := testDigits P e vs
             (t.1,t.2+1)
             else (false,1)

def project {n : ℕ} (P : Finset (Fin n)) (off : ℤ) : List (Entry n) → Table Degrees × ℕ
  | [] => ([],1)
  | (e,c)::xs =>
    let b := testDigits P e (List.finRange n)
    let a := project P off xs
    (if b.1 then (⟨e .x,e .x', off + e .w⟩,c)::a.1 else a.1, a.2+b.2+2)

def prepare {n : ℕ} : List (SparseChild n) → List ShiftFactor × ℕ
  | [] => ([],1)
  | (P,c,L)::xs => let z := project P (-c) L
                     let t := prepare xs
                     ((-c,z.1)::t.1,z.2+t.2+1)

def query (q : Degrees) : Table Degrees → ℚ × ℕ
  | [] => (0,1)
  | (a,c)::t => if a=q then (c,1) else let z := query q t; (z.1,z.2+1)

def fast {n : ℕ} (k : ℕ) (base : ℤ) (cs : List (SparseChild n)) (q : Degrees) : ℚ × ℕ :=
  let f := prepare cs
  let z := layers degreesAdd [(wDegree base,1)] (f.1.map Prod.snd)
  let a := if q.w ≤ (k:ℤ) then query q z.1 else (0,1)
  (a.1, f.2+z.2+a.2+1)

noncomputable def records {n : ℕ} (G : SimpleGraph (Fin n)) (T : RootedTD n) (t : Fin T.N)
    (R : Finset (Fin n)) (Lc : Fin T.N → List (Entry n)) : List (SparseChild n) :=
  (T.children t).toList.map (fun s => (R∩T.adhesion s,(etaNode G T s (R∩T.adhesion s):ℤ),Lc s))

end SingleExpBisect.Convolution


