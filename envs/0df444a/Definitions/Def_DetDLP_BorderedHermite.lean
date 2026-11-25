-- Prove2me | Definitions.Def_DetDLP_BorderedHermite
-- name    : DetDLP_BorderedHermite
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T11:38:23.069804+00:00
-- url     : https://prove2.me/theorems/9dc7a3e1-7df3-49f6-a97b-cc38bcc2301b
-- title:
--   Bounded column elimination for a lattice containing a modular grid
-- statement:
--   Given $m>0$ and integer columns in $n$ rows, the procedure adjoins the reserved grid columns $me_i$ and performs integer column elimination in row order. The pivot in each row is computed by extended Euclidean column operations. Residues of earlier columns are reduced by the pivot, and tail entries are reduced modulo $m$ using the as-yet unused grid columns. Applied to columns $(a^Tb_j,b_j)$, the bordered form supplies the pivot and trailing basis used to encode a modular coset update.
-- source:
--   DetDLP mission, Lemma 4.4, Section 4.3. Explicit executable refinement of the bordered lattice update.

import Mathlib
import Definitions.Def_DetDLP_FilterAndCoset

namespace DetDLP.BorderedHermite

abbrev Column (n : ℕ) := Vector ℤ n

/-- Reserved columns m*e_i for i beyond the current row allow these reductions. -/
def trim {n : ℕ} (m : ℤ) (j i : Fin n) (x : ℤ) : ℤ :=
  if j < i then x % m else x

def pivotPair {n : ℕ} (m : ℤ) (j : Fin n) (v w : Column n) :
    Column n × Column n :=
  let p := (v.get j)
  let t := (w.get j)
  if t = 0 then (v,w)
  else
    let g : ℤ := p.gcd t
    let a := p.gcdA t
    let b := p.gcdB t
    (Vector.ofFn fun i => trim m j i (a*(v.get i)+b*(w.get i)),
     Vector.ofFn fun i => trim m j i (-(t/g)*(v.get i)+(p/g)*(w.get i)))

@[simp] theorem get_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  change (Vector.ofFn f)[i.val] = f i
  simp

def pairStep {n : ℕ} (m : ℤ) (j : Fin n)
    (state : Column n × Array (Column n)) (w : Column n) : Column n × Array (Column n) :=
  let (p,c) := pivotPair m j state.1 w
  (p,state.2.push c)

def reduceFixed {n : ℕ} (m : ℤ) (j : Fin n) (pivot c : Column n) : Column n :=
  let q := c.get j / pivot.get j
  Vector.ofFn fun i => trim m j i (c.get i - q*pivot.get i)

def pivotStage {n : ℕ} (m : ℤ) (j : Fin n)
    (state : Array (Column n) × Array (Column n)) : Array (Column n) × Array (Column n) :=
  let initial : Column n := Vector.ofFn fun i => if i = j then m else 0
  let (pivot,tail) := state.2.toList.foldl (pairStep m j) (initial,#[])
  let fixed := state.1.map (reduceFixed m j pivot)
  (fixed.push pivot,tail)

def runRows {n : ℕ} (m : ℤ) (cols : Array (Column n)) : ℕ → Array (Column n) × Array (Column n)
  | 0 => (#[],cols.map fun c => c.map (· % m))
  | k+1 =>
    let st := runRows m cols k
    if h : k < n then pivotStage m ⟨k,h⟩ st else st

/-- For an input column lattice containing mℤⁿ, perform bounded column elimination.
    The columns of mI are supplied one at a time by pivotStage. -/
def normalForm {n : ℕ} (m : ℤ) (cols : Array (Column n)) : Array (Column n) :=
  (runRows m cols n).1

/-- Compute the bordered form, extract its trailing block, and translate the old representative.
    Input and output matrices are column arrays. -/
def update {n : ℕ} (m : ℕ) (x : Vector ℕ n) (B : Vector (Column n) n)
    (a : Vector ℕ n) (c : ℕ) : Vector ℕ n × Vector (Column n) n :=
  let dot (v : Column n) := (List.finRange n).foldl (fun s i => s+((a.get i):ℤ)*(v.get i)) 0
  let bordered : Array (Column (n+1)) := B.toArray.map fun col =>
    Vector.ofFn (Fin.cases (dot col) (fun i => (col.get i)))
  let cols := normalForm (m:ℤ) bordered
  let zeroCol : Column (n+1) := Vector.replicate _ 0
  let pivot := cols[0]?.getD zeroCol
  let r := ((c:ℤ)-dot (x.map Int.ofNat)) % (m:ℤ)
  let quotient := r / pivot[0]
  (Vector.ofFn fun i => ((((x.get i):ℤ)+quotient*(pivot.get i.succ))%(m:ℤ)).toNat,
   Vector.ofFn fun j => Vector.ofFn fun i => ((cols[j.val+1]?.getD zeroCol)[i.succ]))

/-- The output columns, read as a square integer matrix. -/
def asMatrix {n : ℕ} (cols : Array (Column n)) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => ((cols[j.val]?.getD (Vector.replicate n 0)).get i)

end DetDLP.BorderedHermite


