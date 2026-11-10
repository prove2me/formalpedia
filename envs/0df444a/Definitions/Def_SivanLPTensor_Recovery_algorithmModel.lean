-- Prove2me | Definitions.Def_SivanLPTensor_Recovery_algorithmModel
-- name    : SivanLPTensor_Recovery_algorithmModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T05:33:04.427857+00:00
-- url     : https://prove2.me/theorems/b5128038-2845-424e-82af-9f3c30a80fb7
-- title:
--   All nine steps of Algorithm 1 with singleton preprocessing
-- statement:
--   The routine semantics specify lexicographic Gaussian elimination, nullspace bases, orthonormal column bases, compressed contractions, the spectral pencil, projectors, rank-one block extraction and a final linear solve. For given frames $P,Q$, the compressed operator is
--   $$\Phi=(L^\top\Omega_Q L)(L^\top\Omega_P L)^{-1},\qquad\widehat\Omega_i=L\Pi_i(L^\top\Omega_P L)L^\top.$$
--   The first draw gives $P$. Fresh coefficients generate $Q$ in the explicitly computed nullspace basis of $\Omega_P$. Roots are all distinct real eigenvalues, ordered increasingly; the characteristic polynomial must have only real roots. Singular inverses, insufficient frame ranks, invalid blocks, inconsistent final solves and zero output factors return failure. Step 7 uses one common first-mode representative, and step 9 absorbs the solved coefficients in that first mode.
--   Singleton modes are removed and later restored with factor $1$. With at most two nonsingleton modes the scalar/vector/matrix rank-one branch uses a nonzero tensor entry and its fibers, checks the result, and absorbs the scalar in a retained mode (the first original mode if all modes are singleton). A zero input in that branch returns an empty family.
--   These are mathematical meanings of routines, not extra machine instructions. The implementation predicate requires a finite scalar program's actual halted output to agree on every input and seed. Existence of that implementation and a bound on its executed instructions remain conclusions of Theorem 3.4, not assumptions or hidden fields.
-- source:
--   Shiri Sivan, STOC 2027 submission #1294 (October 2026), Algorithm 1, printed p. 7 / PDF p. 9; correctness and complexity, printed pp. 8–9 / PDF pp. 10–11

import Definitions.Def_SivanLPTensor_Recovery_geometryModel
import Definitions.Def_SivanLPTensor_Recovery_algebraicMachine

noncomputable section

namespace SivanLPTensor.Recovery
open scoped BigOperators
open Classical

/-- Dense, dynamically sized matrices used to describe the source's successive routines.
These are mathematical routine semantics, not additional machine primitives. -/
structure DenseMatrix where
  rows : ℕ
  cols : ℕ
  entry : ℕ → ℕ → ℝ
  deriving Inhabited

abbrev RawMatrix := ℕ → ℕ → ℝ

/-- Lexicographic pivots; normalizing and eliminating are field operations. -/
def reduceRows (A : DenseMatrix) : ℕ × RawMatrix × List ℕ :=
  (List.range A.cols).foldl (fun (s : ℕ × RawMatrix × List ℕ) col =>
    let row := s.1
    let B := s.2.1
    match ((List.range A.rows).filter (fun i => row ≤ i)).find? (fun i => B i col ≠ 0) with
    | none => s
    | some pivot =>
      let swapped : RawMatrix := fun i j =>
        if i = row then B pivot j else if i = pivot then B row j else B i j
      let normalized := fun j => swapped row j / swapped row col
      let result : RawMatrix := fun i j => if i = row then normalized j
        else swapped i j - swapped i col * normalized j
      (row + 1, result, s.2.2 ++ [col])) (0, A.entry, [])

def nullBasis (A : DenseMatrix) : DenseMatrix :=
  let rr := reduceRows A
  let free := (List.range A.cols).filter (fun c => c ∉ rr.2.2)
  { rows := A.cols, cols := free.length
    entry := fun i j =>
      if h : j < free.length then
        let f := free[j]
        if i = f then 1 else
          match rr.2.2.idxOf? i with
          | none => 0
          | some t => -rr.2.1 t f
      else 0 }

def denseTranspose (A : DenseMatrix) : DenseMatrix :=
  ⟨A.cols, A.rows, fun i j => A.entry j i⟩

def denseMul (A B : DenseMatrix) : DenseMatrix :=
  ⟨A.rows, B.cols, fun i j => ∑ k ∈ Finset.range A.cols, A.entry i k * B.entry k j⟩

def denseIdentity (n : ℕ) : DenseMatrix :=
  ⟨n,n,fun i j => if i = j then 1 else 0⟩

def square (A : DenseMatrix) : Matrix (Fin A.rows) (Fin A.rows) ℝ :=
  fun i j => A.entry i.val j.val

def denseInverse (A : DenseMatrix) : DenseMatrix :=
  ⟨A.rows,A.rows,fun i j => if hi : i < A.rows then if hj : j < A.rows then
    (square A)⁻¹ ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0⟩

def orthonormalColumns (A : DenseMatrix) : DenseMatrix :=
  let pivots := (reduceRows A).2.2
  let columns : List (ℕ → ℝ) := pivots.foldl (fun bs col =>
    let v := bs.foldl (fun v b =>
      let dot := ∑ i ∈ Finset.range A.rows, v i * b i
      fun i => v i - dot * b i) (fun i => A.entry i col)
    let norm := Real.sqrt (∑ i ∈ Finset.range A.rows, v i * v i)
    bs ++ [fun i => v i / norm]) []
  ⟨A.rows, columns.length, fun i j => (columns[j]?.getD (fun _ => 0)) i⟩

def offset {m : ℕ} {n : Fin m → ℕ} (x : BlockIndex n) : ℕ :=
  (∑ j ∈ Finset.univ.filter (fun j : Fin m => j < x.1), n j) + x.2.val

def asDense {m : ℕ} {n : Fin m → ℕ}
    (A : Matrix (BlockIndex n) (BlockIndex n) ℝ) : DenseMatrix :=
  let D := ∑ j, n j
  ⟨D,D,fun u v => ∑ x, ∑ y, if offset x = u ∧ offset y = v then A x y else 0⟩

def toAmbientFrame {m d : ℕ} {n : Fin m → ℕ} (P : DenseMatrix) :
    Matrix (Fin d) (BlockIndex n) ℝ := fun t x => P.entry t.val (offset x)

def spectralProjector (Phi : DenseMatrix) (roots : List ℝ) (ρ : ℝ) : DenseMatrix :=
  (roots.filter (· ≠ ρ)).foldl (fun A τ =>
    denseMul A ⟨Phi.rows,Phi.cols,fun i j =>
      (Phi.entry i j - τ * (if i = j then 1 else 0)) / (ρ - τ)⟩)
    (denseIdentity Phi.rows)

/-- Concrete step-7 factor extraction, with a common first-mode representative. -/
def directions {d : ℕ} {n : Fin (d + 2) → ℕ}
    (components : List DenseMatrix) : Option (Factors n components.length) := Id.run do
  let j0 : Fin (d + 2) := 0
  let j1 : Fin (d + 2) := 1
  let pivots := components.map (fun B =>
    ((List.finRange (n j0)).flatMap (fun x =>
      (List.finRange (n j1)).map (fun y => (x.val,y.val)))).find? (fun xy =>
        B.entry xy.1 (n j0 + xy.2) ≠ 0))
  if pivots.any Option.isNone then return none
  let a : Factors n components.length := fun j i x =>
    let B := components[i.val]!
    let pivot := pivots[i.val]!.getD (0,0)
    if j = j0 then B.entry (offset (n := n) ⟨j,x⟩) (n j0 + pivot.2)
    else B.entry pivot.1 (offset (n := n) ⟨j,x⟩) /
      B.entry pivot.1 (n j0 + pivot.2)
  if ∀ (i : Fin components.length) (j : Fin (d + 2)), j ≠ j0 →
      (∃ (x : Fin (n j0)) (y : Fin (n j)), components[i.val]!.entry (offset (n := n) ⟨j0,x⟩) (offset (n := n) ⟨j,y⟩) ≠ 0) ∧
      ∀ (x : Fin (n j0)) (y : Fin (n j)), components[i.val]!.entry (offset (n := n) ⟨j0,x⟩) (offset (n := n) ⟨j,y⟩) = a j0 i x * a j i y
    then return some a else return none

/-- The final linear solve, with all free variables zero and an explicit residual test. -/
def rescale {m r : ℕ} {n : Fin m → ℕ} (T : Tensor n)
    (a : Factors n r) : Option (Factors n r) :=
  let coords := tensorCoordinates n
  let A : DenseMatrix := ⟨coords.length,r+1,fun i j =>
    match coords[i]? with
    | none => 0
    | some α => if h : j < r then pureTensor (fun k => a k ⟨j,h⟩) α else T α⟩
  let rr := reduceRows A
  let lambda := fun i : Fin r => match rr.2.2.idxOf? i.val with
    | none => 0
    | some row => rr.2.1 row r
  let b : Factors n r := fun j i => if j.val = 0 then lambda i • a j i else a j i
  if synthesis b = T ∧ NonzeroFactors b then some b else none

/-- Steps 3–9 for specified P,Q, retaining all tests and final rescaling. -/
def algorithm1Frames {d : ℕ} {n : Fin (d + 2) → ℕ}
    (T : Tensor n) (P Q : Matrix (Fin d) (BlockIndex n) ℝ) :
    Option (Σ r : ℕ, Factors n r) := Id.run do
  let OP := asDense (omegaFormula T P)
  let OQ := asDense (omegaFormula T Q)
  let L := orthonormalColumns OP
  let UP := denseMul (denseMul (denseTranspose L) OP) L
  let UQ := denseMul (denseMul (denseTranspose L) OQ) L
  if Matrix.det (square UP) = 0 then return none
  let Phi := denseMul UQ (denseInverse UP)
  let poly := (square Phi).charpoly
  if poly.roots.card ≠ Phi.rows then return none
  let roots := poly.roots.toFinset.sort (· ≤ ·)
  let components := roots.map (fun rho =>
    denseMul (denseMul (denseMul L (spectralProjector Phi roots rho)) UP) (denseTranspose L))
  match directions (n := n) components with
  | none => return none
  | some a =>
    match rescale T a with
    | none => return none
    | some b => return some ⟨components.length,b⟩

/-- Steps 1–2: sample Q in a computed basis of the kernel, then execute steps 3–9. -/
def algorithm1Core {d : ℕ} {n : Fin (d + 2) → ℕ}
    (T : Tensor n) (seed : ℕ → ℝ) : Option (Σ r : ℕ, Factors n r) := Id.run do
  let D := ∑ j, n j
  let P : DenseMatrix := ⟨d,D,fun t x => seed (t * D + x)⟩
  if (reduceRows P).1 ≠ d then return none
  let OP := asDense (omegaFormula T (toAmbientFrame (d := d) P))
  let K := nullBasis OP
  if K.cols < d then return none
  let coeff : DenseMatrix := ⟨d,K.cols,fun t s => seed (d * D + t * K.cols + s)⟩
  let Q := denseMul coeff (denseTranspose K)
  if (reduceRows Q).1 ≠ d then return none
  return algorithm1Frames T (toAmbientFrame P) (toAmbientFrame Q)

/-- Full-domain scalar/vector/matrix rank-one branch; singleton factors are restored as 1. -/
def rankOneBranch {m : ℕ} {n : Fin m → ℕ} (T : Tensor n) :
    Option (Σ r : ℕ, Factors n r) :=
  let coords := tensorCoordinates n
  match coords.find? (fun α => T α ≠ 0) with
  | none => some ⟨0,fun _ i => Fin.elim0 i⟩
  | some pivot =>
    let active := (List.finRange m).filter (fun j => 1 < n j)
    let absorb := (active.head?).map Fin.val |>.getD 0
    let a : Factors n 1 := fun j _ x =>
      if j.val = absorb then T (Function.update pivot j x)
      else if n j = 1 then 1 else T (Function.update pivot j x) / T pivot
    if synthesis a = T ∧ NonzeroFactors a then some ⟨1,a⟩ else none

/-- Source-sanctioned singleton preprocessing and restoration. The reduced tensor is
selected by retained coordinates only; no factors or rank are supplied to the routine. -/
def algorithm1 {m : ℕ} {n : Fin m → ℕ} (hm : 3 ≤ m)
    (T : Tensor n) (seed : ℕ → ℝ) : Option (Σ r : ℕ, Factors n r) :=
  let active := (List.finRange m).filter (fun j => 1 < n j)
  if active.length ≤ 2 then rankOneBranch T else
    let d := active.length - 2
    let g : Fin (d + 2) → Fin m := fun t => active[t.val]?.getD ⟨0,by omega⟩
    let nr := fun t => n (g t)
    let reduced : Tensor nr := fun β =>
      ∑ α, if ∀ t, (α (g t)).val = (β t).val then T α else 0
    match algorithm1Core reduced seed with
    | none => none
    | some out =>
      let lifted : Factors n out.1 := fun j i x =>
        match (List.finRange (d + 2)).find? (fun t => g t = j) with
        | none => 1
        | some t => if h : x.val < nr t then out.2 t i ⟨x.val,h⟩ else 0
      some ⟨out.1,lifted⟩

/-- Compilation/implementation is a theorem obligation, not a new unit-cost primitive.
The result is determined by execution of a finite program on T and dimensions alone. -/
def ImplementsAlgorithm1 (p : Program) : Prop :=
  ∀ (m : ℕ) (n : Fin m → ℕ) (hm : 3 ≤ m), (∀ j, 0 < n j) →
    ∀ (T : Tensor n) seed, ∃ t,
      let s := machineRun p (encodeInput T) seed t
      s.stopped = true ∧
      match algorithm1 hm T seed with
      | none => s.natural 1 = 0
      | some b => s.natural 1 = 1 ∧ s.natural 0 = b.1 ∧
          HEq (outputFactors (n := n) s) b.2

end SivanLPTensor.Recovery


