-- Prove2me | Definitions.Def_ChvatalOneHard398_SAT_Supplement_Algorithms
-- name    : ChvatalOneHard398_SAT_Supplement_Algorithms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:18:45.608861+00:00
-- url     : https://prove2.me/theorems/9b7717b5-f1ff-4ba7-a198-2acddf8a3640
-- title:
--   Hermite basis, kernel elimination and the canonical formula map
-- statement:
--   For an integer matrix $A$ and modulus $q$, a deterministic integer row-Hermite computation is applied to the transposed generators $[A^T\mid qI_m]$. Extended gcd operations produce a positive pivot, eliminate the pivot coordinate and reduce entries against the later pivots. The resulting columns form the matrix denoted $B(A)$; its basis and coefficient guarantees are conclusions of Proposition 11.
--
--   A separate bounded Gaussian elimination over $\mathbb Z/q\mathbb Z$ uses the first available pivot in column order. Free columns in increasing order give nullspace vectors with free coordinate one and pivot coordinates read from the reduced matrix. Their canonical residues form $H(A)$. Its lattice equality and row-count guarantees are conclusions of Lemma 28.
--
--   Set $k=\lceil\log_2q\rceil$, $m=3nk$, and $r=\lfloor(q-1)/(16m^2)\rfloor$. The parallelepiped map uses $B(A),t,r$. The formula map uses the largest $h$ with $h2^h\le q/(4m^{3/2})$, and one maximal prime power at most $h$ per prime, in increasing prime order. It calls the published lattice formula, including its asymmetric error box and target shift. Raw degenerate parameters have explicit total defaults. No correctness, rank, thinness or complexity assertion is a field of the construction data.
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.14–15, 29–30, Proposition 11, Lemma 28 and Theorem 29. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Supplement_Ary

namespace ChvatalOneHard398.SAT.Supplement
open scoped BigOperators

def rowAdd (s : ℤ) (u : List ℤ) (t : ℤ) (v : List ℤ) : List ℤ :=
  List.zipWith (fun x y => s*x+t*y) u v

/-- Integer row-Hermite elimination of the transposed generator matrix. Gcd operations
are explicit; the definition contains no basis or rank assertions. -/
def hermiteRows : ℕ → List (List ℤ) → List (List ℤ)
  | 0, _ => []
  | d+1, rows =>
    let z := rows.foldl (fun (st : List ℤ × List (List ℤ)) v =>
      let a := st.1.headD 0
      let b := v.headD 0
      let g := (Int.gcd a b : ℤ)
      let p := rowAdd (Int.gcdA a b) st.1 (Int.gcdB a b) v
      let w := rowAdd (-b / g) st.1 (a / g) v
      if g = 0 then (st.1, st.2 ++ [v.tail])
      else (p, st.2 ++ [w.tail])) (List.replicate (d+1) 0, [])
    let tails := hermiteRows d z.2
    let reduced := tails.zipIdx |>.foldl (fun (v : List ℤ) bk =>
      let b := bk.1
      let k := bk.2
      rowAdd 1 v (-((v[k]!) / (b[k]!))) b) z.1.tail
    (z.1.headD 0 :: reduced) :: tails.map (0 :: ·)

def basisMatrix (a : AryMatrix) : Matrix (Fin a.m) (Fin a.m) ℤ :=
  let gs := (List.finRange a.n).map (fun i => List.ofFn (a.A i)) ++
    (List.finRange a.m).map (fun i => List.ofFn fun j => if i=j then (a.q : ℤ) else 0)
  let bs := hermiteRows a.m gs
  fun i j => (bs[j.val]!).getD i.val 0

/-- Exact ceiling of log base two, totalized to zero at q=0. -/
def bits (q : ℕ) : ℕ := if q ≤ 1 then 0 else Nat.log 2 (q-1)+1

def samples (n q : ℕ) : ℕ := 3*n*bits q

def radius (m q : ℕ) : ℤ := ((q : ℤ)-1) / (16*(m : ℤ)^2)

def toPara (a : AryInput) : ParaInput :=
  ⟨a.m, fun i j => (basisMatrix a.toAryMatrix i j : ℚ),
    fun j => (a.t j : ℚ), (radius a.m a.q : ℚ)⟩

/-- Full reduced row elimination over Z/qZ; inverses are used only in the prime case
in the theorems. The loop is bounded on malformed data as well. -/
noncomputable def eliminate (a : AryMatrix) : List (Fin a.m → ZMod a.q) × List ℕ := Id.run do
  let mut rows := (List.finRange a.n).map (fun i j => (a.A i j : ZMod a.q))
  let mut pivots := []
  for j in List.finRange a.m do
    let rank := pivots.length
    let found := (List.range a.n).find? (fun i => rank ≤ i ∧ (rows.getD i 0) j ≠ 0)
    match found with
    | none => pure ()
    | some i =>
      let pivot := rows.getD i 0
      let old := rows.getD rank 0
      rows := (rows.set i old).set rank pivot
      let normalized := fun l => (pivot j)⁻¹ * pivot l
      rows := rows.set rank normalized
      rows := (rows.zipIdx).map fun ri =>
        if ri.2 = rank then normalized else fun l => ri.1 l - ri.1 j * normalized l
      pivots := pivots ++ [j.val]
  return (rows,pivots)

structure KernelMatrix (m : ℕ) where
  r : ℕ
  H : Matrix (Fin r) (Fin m) ℤ

noncomputable def kernelMatrix (a : AryMatrix) : KernelMatrix a.m :=
  let z := eliminate a
  let free := (List.range a.m).filter (fun j => j ∉ z.2)
  ⟨free.length, fun i j =>
    let k := free[i.val]!
    let v : ZMod a.q := if j.val = k then 1 else
      match (z.2.zipIdx).find? (fun pi => pi.1 = j.val) with
      | none => 0
      | some pi => -((List.ofFn (z.1.getD pi.2 0)).getD k 0)
    v.val⟩

/-- A bounded search for the largest admissible h; q itself bounds h when m>0.
The zero-dimensional raw case has the explicit default h=0. -/
noncomputable def height (n q : ℕ) : ℕ :=
  if samples n q = 0 then 0 else
    ((List.range (bits q+1)).filter (fun (h : ℕ) => (h : ℝ) * (2 : ℝ)^h ≤
      (q : ℝ)/(4*(samples n q : ℝ)^(3/2 : ℝ)))).foldl max 0

/-- One maximal prime power per prime, in increasing order of its prime. -/
def primePowers (h : ℕ) : List ℕ :=
  ((List.range (h+1)).filter Nat.Prime).map fun p => p ^ Nat.log p h

noncomputable def formulaParams (a : AryInput) : Params :=
  let H := kernelMatrix a.toAryMatrix
  ⟨a.m,H.r,primePowers (height a.n a.q),height a.n a.q,a.q,H.H,a.t⟩

noncomputable def toFormula (a : AryInput) : Formula := latticeFormula (formulaParams a)

def encAryMatrix (a : AryMatrix) : List OnlineCRS.Combine.Sym :=
  frame (List.replicate a.n 1) ++ frame (List.replicate a.m 1) ++
  frame (OnlineCRS.Combine.encNat a.q) ++
  RobustToDynamics.encMat (fun i j => (a.A i j : ℚ))

def encAry (a : AryInput) : List OnlineCRS.Combine.Sym :=
  frame (encAryMatrix a.toAryMatrix) ++ OnlineCRS.Combine.encVec (fun j => (a.t j : ℚ))

def encBasis (a : AryMatrix) (B : Matrix (Fin a.m) (Fin a.m) ℤ) :=
  RobustToDynamics.encMat (fun i j => (B i j : ℚ))

def encKernel {m : ℕ} (H : KernelMatrix m) : List OnlineCRS.Combine.Sym :=
  frame (OnlineCRS.Combine.encNat m) ++ frame (OnlineCRS.Combine.encNat H.r) ++
  RobustToDynamics.encMat (fun i j => (H.H i j : ℚ))

end ChvatalOneHard398.SAT.Supplement


