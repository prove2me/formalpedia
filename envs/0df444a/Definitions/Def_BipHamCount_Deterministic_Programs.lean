-- Prove2me | Definitions.Def_BipHamCount_Deterministic_Programs
-- name    : BipHamCount_Deterministic_Programs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:47:44.517598+00:00
-- url     : https://prove2.me/theorems/16be4ed0-65c8-4925-a621-f30089374981
-- title:
--   The fixed deterministic counting program and its charged subroutines
-- statement:
--   The programs implement the evaluation specified in §4. The large-term routine fills arrays of permanent pairs for valid row sets and equally sized column sets, addressed by colex ranks, and accumulates the terms with $|S|>k$. Subsets of a prescribed size are generated directly, with impossible recursive branches pruned. The small-term routine generates $U=X\cup Y$ of size at most $k$ and the three labels on every element of $U$.
--
--   For each pair, computeF materializes $C=A[L,Z]B[Z,L]$, $Z=R\setminus(X\cup Y)$, and evaluates $Q(x)=\det(x\Delta+C)$ by the coefficient-array Berkowitz program; $\Delta_{vv}=0$ and $\Delta_{ii}=w_i$ otherwise. It returns
--   $$\sum_{q=0}^{\min(k,m)}(-1)^{m-q+1}[x^q]Q(x).$$
--
--   The outer program discovers a two-colouring by deterministic stack DFS of every component, lists each side in increasing vertex order, and chooses the first left vertex as $v$. Empty inputs, failed colourings and unequal sides return zero. Otherwise it constructs the two adjacency matrices, runs the large and small routines at kOf(m), adds their integer answers and converts to a natural number.
--
--   Every traversal, matrix read, subset primitive, table access and integer/coefficient operation has an explicit charge. Colex sorting, address arithmetic and buffer administration are conservatively overcharged by fixed polynomials in the side size. No specification count, determinant or permanent is called by these programs.
-- source:
--   Koana, Kumabe, Counting Hamiltonian Cycles in Bipartite Digraphs Deterministically in O(1.9526^n) Time, STOC 2027 submission #814 (October 2026), §2 p.4; §4 pp.6–9; Theorem 1.1 p.2. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/814.pdf

import Mathlib
import Definitions.Def_BipHamCount_Deterministic_Core
import Definitions.Def_BipHamCount_Deterministic_Arithmetic

open CapacitatedAssort.General

namespace BipHamCount.Deterministic

/-! The fixed programs of §4, pp.6–9. Natural address arithmetic, finite index
construction and buffer administration are conservatively overcharged by explicit
polynomials. Subset primitives cost m+1; pair-table accesses cost (m+1)².
There are no specification calls, opaque oracles, or uncharged exponential scans. -/

/-- Direct recursive generation of q-subsets, §4.1 p.7. Impossible branches are
pruned before recursion; no powerset is scanned. Each emitted insertion costs m+1. -/
def chooseSets {m : ℕ} : List (Fin m) → ℕ → Work (List (Finset (Fin m)))
  | _, 0 => do charge 2; return [∅]
  | [], _+1 => do charge 1; return []
  | i :: xs, q+1 => do
      charge (m+4)
      if xs.length < q then return []
      let withI ← chooseSets xs q
      let withoutI ← chooseSets xs (q+1)
      let mut out := withoutI
      for S in withI do
        charge (m+3)
        out := insert i S :: out
      return out

/-- Materialize the suffix with zero-based lower bound lo, §4.1 p.7. -/
def suffix {m : ℕ} (lo : ℕ) : Work (List (Fin m)) := do
  charge (4*m+1)
  let mut out := []
  for i in (List.finRange m).reverse do
    charge (m+3)
    if lo ≤ i.val then out := i :: out
  return out

/-- Pascal table for polynomial-time colex addressing, §4.1 p.7.
All address integers have O(m) bits; the square charge covers their additions. -/
def binomTable (m : ℕ) : Work (Array (Array ℕ)) := do
  charge (4*(m+1)+1)
  let mut out := #[]
  let mut prev := Array.replicate (m+1) 0
  for r in List.range (m+1) do
    charge (4*(m+1)+1)
    let mut row := #[]
    for j in List.range (m+1) do
      charge (8*(m+1)^2)
      let x := if j = 0 then 1 else
        if r = 0 then 0 else (prev[j-1]?.getD 0) + (prev[j]?.getD 0)
      row := row.push x
    charge 1
    out := out.push row
    prev := row
  return out

/-- Colex rank of I within the q-subsets of the suffix [lo,m), p.7:
Σ_{t=1}^q binomial(i_t−lo,t). Sorting and address arithmetic are charged. -/
def colex {m : ℕ} (binom : Array (Array ℕ)) (lo : ℕ)
    (I : Finset (Fin m)) : Work ℕ := do
  charge (8*(m+1)^3)
  let mut rank := 0
  let mut t := 1
  for i in I.sort (· ≤ ·) do
    charge (8*(m+1)^2)
    rank := rank + ((binom[i.val-lo]?.getD #[])[t]?.getD 0)
    t := t+1
  return rank

/-- Pair table lookup, p.7, using colex ranks; zero outside a filled layer.
The address multiplication is overcharged in addition to the prescribed table charge. -/
def tableRead (m width ri rj : ℕ) (tab : Array (ℤ × ℤ)) : Work (ℤ × ℤ) := do
  charge ((m+1)^2 + 8*(m+1)^3)
  return tab[ri*width+rj]?.getD (0,0)

/-- Materialize a minor in increasing row and column orders, §2 pp.4–5.
Every entry read and every subset/list operation is charged. -/
def minorBuffer {m : ℕ} (M : Matrix (Fin m) (Fin m) ℤ)
    (S T : Finset (Fin m)) : Work (Array (Array ℤ)) := do
  charge (8*(m+1)^3)
  let rows := S.sort (· ≤ ·)
  let cols := T.sort (· ≤ ·)
  let mut out := #[]
  for i in rows do
    charge 2
    let mut row := #[]
    for j in cols do
      charge 3
      row := row.push (M i j)
    charge 1
    out := out.push row
  return out

/-- Evaluate one large summand from its two previously computed permanents, p.7. -/
def largeSummand {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ)
    (S T : Finset (Fin m)) (pa pb : ℤ) : Work ℤ := do
  charge (4*(m+1))
  let Sc := Sᶜ
  let Tc := Tᶜ
  let a ← minorBuffer A Sc Tc
  let b ← minorBuffer B Tc Sc
  let da ← berkowitz intOps Sc.card a
  let db ← berkowitz intOps Tc.card b
  let s ← paritySign (Sc.card+1)
  let x ← zmul s pa
  let x ← zmul x pb
  let x ← zmul x da
  zmul x db

/-- The valid-set permanent DP and large-term accumulation, §4.1 pp.6–7.
Only adjacent layers are stored in arrays, at colex addresses. A large summand
is accumulated when its layer is filled. No invalid row pairs are generated. -/
def largeTerms (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m)
    (k : ℕ) : Work ℤ := do
  let binom ← binomTable m
  let all ← suffix (m := m) 0
  let mut prev : Array (ℤ × ℤ) := #[]
  let mut prevWidth := 0
  let mut total : ℤ := 0
  charge (4*(m+1)+1)
  for q in List.range (m+1) do
    charge (8*(m+1)^3)
    let lo := k-q
    let rowUniverse ← suffix (m := m) lo
    let rows ← chooseSets rowUniverse q
    let cols ← chooseSets all q
    let nr := ((binom[m-lo]?.getD #[])[q]?.getD 0)
    let nc := ((binom[m]?.getD #[])[q]?.getD 0)
    charge ((nr*nc+1)*((m+1)^2+1))
    let mut cur := Array.replicate (nr*nc) ((0 : ℤ), (0 : ℤ))
    for I in rows do
      charge (8*(m+1)^3)
      let ri ← colex binom lo I
      let first := (I.sort (· ≤ ·)).head?
      for J in cols do
        charge (4*(m+1))
        let rj ← colex binom 0 J
        let mut pa : ℤ := 0
        let mut pb : ℤ := 0
        if q = 0 then
          pa := 1
          pb := 1
        else if let some i := first then
          charge (m+1)
          let Ip := I.erase i
          let rIp ← colex binom (k-(q-1)) Ip
          charge (8*(m+1)^3)
          for j in (J.sort (· ≤ ·)) do
            charge (m+5)
            let Jp := J.erase j
            let rJp ← colex binom 0 Jp
            let old ← tableRead m prevWidth rIp rJp prev
            let a ← zmul (A i j) old.1
            let b ← zmul (B j i) old.2
            pa ← zadd pa a
            pb ← zadd pb b
        charge ((m+1)^2 + 8*(m+1)^3)
        cur := cur.set! (ri*nc+rj) (pa,pb)
        charge (2*(m+1))
        if k < q ∧ v ∉ I then
          let z ← largeSummand A B I J pa pb
          total ← zadd total z
    prev := cur
    prevWidth := nc
  return total

/-- Charged wᵢ calculation from §4.2 p.7. -/
def computeW {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ)
    (X Y : Finset (Fin m)) (i : Fin m) : Work ℤ := do
  charge (16*(m+1)^3)
  let mut a : ℤ := 0
  let mut b : ℤ := 0
  for j in (X.sort (· ≤ ·)) do
    charge 2
    a ← zadd a (A i j)
  for j in (Y.sort (· ≤ ·)) do
    charge 2
    b ← zadd b (B j i)
  zmul a b

/-- F evaluation, Lemma 4.4 pp.8–9. Build C=A[L,Z]B[Z,L], put wᵢx
on the diagonal except at v, use Berkowitz over coefficient arrays, then sum
(−1)^{m−q+1}[x^q]Q. The coefficient loop is clamped at m, the degree bound. -/
def computeF (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m)
    (k : ℕ) (X Y : Finset (Fin m)) : Work ℤ := do
  charge (8*(m+1)^3)
  let Z := (X ∪ Y)ᶜ
  let zs := (Z.sort (· ≤ ·))
  let mut ws : Array ℤ := #[]
  charge (4*m+1)
  for i in List.finRange m do
    charge 2
    let x ← computeW A B X Y i
    ws := ws.push x
  let mut mat : Array (Array ZPoly) := #[]
  charge (4*m+1)
  for i in List.finRange m do
    let mut row := #[]
    charge (4*m+1)
    for j in List.finRange m do
      let mut c : ℤ := 0
      for z in zs do
        charge 3
        let p ← zmul (A i z) (B z j)
        c ← zadd c p
      charge 6
      let p : ZPoly := if i = j ∧ i ≠ v then #[c, ws[i.val]?.getD 0] else #[c]
      row := row.push p
    charge 1
    mat := mat.push row
  let Q ← berkowitz polyOps m mat
  let mut out : ℤ := 0
  charge (4*(min k m+1)+1)
  for q in List.range (min k m+1) do
    charge 2
    let s ← paritySign (m-q+1)
    let a ← zmul s (Q[q]?.getD 0)
    out ← zadd out a
  return out

/-- Three-way labellings of U into X only, Y only, or both, p.8.
Every resulting pair has union U, and is produced exactly once. -/
def labelPairs {m : ℕ} : List (Fin m) → Work (List (Finset (Fin m) × Finset (Fin m)))
  | [] => do charge 2; return [(∅,∅)]
  | i :: xs => do
      charge 1
      let tails ← labelPairs xs
      let mut out := []
      for p in tails do
        charge (4*(m+1)+4)
        let x := insert i p.1
        let y := insert i p.2
        out := (x,p.2) :: (p.1,y) :: (x,y) :: out
      return out

/-- Small-term enumeration by U=X∪Y and its three-way labels, §4.2 pp.7–8.
There is no enumeration over all 4^m pairs (X,Y). -/
def smallTerms (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m)
    (k : ℕ) : Work ℤ := do
  let all ← suffix (m := m) 0
  let mut out : ℤ := 0
  charge (4*(min k m+1)+1)
  for q in List.range (min k m+1) do
    charge 1
    let us ← chooseSets all q
    for U in us do
      charge (8*(m+1)^3)
      let pairs ← labelPairs (U.sort (· ≤ ·))
      for p in pairs do
        charge (2*(m+1)+1)
        let f ← computeF m A B v k p.1 p.2
        let s ← paritySign (p.1.card+p.2.card)
        let z ← zmul s f
        out ← zadd out z
  return out

/-- Deterministic stack DFS of the underlying undirected graph, pp.1–2 and §2 p.4.
All components are started in vertex order. Each newly coloured vertex is pushed once;
n pop attempts per component suffice. A conflicting edge returns none. -/
def twoColor (n : ℕ) (adj : Fin n → Fin n → Bool) : Work (Option (Fin n → Bool)) := do
  charge (4*n+1)
  let mut colors : Array (Option Bool) := Array.replicate n none
  let mut good := true
  for root in List.finRange n do
    charge 3
    if (colors[root.val]?.getD none).isNone then
      charge 2
      colors := colors.set! root.val (some false)
      let mut stack := [root]
      charge (4*n+1)
      for _ in List.range n do
        charge 2
        if let u :: rest := stack then
          stack := rest
          charge 1
          let cu := (colors[u.val]?.getD none).getD false
          charge (4*n+1)
          for w in List.finRange n do
            charge 5
            if adj u w || adj w u then
              match colors[w.val]?.getD none with
              | none =>
                  charge 3
                  colors := colors.set! w.val (some (!cu))
                  stack := w :: stack
              | some cw =>
                  charge 1
                  if cw = cu then good := false
  charge 1
  return if good then some (fun i => (colors[i.val]?.getD none).getD false) else none

/-- Fixed algorithm of Theorem 1.1, p.2, and §4 pp.6–9.
Input contains only adjacency. Empty/unequal-side instances return zero. Sides are
listed in increasing vertex order; v is their first left vertex. -/
def countHamCycles (n : ℕ) (adj : Fin n → Fin n → Bool) : Work ℕ := do
  charge (Nat.size n+2)
  if hn : 0 < n then
    let coloring ← twoColor n adj
    match coloring with
    | none => return 0
    | some c =>
        let mut left : Array (Fin n) := #[]
        let mut right : Array (Fin n) := #[]
        charge (4*n+1)
        for i in List.finRange n do
          charge 3
          if c i then right := right.push i else left := left.push i
        charge (Nat.size n+3)
        if left.size ≠ right.size then return 0
        let m := left.size
        if hm : 0 < m then
          let mut aa : Array (Array ℤ) := #[]
          let mut bb : Array (Array ℤ) := #[]
          charge (4*m+1)
          for i in List.finRange m do
            let mut a := #[]
            let mut b := #[]
            charge (4*m+1)
            for j in List.finRange m do
              charge 10
              let u := left[i.val]?.getD ⟨0, hn⟩
              let w := right[j.val]?.getD ⟨0, hn⟩
              a := a.push (if adj u w then (1 : ℤ) else 0)
              b := b.push (if adj w u then (1 : ℤ) else 0)
            charge 2
            aa := aa.push a
            bb := bb.push b
          let A : Matrix (Fin m) (Fin m) ℤ := fun i j => ((aa[i.val]?.getD #[])[j.val]?).getD 0
          let B : Matrix (Fin m) (Fin m) ℤ := fun j i => ((bb[i.val]?.getD #[])[j.val]?).getD 0
          charge (8*(m+1)^3)
          let v : Fin m := ⟨0, hm⟩
          let k := kOf m
          let large ← largeTerms m A B v k
          let small ← smallTerms m A B v k
          let z ← zadd large small
          let _ ← zcmp z
          charge (Nat.size z.natAbs+1)
          return z.toNat
        else return 0
  else return 0

end BipHamCount.Deterministic


