-- Prove2me | Definitions.Def_QMCTied_Prog
-- name    : QMCTied_Prog
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T10:14:21.125524+00:00
-- url     : https://prove2.me/theorems/98fc317a-b926-40f0-8e91-db4819e4ce03
-- title:
--   List program for the level-$k$ Pauli moment relaxation
-- statement:
--   Enumerates the Pauli words of support at most $k$ as dense label lists without repetition, builds the tables of product classes, real phase signs and normalized objective coefficients, and runs the guarded integer penalty supergradient iteration on the table of class values. The output is the total weight times the best certified normalized value.
-- source:
--   Supporting library for QuantumMaxCutEnergy.PauliSDP.uniform_value_lower_approximation_compiler (Prove2me Quantum Max-Cut campaign; level-k Pauli moment relaxation as in Gribling, Sinjorgo and Sotirov, arXiv:2504.11120, Section 2). Method: integer penalty supergradient iteration with matrix-power certificates.

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_QMCSub_Fold
import Definitions.Def_QMCSub_Prog

/-!
The list-level program for the level-`k` Pauli moment relaxation: enumeration of Pauli words,
their product, sign and class tables, and a guarded integer penalty supergradient iteration on
the table of class values.
-/

namespace QMCTied
open QMCNumericRuntime QMCSub

/-! ### Generic iteration on tables -/

/-- Static data: `idx, clsTab, sgnTab, gCTab, csTab, fuelK, padI, padO, prm` with
`prm = [D, eta, dN, D2, c0]`. -/
abbrev ST := List ℕ × Mat × Mat × Mat × Mat × List Unit × List Unit × List Unit × List ℚ

/-- Rounding toward zero. -/
def qrnd (q : ℚ) : ℚ := if q < 0 then -qfloor (-q) else qfloor q

def clampQ (D x : ℚ) : ℚ := if x < -D then -D else if D < x then D else x

def maxQ (a b : ℚ) : ℚ := if a < b then b else a

/-- The shifted matrix `N D - sgn * Y`. -/
def shiftT (idx : List ℕ) (sgnTab : Mat) (D : ℚ) (Y : Mat) : Mat :=
  idx.map (fun i => idx.map (fun j =>
    (if i = j then (idx.length : ℚ) * D else 0) - gm sgnTab i j * gm Y i j))

def powT (s : ST) (Y : Mat) : Mat :=
  matPow s.1 (shiftT s.1 s.2.2.1 (gv s.2.2.2.2.2.2.2.2 0) Y) s.2.2.2.2.2.2.1 s.2.2.2.2.2.1

/-- Class sum of the signed power matrix, for the class of entry `(i, j)`. -/
def gQT (idx : List ℕ) (clsTab sgnTab Q : Mat) (i j : ℕ) : ℚ :=
  (idx.map (fun i' => (idx.map (fun j' =>
    if gm clsTab i' j' = gm clsTab i j then gm sgnTab i' j' * gm Q i' j' else 0)).sum)).sum

/-- Whether the penalty is active. -/
def actT (s : ST) (Y : Mat) : Bool :=
  decide ((s.1.length : ℚ) * gv s.2.2.2.2.2.2.2.2 0 * diagSum s.1 (powT s Y) <
    lapDot s.1 (shiftT s.1 s.2.2.1 (gv s.2.2.2.2.2.2.2.2 0) Y) (powT s Y))

def stepT (s : ST) (Y : Mat) (i j : ℕ) : ℚ :=
  gv s.2.2.2.2.2.2.2.2 1 * (gm s.2.2.2.1 i j +
    (if actT s Y then
      2 * gQT s.1 s.2.1 s.2.2.1 (powT s Y) i j / diagSum s.1 (powT s Y) else 0))

def nextT (s : ST) (Y : Mat) : Mat :=
  s.1.map (fun i => s.1.map (fun j =>
    if i = j then capQ s.2.2.2.2.2.2.2.1 (gm Y i j)
    else capQ s.2.2.2.2.2.2.2.1
      (clampQ (gv s.2.2.2.2.2.2.2.2 0) (gm Y i j + qrnd (stepT s Y i j)))))

def aqT (s : ST) (Y : Mat) : ℚ :=
  maxQ 0 (lapDot s.1 (shiftT s.1 s.2.2.1 (gv s.2.2.2.2.2.2.2.2 0) Y) (powT s Y) *
      (gv s.2.2.2.2.2.2.2.2 2 + 1) /
      (diagSum s.1 (powT s Y) * (gv s.2.2.2.2.2.2.2.2 2 - 1)) -
    (s.1.length : ℚ) * gv s.2.2.2.2.2.2.2.2 0) / gv s.2.2.2.2.2.2.2.2 0

def objT (s : ST) (Y : Mat) : ℚ :=
  gv s.2.2.2.2.2.2.2.2 4 + lapDot s.1 s.2.2.2.2.1 Y / gv s.2.2.2.2.2.2.2.2 0

def valT (s : ST) (Y : Mat) : ℚ :=
  (objT s Y + aqT s Y * gv s.2.2.2.2.2.2.2.2 4) / (1 + aqT s Y)

/-- One guarded step on `(Y, best)`. -/
def stepO (s : ST) (d : Mat × ℚ) : Mat × ℚ :=
  (nextT s d.1,
   capQ s.2.2.2.2.2.2.2.1
     (maxQ d.2 (qfloor (gv s.2.2.2.2.2.2.2.2 3 * maxQ 0 (valT s d.1)))))

/-! ### Pauli words and tables -/

/-- The all-identity word on the positions `idxn`. -/
def zeroW (idxn : List ℕ) : Vec := idxn.map (fun _ => (0 : ℚ))

def setW (idxn : List ℕ) (w : Vec) (p : ℕ) (a : ℚ) : Vec :=
  idxn.map (fun q => if q = p then a else gv w q)

/-- Add all single-site modifications. -/
def extW (idxn : List ℕ) (ws : List Vec) : List Vec :=
  ws ++ ws.flatMap (fun w => idxn.flatMap (fun p =>
    [(1 : ℚ), 2, 3].map (fun a => setW idxn w p a)))

/-- All words of support at most `k`, with repetitions. -/
def rowsRaw : ℕ → List ℕ → List Vec
  | 0, idxn => [zeroW idxn]
  | k + 1, idxn => extW idxn (rowsRaw k idxn)

def wordEq (idxn : List ℕ) (w v : Vec) : Bool :=
  (idxn.filter (fun q => !decide (gv w q = gv v q))).isEmpty

/-- Keep the first occurrence of every word. -/
def dedupW (idxn : List ℕ) (R : List Vec) : List Vec :=
  ((List.range R.length).filter (fun i =>
    ((List.range R.length).filter (fun i' =>
      decide (i' < i) && wordEq idxn (R[i']?.getD []) (R[i]?.getD []))).isEmpty)).map
    (fun i => R[i]?.getD [])

/-- The rows of the Gram matrix: all words of support at most `k`, without repetition. -/
def rowsW (k : ℕ) (idxn : List ℕ) : List Vec := dedupW idxn (rowsRaw k idxn)

/-- Product of Pauli labels `0, 1, 2, 3`. -/
def lp (a b : ℚ) : ℚ := if a = b then 0 else if a = 0 then b else if b = 0 then a else 6 - a - b

/-- Exponent of `i` in the phase of a product of Pauli labels. -/
def le (a b : ℚ) : ℚ :=
  if a = 0 then 0 else if b = 0 then 0 else if a = b then 0
  else if b - a = 1 then 1 else if b - a = -2 then 1 else 3

def prodW (idxn : List ℕ) (w v : Vec) : Vec := idxn.map (fun q => lp (gv w q) (gv v q))

def expoW (idxn : List ℕ) (w v : Vec) : ℚ := (idxn.map (fun q => le (gv w q) (gv v q))).sum

/-- Real part of `i ^ t` for a natural exponent `t`. -/
def sgnOf (t : ℚ) : ℚ :=
  if t - 4 * qfloor (t / 4) = 0 then 1 else if t - 4 * qfloor (t / 4) = 2 then -1 else 0

def rowAt (rows : List Vec) (i : ℕ) : Vec := rows[i]?.getD []

def sgnTabW (idxn : List ℕ) (rows : List Vec) : Mat :=
  (List.range rows.length).map (fun i => (List.range rows.length).map (fun j =>
    sgnOf (expoW idxn (rowAt rows i) (rowAt rows j))))

def pairsW (rows : List Vec) : List (ℕ × ℕ) :=
  (List.range rows.length).flatMap (fun i => (List.range rows.length).map (fun j => (i, j)))

/-- Class identifiers: the position of the first pair with the same product word. -/
def clsTabW (idxn : List ℕ) (rows : List Vec) : Mat :=
  (List.range rows.length).map (fun i => (List.range rows.length).map (fun j =>
    (((pairsW rows).findIdx (fun p =>
      wordEq idxn (prodW idxn (rowAt rows p.1) (rowAt rows p.2))
        (prodW idxn (rowAt rows i) (rowAt rows j))) : ℕ) : ℚ)))

def suppW (idxn : List ℕ) (w : Vec) : List ℕ := idxn.filter (fun q => !decide (gv w q = 0))

/-- Normalized objective coefficients: `-(w_pq / W) / 2` at the entry of two equal single-site
labels on `p < q`. -/
def csTabW (idxn : List ℕ) (rows : List Vec) (xs : List NumericEdge) : Mat :=
  (List.range rows.length).map (fun i => (List.range rows.length).map (fun j =>
    if (suppW idxn (rowAt rows i)).length = 1 then
      (if (suppW idxn (rowAt rows j)).length = 1 then
        (if gv (rowAt rows i) ((suppW idxn (rowAt rows i)).head?.getD 0) =
            gv (rowAt rows j) ((suppW idxn (rowAt rows j)).head?.getD 0) then
          (if (suppW idxn (rowAt rows i)).head?.getD 0 < (suppW idxn (rowAt rows j)).head?.getD 0
            then -(edgeW xs ((suppW idxn (rowAt rows i)).head?.getD 0)
                ((suppW idxn (rowAt rows j)).head?.getD 0)) / (2 * edgeWeightSum xs)
            else 0)
          else 0)
        else 0)
      else 0))

def gCTabW (idx : List ℕ) (clsTab csTab : Mat) : Mat :=
  idx.map (fun i => idx.map (fun j =>
    (idx.map (fun i' => (idx.map (fun j' =>
      if gm clsTab i' j' = gm clsTab i j then gm csTab i' j' else 0)).sum)).sum))

/-! ### Parameters, as functions of the number of rows -/

def NQ (idx : List ℕ) : ℚ := (idx.length : ℚ)

/-- Grid `D = 4096 E^2 N^8`. -/
def DQ (E : ℕ) (idx : List ℕ) : ℚ :=
  4096 * (E : ℚ) * (E : ℚ) *
    (NQ idx * NQ idx * NQ idx * NQ idx * NQ idx * NQ idx * NQ idx * NQ idx)

/-- Step `eta = 16 E N^2` in grid units. -/
def etaQ2 (E : ℕ) (idx : List ℕ) : ℚ := 16 * (E : ℚ) * (NQ idx * NQ idx)

/-- `dN = 48 E N^2`. -/
def dNQ (E : ℕ) (idx : List ℕ) : ℚ := 48 * (E : ℚ) * (NQ idx * NQ idx)

def prmW (E : ℕ) (idx : List ℕ) : List ℚ :=
  [DQ E idx, etaQ2 E idx, dNQ E idx, 8 * (E : ℚ), 1 / 2]

/-- Outer fuel, of length `1024 E^2 N^8`. -/
def fuelT2 (E : ℕ) (idx : List ℕ) : List Unit :=
  pw idx (pw idx (pw idx (pw idx (pw idx (pw idx (pw idx (pw idx (rep (1024 * E * E)))))))))

/-- Inner fuel, of length `2K = 96 E N^2 (48 E + 3 N)`. -/
def fuelK2 (E : ℕ) (idx : List ℕ) : List Unit :=
  (pw idx (pw idx (rep (96 * E)))).flatMap (fun _ => rep (48 * E) ++ pw idx (rep 3))

/-- Inner size pad, of length `1 + 2K (8192 E^2 + 10 N)`. -/
def padI2 (E : ℕ) (idx : List ℕ) : List Unit :=
  () :: (fuelK2 E idx).flatMap (fun _ => rep (8192 * E * E) ++ pw idx (rep 10))

/-- Outer size pad, of length `4096 E^2 + 1 + 8 N`. -/
def padO2 (E : ℕ) (idx : List ℕ) : List Unit := rep (4096 * E * E + 1) ++ pw idx (rep 8)

/-! ### The solver -/

def staticW (k E : ℕ) (idxn : List ℕ) (xs : List NumericEdge) : ST :=
  (List.range (rowsW k idxn).length,
   clsTabW idxn (rowsW k idxn),
   sgnTabW idxn (rowsW k idxn),
   gCTabW (List.range (rowsW k idxn).length) (clsTabW idxn (rowsW k idxn))
     (csTabW idxn (rowsW k idxn) xs),
   csTabW idxn (rowsW k idxn) xs,
   fuelK2 E (List.range (rowsW k idxn).length),
   padI2 E (List.range (rowsW k idxn).length),
   padO2 E (List.range (rowsW k idxn).length),
   prmW E (List.range (rowsW k idxn).length))

def initY (D : ℚ) (idx : List ℕ) : Mat :=
  idx.map (fun i => idx.map (fun j => if i = j then D else 0))

/-- The final `(Y, best)` after the outer loop. -/
def runW (k E : ℕ) (idxn : List ℕ) (xs : List NumericEdge) : Mat × ℚ :=
  (gfold stepO (fuelT2 E (List.range (rowsW k idxn).length))
    (staticW k E idxn xs,
      (initY (DQ E (List.range (rowsW k idxn).length)) (List.range (rowsW k idxn).length),
        (0 : ℚ)))).2

/-- The lower value for the level-`k` relaxation with accuracy `1 / E`. -/
def solveW (k E : ℕ) (idxn : List ℕ) (xs : List NumericEdge) : ℚ :=
  if edgeWeightSum xs = 0 then 0
  else edgeWeightSum xs * ((runW k E idxn xs).2 / (8 * (E : ℚ)))

def solveRawW (k E : ℕ) (bits : List Bool) : ℚ :=
  solveW k E (parserVertices bits) (parseEdges bits)

end QMCTied


