-- Prove2me | Definitions.Def_QMCSub_Prog
-- name    : QMCSub_Prog
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T09:15:44.85027+00:00
-- url     : https://prove2.me/theorems/cb89043d-7bf9-402c-babb-c175d7c49efa
-- title:
--   List program: rounded dual subgradient method for the Max-Cut SDP
-- statement:
--   The list-level program behind the polynomial-time lower value for the Max-Cut semidefinite relaxation. From the vertex list and the weighted edge list it scales and rounds the weights to integers, forms their Laplacian $L$, and runs $T=c_Tn^3$ steps of a dual subgradient iteration on $u\in\mathbb Z^n$. Each step computes the exact matrix power $Q=(L+\operatorname{diag}(\sigma+u))^{2K}$ by repeated multiplication, updates $u_i\leftarrow u_i+\eta-\lfloor\eta nQ_{ii}/\operatorname{tr}Q\rfloor$ and accumulates $\lfloor n\langle L,Q\rangle/\operatorname{tr}Q\rfloor$. Every stored number passes a bit-size guard, so the state stays polynomially bounded on all inputs. The output is the scaled average of the accumulated values when a primal feasibility check on the final iterate passes, and $0$ otherwise.
-- source:
--   Supporting library for QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2 (Prove2me mission 'Quantum Max-Cut: 0.526 energy estimation'; Anshu, Gosset, Morenz, Beyond product state approximations for a quantum analogue of Max Cut, arXiv:2003.14394). Method: rounded dual subgradient iteration for the Max-Cut semidefinite relaxation with matrix-power approximate subgradients.

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_QMCSub_Fold

/-!
The list-level program: a rounded dual subgradient method for the Max-Cut SDP whose
approximate subgradients are diagonals of exact matrix powers.
-/

namespace QMCSub
open QMCNumericRuntime

abbrev Vec := List ℚ
abbrev Mat := List (List ℚ)

/-- Vector entry, `0` outside the list. -/
def gv (v : Vec) (i : ℕ) : ℚ := v[i]?.getD 0

/-- Matrix entry, `0` outside the lists. -/
def gm (A : Mat) (i j : ℕ) : ℚ := (A[i]?.getD [])[j]?.getD 0

/-- Floor of a nonnegative rational, as a rational. -/
def qfloor (q : ℚ) : ℚ := ((q.num.natAbs / q.den : ℕ) : ℚ)

/-- Numerator and denominator both have at most `m` bits. -/
def fitsQ (m : ℕ) (q : ℚ) : Bool :=
  decide (q.num.natAbs.size ≤ m) && decide (q.den.size ≤ m)

/-- Size guard: keep `q` if it fits in `pad.length` bits, otherwise `0`. -/
def capQ (pad : List Unit) (q : ℚ) : ℚ := if fitsQ pad.length q then q else 0

def idMat (idx : List ℕ) : Mat :=
  idx.map (fun i => idx.map (fun j => if i = j then (1 : ℚ) else 0))

/-- Inner static data: index list, the matrix `M`, the size pad. -/
abbrev SI := List ℕ × Mat × List Unit

/-- One guarded multiplication `P ↦ P * M`. -/
def innerStep (s : SI) (P : Mat) : Mat :=
  s.1.map (fun i => s.1.map (fun j =>
    capQ s.2.2 ((s.1.map (fun k => gm P i k * gm s.2.1 k j)).sum)))

/-- `M ^ fuel.length`, by repeated guarded multiplication. -/
def matPow (idx : List ℕ) (M : Mat) (pad fuel : List Unit) : Mat :=
  (gfold innerStep fuel ((idx, M, pad), idMat idx)).2

def shiftMat (idx : List ℕ) (lap : Mat) (sig : ℚ) (u : Vec) : Mat :=
  idx.map (fun i => idx.map (fun j => gm lap i j + (if i = j then sig + gv u i else 0)))

def diagSum (idx : List ℕ) (Q : Mat) : ℚ := (idx.map (fun i => gm Q i i)).sum

def lapDot (idx : List ℕ) (lap Q : Mat) : ℚ :=
  (idx.map (fun i => (idx.map (fun j => gm lap i j * gm Q i j)).sum)).sum

/-- Outer static data: `idx, lap, fuelK, padI, padO, eta, sig`. -/
abbrev SO := List ℕ × Mat × List Unit × List Unit × List Unit × ℚ × ℚ

/-- The even matrix power at the current iterate. -/
def powQ (s : SO) (u : Vec) : Mat :=
  matPow s.1 (shiftMat s.1 s.2.1 s.2.2.2.2.2.2 u) s.2.2.2.1 s.2.2.1

/-- One guarded subgradient step on `(u, P)`. -/
def outerStep (s : SO) (d : Vec × ℚ) : Vec × ℚ :=
  (s.1.map (fun i => capQ s.2.2.2.2.1
      (gv d.1 i + s.2.2.2.2.2.1 -
        qfloor (s.2.2.2.2.2.1 * (s.1.length : ℚ) * gm (powQ s d.1) i i /
          diagSum s.1 (powQ s d.1)))),
   capQ s.2.2.2.2.1
      (d.2 + qfloor ((s.1.length : ℚ) * lapDot s.1 s.2.1 (powQ s d.1) /
        diagSum s.1 (powQ s d.1))))

/-- The numeric constants of the method. -/
structure Consts where
  cT : ℕ
  cH : ℕ
  cOm : ℕ
  cK : ℕ
  cth : ℕ
  cbI : ℕ
  cbO : ℕ

def rep (c : ℕ) : List Unit := List.replicate c ()

/-- A unit list of length `idx.length * l.length`. -/
def pw (idx : List ℕ) (l : List Unit) : List Unit := idx.flatMap (fun _ => l)

/-- Outer fuel, of length `cT * n^3`. -/
def fuelT (c : Consts) (idx : List ℕ) : List Unit := pw idx (pw idx (pw idx (rep c.cT)))

/-- Inner fuel, of length `cK * n^5` (this is `2K`). -/
def fuelK (c : Consts) (idx : List ℕ) : List Unit :=
  pw idx (pw idx (pw idx (pw idx (pw idx (rep c.cK)))))

/-- Inner size pad, of length `1 + 2K * (cbI + 8 n)`. -/
def padI (c : Consts) (idx : List ℕ) : List Unit :=
  () :: (fuelK c idx).flatMap (fun _ => rep c.cbI ++ pw idx (rep 8))

/-- Outer size pad, of length `cbO + 1 + 9 n`. -/
def padO (c : Consts) (idx : List ℕ) : List Unit := rep (c.cbO + 1) ++ pw idx (rep 9)

def nq (idx : List ℕ) : ℚ := (idx.length : ℚ)

/-- Step size `η = cH n^3`. -/
def etaQ (c : Consts) (idx : List ℕ) : ℚ := (c.cH : ℚ) * (nq idx * nq idx * nq idx)

/-- Shift `σ = cT cH n^7`. -/
def sigQ (c : Consts) (idx : List ℕ) : ℚ :=
  (c.cT : ℚ) * (c.cH : ℚ) *
    (nq idx * nq idx * nq idx * nq idx * nq idx * nq idx * nq idx)

/-- Weight scale `Ω = cOm n^5`. -/
def omQ (c : Consts) (idx : List ℕ) : ℚ :=
  (c.cOm : ℚ) * (nq idx * nq idx * nq idx * nq idx * nq idx)

def TQ (c : Consts) (idx : List ℕ) : ℚ := ((fuelT c idx).length : ℚ)

/-- The weight between vertices `i` and `j`, read off the edge list. -/
def edgeW (xs : List NumericEdge) (i j : ℕ) : ℚ :=
  (xs.map (fun e =>
    if (decide (e.1.1 = i) && decide (e.1.2 = j)) || (decide (e.1.1 = j) && decide (e.1.2 = i))
    then e.2 else 0)).sum

/-- Scaled and rounded-down weights. -/
def scaledN (c : Consts) (idx : List ℕ) (xs : List NumericEdge) (i j : ℕ) : ℚ :=
  qfloor (omQ c idx * edgeW xs i j / edgeWeightSum xs)

/-- The integer Laplacian of the scaled weights, as a list matrix. -/
def lapList (c : Consts) (idx : List ℕ) (xs : List NumericEdge) : Mat :=
  idx.map (fun i => idx.map (fun j =>
    if i = j then (idx.map (fun k => scaledN c idx xs i k)).sum else -scaledN c idx xs i j))

def staticO (c : Consts) (idx : List ℕ) (xs : List NumericEdge) : SO :=
  (idx, lapList c idx xs, fuelK c idx, padI c idx, padO c idx, etaQ c idx, sigQ c idx)

/-- The final `(u, P)` after the outer loop. -/
def runO (c : Consts) (idx : List ℕ) (xs : List NumericEdge) : Vec × ℚ :=
  (gfold outerStep (fuelT c idx) (staticO c idx xs, (idx.map (fun _ => (0 : ℚ)), (0 : ℚ)))).2

/-- The primal feasibility check on the final iterate. -/
def checkOK (c : Consts) (idx : List ℕ) (u : Vec) : Bool :=
  (idx.filter (fun i =>
    decide (etaQ c idx * TQ c idx < (c.cth : ℚ) * (TQ c idx - gv u i)))).isEmpty

def rawVal (c : Consts) (idx : List ℕ) (xs : List NumericEdge) : ℚ :=
  (edgeWeightSum xs / omQ c idx) *
    ((runO c idx xs).2 * (c.cth : ℚ) / (TQ c idx * ((c.cth : ℚ) + 1))) / 4

/-- The lower value, from the vertex index list and the edge list. -/
def solveCore (c : Consts) (idx : List ℕ) (xs : List NumericEdge) : ℚ :=
  if edgeWeightSum xs = 0 then 0
  else if checkOK c idx (runO c idx xs).1 then
    (if rawVal c idx xs < 0 then 0 else rawVal c idx xs)
  else 0

/-- The lower value, from the raw request bits. -/
def solveRaw (c : Consts) (bits : List Bool) : ℚ :=
  solveCore c (parserVertices bits) (parseEdges bits)

end QMCSub


