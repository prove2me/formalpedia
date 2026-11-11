-- Prove2me | Definitions.Def_ShortestPlanarDisjoint_Main_PortContributions
-- name    : ShortestPlanarDisjoint_Main_PortContributions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:06.724789+00:00
-- url     : https://prove2.me/theorems/854bb5ed-39e9-4677-9d06-71abdafa66ac
-- title:
--   Two-port component weights and ordered transport
-- statement:
--   For a commutative coefficient ring, let
--
--   $$J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
--   v(t)=(t,1)^T,\quad [u,v]=u^TJv.$$
--
--   A path with $h$ internal vertices has $h+1$ edge matrices in traversal order. At
--   each internal vertex choose an incoming port, either zero or one; its outgoing
--   port is the other. Insert the terminal vectors at the two ends and multiply the
--   edge-block factors $u^TJT_ev$. Summing over the $2^h$ internal assignments defines
--   the path contribution.
--
--   For a simple cycle of $h$ distinct vertices, choose the incoming port at every
--   vertex, switch to the other outgoing port, and multiply the corresponding edge
--   factors cyclically. Sum over all $2^h$ assignments. A fixed traversal represents
--   each assignment once, without summing again over the reverse direction. These
--   are explicit port sums, not definitions by their desired bracket/trace values.
--   The common cost monomial is omitted exactly as in Claims 1 and 2. A doubled edge
--   is a separate component and is not treated by the simple-cycle sum.
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Section 5.3, Claims 1 and 2 (cost-free local factors), p. 21 (PDF p. 23)

import Mathlib

set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main

abbrev Mat2 (R : Type*) := Matrix (Fin 2) (Fin 2) R
abbrev Vec2 (R : Type*) := Fin 2 → R

/-- The switch between the two ports at an internal vertex. -/
def switchMatrix (R : Type*) [Zero R] [One R] : Mat2 R := !![0, 1; 1, 0]

def terminalVector {R : Type*} [One R] (t : R) : Vec2 R := ![t, 1]

def portVector {R : Type*} [Zero R] [One R] (p : Fin 2) : Vec2 R :=
  fun i => if i = p then 1 else 0

def otherPort (p : Fin 2) : Fin 2 := ⟨1 - p.val, by omega⟩

def bracket {R : Type*} [CommRing R] (v w : Vec2 R) : R :=
  ∑ i, ∑ j, v i * switchMatrix R i j * w j

/-- The product is in edge traversal order; in particular the empty product is I₂. -/
def transport {R : Type*} [CommRing R] (ts : List (Mat2 R)) : Mat2 R := ts.prod

/-- An individual internal-port assignment for a path with h internal vertices
and h+1 graph edges. An assignment chooses the incoming port; the outgoing port
is the other one. The terminal vectors are inserted in the first and last edge. -/
def pathPortWeight {R : Type*} [CommRing R] {h : ℕ} (ts : Fin (h + 1) → Mat2 R)
    (vi vj : Vec2 R) (a : Fin h → Fin 2) : R :=
  ∏ e : Fin (h + 1),
    let left : Vec2 R := if hfirst : e.val = 0 then vi
      else portVector (otherPort (a ⟨e.val - 1, by omega⟩))
    let right : Vec2 R := if hlast : e.val < h then portVector (a ⟨e.val, hlast⟩)
      else vj
    bracket left ((ts e).mulVec right)

/-- The sum over the two possible incoming ports at every internal vertex. -/
def pathPortSum {R : Type*} [CommRing R] {h : ℕ} (ts : Fin (h + 1) → Mat2 R)
    (vi vj : Vec2 R) : R := ∑ a : Fin h → Fin 2, pathPortWeight ts vi vj a

/-- A cycle traversal distinguishes its h distinct edges. This is used for
simple cycles (h≥3), never for a doubled edge. -/
def cyclePortWeight {R : Type*} [CommRing R] {h : ℕ} (hh : 0 < h)
    (ts : Fin h → Mat2 R) (a : Fin h → Fin 2) : R :=
  ∏ e : Fin h,
    bracket (portVector (otherPort (a e)))
      ((ts e).mulVec (portVector (a ⟨(e.val + 1) % h, Nat.mod_lt _ hh⟩)))

def cyclePortSum {R : Type*} [CommRing R] {h : ℕ} (hh : 0 < h)
    (ts : Fin h → Mat2 R) : R :=
  ∑ a : Fin h → Fin 2, cyclePortWeight hh ts a

end ShortestPlanarDisjoint.Main


