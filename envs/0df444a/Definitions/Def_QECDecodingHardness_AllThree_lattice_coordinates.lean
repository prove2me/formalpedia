-- Prove2me | Definitions.Def_QECDecodingHardness_AllThree_lattice_coordinates
-- name    : QECDecodingHardness_AllThree_lattice_coordinates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:49.467936+00:00
-- url     : https://prove2.me/theorems/5f896768-8803-4c5a-ba0f-dc295b53686a
-- title:
--   Finite triangular color-code and relative square-lattice coordinates
-- statement:
--   Integer pairs (u,v) label vertices of a triangular lattice. Its elementary triangles are the two orientations with vertices (u,v),(u+1,v),(u,v+1) and (u+1,v),(u,v+1),(u+1,v+1). For color-code order k, the stabilizer vertices satisfy
--
--   $$u-v\le k,\qquad u+2v\le k+1,\qquad -2u-v\le k-1.$$
--
--   For k>0 the qubits are the triangles incident to at least two such vertices, together with the three tip triangles based at (-1,-k), (-k,k), and (k,-1) in the second orientation. This gives the three colored stair-step boundaries of Figure 12; other boundary vertices carry no stabilizers. Order zero is the one-qubit, no-check patch.
--
--   For a positive square-lattice size L, coordinates range over the L by L square cellulation. Left and right are rough boundaries: their vertices carry no X checks and their vertical boundary edges carry no qubits. Faces carry Z checks, and top and bottom are smooth. Edge–vertex and edge–face incidence are computed from endpoints and the four sides of a unit face.
--
--   These coordinate enumerations provide finite code families of unbounded size, rather than arbitrary parity-check matrices. Lexicographic integer-box enumeration fixes their machine representation.
-- source:
--   Shouzhen (Bailey) Gu, Lily Wang, Aleksander Kubica, STOC 2027 submission #745 (October 2026), pp.3–4, Section II.1–2; p.6, boundary convention; p.18, Figure 12(a)(b)

import Definitions.Def_QECDecodingHardness_AllThree_check_system

namespace QECDecodingHardness.AllThree

abbrev Point := ℤ × ℤ
/-- An up/down elementary triangle with southwest integer coordinate. -/
abbrev Triangle := Bool × Point

def triangleVertices (t : Triangle) : Finset Point :=
  let u := t.2.1
  let v := t.2.2
  if t.1 then {(u + 1, v), (u, v + 1), (u + 1, v + 1)}
  else {(u, v), (u + 1, v), (u, v + 1)}

/-- Canonical lexicographic enumeration of an integer box. -/
def integerBox (lo hi : ℤ) : List Point :=
  (List.range (hi - lo).toNat).flatMap (fun i =>
    (List.range (hi - lo).toNat).map (fun j => (lo + (i : ℤ), lo + (j : ℤ))))

/-- Check vertices of the triangular hexagonal color-code patch of distance 2k+1.
The three offset halfplanes implement the three colored stair-step boundaries
in Fig.12(a)(b), p.18. `k=0` is the single-qubit patch with no checks. -/
def inColorChecks (k : ℕ) (p : Point) : Prop :=
  p.1 - p.2 ≤ (k : ℤ) ∧ p.1 + 2 * p.2 ≤ (k : ℤ) + 1 ∧
    -2 * p.1 - p.2 ≤ (k : ℤ) - 1

instance (k : ℕ) (p : Point) : Decidable (inColorChecks k p) := by
  unfold inColorChecks
  infer_instance

def colorChecks (k : ℕ) : List Point :=
  (integerBox (-((k : ℤ) + 2)) ((k : ℤ) + 3)).filter (fun p => decide (inColorChecks k p))

/-- All triangles incident to at least two check vertices, and the three tip
triangles incident to one check. Boundary vertices outside `colorChecks` do not
carry stabilizers. This avoids imposing spurious odd-weight boundary checks. -/
def inColorQubits (k : ℕ) (t : Triangle) : Prop :=
  if k = 0 then t = (false, (0, 0)) else
    2 ≤ ((triangleVertices t).filter (inColorChecks k)).card ∨
    t = (true, (-1, -(k : ℤ))) ∨
    t = (true, (-(k : ℤ), (k : ℤ))) ∨
    t = (true, ((k : ℤ), -1))

instance (k : ℕ) (t : Triangle) : Decidable (inColorQubits k t) := by
  unfold inColorQubits
  infer_instance

def colorQubits (k : ℕ) : List Triangle :=
  ([false, true] : List Bool).flatMap (fun b =>
    ((integerBox (-((k : ℤ) + 2)) ((k : ℤ) + 3)).map (fun p => (b, p))).filter
      (fun t => decide (inColorQubits k t)))

/-- A horizontal (`false`) or vertical (`true`) unit square-lattice edge. -/
abbrev SquareEdge := Bool × (ℕ × ℕ)
abbrev SquareVertex := ℕ × ℕ
abbrev SquareFace := ℕ × ℕ

def squareVertices (L : ℕ) : List SquareVertex :=
  (List.range (L + 1)).flatMap (fun x => (List.range (L + 1)).map (fun y => (x, y)))

/-- Relative square cellulation: the left/right sides are rough boundaries.
They carry no X checks; their vertical edges carry no qubits. Top/bottom are
smooth. The `L×L` lattice is finite and has an arbitrarily large bulk. -/
def surfaceXChecks (L : ℕ) : List SquareVertex :=
  (squareVertices L).filter (fun v => decide (0 < v.1 ∧ v.1 < L))

def surfaceZChecks (L : ℕ) : List SquareFace :=
  (List.range L).flatMap (fun x => (List.range L).map (fun y => (x, y)))

def surfaceQubits (L : ℕ) : List SquareEdge :=
  ((List.range L).flatMap (fun x =>
    (List.range (L + 1)).map (fun y => (false, (x, y))))) ++
  ((List.range (L + 1)).flatMap (fun x =>
    if 0 < x ∧ x < L then (List.range L).map (fun y => (true, (x, y))) else []))

def edgeAtVertex (v : SquareVertex) (e : SquareEdge) : Prop :=
  if e.1 then v = e.2 ∨ v = (e.2.1, e.2.2 + 1)
  else v = e.2 ∨ v = (e.2.1 + 1, e.2.2)

def edgeAtFace (f : SquareFace) (e : SquareEdge) : Prop :=
  if e.1 then e.2 = f ∨ e.2 = (f.1 + 1, f.2)
  else e.2 = f ∨ e.2 = (f.1, f.2 + 1)

instance (v : SquareVertex) (e : SquareEdge) : Decidable (edgeAtVertex v e) := by
  unfold edgeAtVertex
  infer_instance

instance (f : SquareFace) (e : SquareEdge) : Decidable (edgeAtFace f e) := by
  unfold edgeAtFace
  infer_instance

end QECDecodingHardness.AllThree


