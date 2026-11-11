-- Prove2me | Definitions.Def_ShortestPlanarDisjoint_Main_Configuration
-- name    : ShortestPlanarDisjoint_Main_Configuration
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:37:47.159028+00:00
-- url     : https://prove2.me/theorems/42b0741e-ac33-4348-b3a3-713bbd832ba7
-- title:
--   Graph configurations, port matrix and matching projection
-- statement:
--   A graph configuration assigns multiplicity zero, one or two to each unordered edge, zero to nonedges, degree one to each terminal and degree zero or two to each nonterminal. Thus its nontrivial components are exactly vertex-disjoint terminal paths, simple cycles and doubled edges. No prescribed pairing is imposed on configurations. Canonical traversals of multiplicity-one components extract their actual ordered edge words; doubled edges have signature factor one. The cost sums multiplicity times edge cost.
--
--   One port at each terminal and two at every nonterminal index the matrix K. An unused nonterminal has internal block J. An edge block is z^ell times E_u^T J T_uv E_v, where terminal columns are (t_i,1)^T and other columns are the two coordinate vectors. The reverse block is its transpose. Transports are actual ordered products of crossing matrices, with reversal reversing the word and the crossing direction. Perfect matchings project by counting external port pairs on each primal edge. The matching-weight product and projection predicate are defined independently of the port-expansion theorem. Empty port sets and configurations retain their empty products.
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Section 5.3, equation (8), p. 21 (PDF p. 23)

import Definitions.Def_ShortestPlanarDisjoint_Main_Linkage
import Definitions.Def_ShortestPlanarDisjoint_Main_SignatureAlgebra
import Definitions.Def_ShortestPlanarDisjoint_Main_Pfaffian

set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main
noncomputable section

def RoutingInput.terminalLabel {n k : ℕ} (I : RoutingInput n k) (v : Fin n) : Option (Fin (2*k)) := by
  classical
  exact (List.finRange (2*k)).find? fun i => I.terminal i = v

/-- Edge multiplicities determine an unoriented configuration uniquely. Terminal
degree is one; every other degree is zero or two. Multiplicity two represents a
doubled edge. No pairing or minimum-cost condition is built in. -/
structure GraphConfiguration {n k : ℕ} (I : RoutingInput n k) where
  multiplicity : Sym2 (Fin n) → Fin 3
  nonedges : ∀ e, e ∉ I.graph.edgeSet → multiplicity e = 0
  degree : ∀ v,
    let d := ∑ u : Fin n, (multiplicity s(v,u)).val
    if I.terminalLabel v = none then d = 0 ∨ d = 2 else d = 1

instance {n k : ℕ} (I : RoutingInput n k) : Fintype (GraphConfiguration I) := by
  classical
  apply Fintype.ofInjective GraphConfiguration.multiplicity
  intro C D h
  cases C; cases D; cases h; rfl

namespace GraphConfiguration
variable {n k : ℕ} {I : RoutingInput n k}

def singleGraph (C : GraphConfiguration I) : SimpleGraph (Fin n) :=
  I.graph.deleteEdges {e | C.multiplicity e ≠ 1}

def componentWalk (C : GraphConfiguration I) (start : Fin n) :
    ℕ → Option (Fin n) → Fin n → List (Fin n)
  | 0, _, _ => []
  | t + 1, previous, current => by
    classical
    exact current ::
      (if previous.isSome && (I.terminalLabel current).isSome then [] else
        match (List.finRange n).find? (fun u =>
          C.multiplicity s(current,u) = 1 ∧ previous ≠ some u) with
        | none => []
        | some u => if u = start then [u]
          else C.componentWalk start t (some current) u)

def vertexWalk (C : GraphConfiguration I) (v : Fin n) : List (Fin n) :=
  C.componentWalk v (n+1) none v

def cost (C : GraphConfiguration I) (ell : Sym2 (Fin n) → ℕ) : ℕ :=
  ∑ e : I.Edge, (C.multiplicity e.val).val * ell e.val

end GraphConfiguration

/-- Crossing lists for a canonical orientation of each primal edge. Reversal is
computed, not assumed; every reverse crossing uses the inverse crossing matrix. -/
abbrev EdgeWords (n r : ℕ) := Sym2 (Fin n) → List (Fin r × Bool)

def orientedEdgeWord {n r : ℕ} (words : EdgeWords n r) (u v : Fin n) : List (Fin r × Bool) :=
  if u < v then words s(u,v) else (words s(u,v)).reverse.map fun c => (c.1, !c.2)

def walkWord {n r : ℕ} (words : EdgeWords n r) (vertices : List (Fin n)) :
    List (Fin r × Bool) :=
  (vertices.zip vertices.tail).flatMap fun uv => orientedEdgeWord words uv.1 uv.2

def GraphConfiguration.words {n k r : ℕ} {I : RoutingInput n k}
    (C : GraphConfiguration I) (words : EdgeWords n r) : CurveWords k r := by
  classical
  exact {
    paths := (List.finRange (2*k)).filterMap fun i =>
      let vertices := C.vertexWalk (I.terminal i)
      match vertices.getLast? >>= I.terminalLabel with
      | none => none
      | some j => if i < j then some (i,j,walkWord words vertices) else none
    cycles := ((List.finRange n).filter fun v =>
      (∃ u, C.multiplicity s(v,u) = 1) ∧
      (∀ i, ¬ C.singleGraph.Reachable v (I.terminal i)) ∧
      (∀ u, C.singleGraph.Reachable v u → v ≤ u)).map fun v =>
        walkWord words (C.vertexWalk v) }

def GraphConfiguration.signature {n k r : ℕ} {I : RoutingInput n k}
    (C : GraphConfiguration I) (words : EdgeWords n r) : SignatureRing k r :=
  curveSignature (C.words words)

/-- One port at a terminal, two elsewhere. -/
def GraphPort {n k : ℕ} (I : RoutingInput n k) :=
  {p : Fin n × Fin 2 // I.terminalLabel p.1 = none ∨ p.2 = 0}

instance {n k : ℕ} (I : RoutingInput n k) : Fintype (GraphPort I) := by
  unfold GraphPort
  exact Fintype.ofFinite _

def GraphPort.vector {n k r : ℕ} {I : RoutingInput n k} (p : GraphPort I) : Vec2 (SignatureRing k r) :=
  match I.terminalLabel p.val.1 with
  | none => portVector p.val.2
  | some i => terminalVector (terminalVariable i)

def indexedPort {n k : ℕ} (I : RoutingInput n k)
    (i : Fin (Fintype.card (GraphPort I))) : GraphPort I := (Fintype.equivFin (GraphPort I)).symm i

def portMatrix {n k r : ℕ} (I : RoutingInput n k) (words : EdgeWords n r)
    (ell : Sym2 (Fin n) → ℕ) :
    Matrix (Fin (Fintype.card (GraphPort I))) (Fin (Fintype.card (GraphPort I)))
      (Polynomial (SignatureRing k r)) := by
  classical
  exact fun i j =>
    let p := indexedPort I i
    let q := indexedPort I j
    let u := p.val.1
    let v := q.val.1
    if u = v then if p.val.2 ≠ q.val.2 then 1 else 0 else
    if I.graph.Adj u v then
      Polynomial.monomial (ell s(u,v))
        (if u < v then bracket p.vector ((crossingTransport (words s(u,v))).mulVec q.vector)
          else bracket q.vector ((crossingTransport (words s(u,v))).mulVec p.vector))
    else 0

def portMatchingWeight {n k r : ℕ} (I : RoutingInput n k) (words : EdgeWords n r)
    (ell : Sym2 (Fin n) → ℕ) (p : IndexMatching (Fintype.card (GraphPort I))) :
    Polynomial (SignatureRing k r) := by
  classical
  exact ∏ i ∈ Finset.univ.filter (fun i => i < p.val i), portMatrix I words ell i (p.val i)

def projectsTo {n k : ℕ} {I : RoutingInput n k}
    (p : IndexMatching (Fintype.card (GraphPort I))) (C : GraphConfiguration I) : Prop :=
  ∀ e : Sym2 (Fin n), (C.multiplicity e).val =
    (Finset.univ.filter (fun i => i < p.val i ∧
      (indexedPort I i).val.1 ≠ (indexedPort I (p.val i)).val.1 ∧
      s((indexedPort I i).val.1, (indexedPort I (p.val i)).val.1) = e)).card

instance {n k : ℕ} {I : RoutingInput n k}
    (p : IndexMatching (Fintype.card (GraphPort I))) (C : GraphConfiguration I) :
    Decidable (projectsTo p C) := Classical.propDecidable _

instance {k r : ℕ} : CharP (SignatureRing k r) 2 :=
  CharP.of_ringHom_of_ne_zero (algebraMap (ZMod 2) (SignatureRing k r)) 2 (by decide)

end
end ShortestPlanarDisjoint.Main


