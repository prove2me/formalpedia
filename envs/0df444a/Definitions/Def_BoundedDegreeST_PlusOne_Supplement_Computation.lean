-- Prove2me | Definitions.Def_BoundedDegreeST_PlusOne_Supplement_Computation
-- name    : BoundedDegreeST_PlusOne_Supplement_Computation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:48:54.738786+00:00
-- url     : https://prove2.me/theorems/aa8d18e8-a4d9-445f-aed9-707b7bf23101
-- title:
--   Theorem 3.3 — binary rational inputs and effective LP and Figure 2 implementations
-- statement:
--   For the computational assertion, vertices are labelled $0,\ldots,n-1$. A rational input contains $n$, the surviving-vertex mask, the symmetric edge table, signed integer bounds, the constrained-vertex mask, and a symmetric table of rational costs. Naturals use binary digits in self-delimiting fields; integers add a sign, and rationals store the reduced numerator and positive denominator. Edge and vector tables have a fixed row-major order, including their diagonal.
--
--   An LP implementation is a function on bit strings that, for every well-formed LP-feasible rational residual input, outputs the exact binary encoding of some rational basic optimal vector. A Figure 2 implementation outputs the encoding of an edge set returned by the leaf algorithm on every feasible original input:
--
--   $$\operatorname{solve}(\operatorname{enc}(D))=\operatorname{enc}(x^*),\qquad \operatorname{run}(\operatorname{enc}(D))=\operatorname{enc}(H).$$
--
--   Theorem 3.3 separately requires both functions to have actual uniform polynomial-time Turing-machine realizations, using Mathlib's finite multi-stack machine semantics and transition-count bounds. Neither LP optimization nor the existence of either machine is assumed by these definitions.
--
--   **Formalization Note** Binary rational input gives the usual bit-complexity meaning of polynomial time. The correctness relation for arbitrary real costs is retained separately. No strongly polynomial real-arithmetic LP oracle is postulated; the LP implementation itself is part of the theorem's conclusion.
-- source:
--   Singh, Lau, Approximating minimum bounded degree spanning trees to within one of optimal, STOC 2007, DOI 10.1145/1250790.1250887, pp. 664–665, Theorem 3.3 and polynomial-time LP paragraph above Figure 2

import Definitions.Def_BoundedDegreeST_PlusOne_Supplement_LeafAlgorithm

namespace BoundedDegreeST.PlusOne.Supplement

/-- Finite, ordinary rational inputs for the bit-complexity assertion. Real-cost
correctness is a separate, unrestricted clause of Theorem 3.3. -/
structure RationalInput where
  n : ℕ
  alive : Finset (Fin n)
  E : Finset (Sym2 (Fin n))
  B : Fin n → ℤ
  W : Finset (Fin n)
  c : Sym2 (Fin n) → ℚ

def RationalInput.state (D : RationalInput) : LeafState (Fin D.n) :=
  ⟨D.alive, D.E, D.B, D.W, ∅⟩

def RationalInput.realCost (D : RationalInput) : Sym2 (Fin D.n) → ℝ :=
  fun e => (D.c e : ℝ)

/-- A self-delimiting field. Every payload bit is prefixed by one; zero ends it. -/
def field (bits : List Bool) : List Bool :=
  bits.flatMap (fun b => [true, b]) ++ [false]

/-- Binary integers and rational numerator/positive denominator, not unary magnitudes. -/
def encodeNat (n : ℕ) : List Bool := field n.bits

def encodeInt (z : ℤ) : List Bool :=
  decide (z < 0) :: encodeNat z.natAbs

def encodeRat (q : ℚ) : List Bool := encodeInt q.num ++ encodeNat q.den

/-- Dense symmetric n-by-n tables fix the edge ordering without a hidden
ordering oracle on unordered pairs. The diagonal is included in the encoding. -/
def encodeEdges {n : ℕ} (E : Finset (Sym2 (Fin n))) : List Bool :=
  (List.ofFn fun i : Fin n => List.ofFn fun j : Fin n => decide (s(i, j) ∈ E)).flatten

def encodeVector {n : ℕ} (q : Sym2 (Fin n) → ℚ) : List Bool :=
  (List.ofFn fun i : Fin n =>
    (List.ofFn fun j : Fin n => encodeRat (q s(i, j))).flatten).flatten

/-- The dimension, surviving vertices, graph, bounds, constrained vertices and
costs are all input data. There is one uniform machine for every dimension. -/
def RationalInput.encode (D : RationalInput) : List Bool :=
  encodeNat D.n ++
  List.ofFn (fun i : Fin D.n => decide (i ∈ D.alive)) ++
  encodeEdges D.E ++
  (List.ofFn fun i : Fin D.n => encodeInt (D.B i)).flatten ++
  List.ofFn (fun i : Fin D.n => decide (i ∈ D.W)) ++ encodeVector D.c

/-- An effective implementation of the LP solve itself. On every well-formed
feasible residual rational input its output is a rational basic optimal vector.
Polynomial running time is required separately, not assumed of an oracle. -/
def ImplementsLP (solve : List Bool → List Bool) : Prop :=
  ∀ D : RationalInput, WellFormed D.state →
    (∃ x, ResidualFeasible D.state x) →
    ∃ q : Sym2 (Fin D.n) → ℚ,
      solve D.encode = encodeVector q ∧
      ResidualBasic D.state (fun e => (q e : ℝ)) ∧
      ResidualOptimal D.realCost D.state (fun e => (q e : ℝ))

/-- The finite program returns an output of Figure 2, including the singleton
boundary, for every feasible rational MBDST instance. It does not merely output
an arbitrary tree meeting the numerical approximation bound. -/
def ImplementsFigureTwo (run : List Bool → List Bool) : Prop :=
  ∀ D : RationalInput, D.alive = Finset.univ → D.W = Finset.univ →
    SimpleEdges D.E → (∃ x, Feasible D.E D.B Finset.univ ∅ x) →
    ∃ H : Finset (Sym2 (Fin D.n)),
      run D.encode = encodeEdges H ∧ LeafReturns D.realCost (initial D.E D.B) H

end BoundedDegreeST.PlusOne.Supplement


