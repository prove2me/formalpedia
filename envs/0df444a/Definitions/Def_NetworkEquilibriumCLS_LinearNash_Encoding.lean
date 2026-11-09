-- Prove2me | Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding
-- name    : NetworkEquilibriumCLS_LinearNash_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:17:54.185271+00:00
-- url     : https://prove2.me/theorems/37c62287-d603-4d6e-8ed7-fddc725cb862
-- title:
--   Binary input codes and exact rational search relations
-- statement:
--   All instances are explicit finite lists. A natural number uses a unary prefix for the length of its binary digits followed by those digits; this prefix is logarithmic in the number. Integers carry a sign, rationals carry their reduced signed numerator and positive denominator, and lists carry their length. Matrices and vectors use deterministic index order. Network codes contain vertex lists, edge endpoints and coefficients, and the terminal pair of every player. Coordination codes contain player lists and their present edges with four rational payoff entries. No normal-form path table is included.
--
--   Quadratic and bilinear answers are rational vectors satisfying exact box KKT. Coordination answers are rational vectors satisfying exact Nash. A network answer gives every player a list of simple edge paths with nonnegative rational probabilities summing to one; repeated entries are combined when forming the mixed profile. Every feasible path remains a possible deviation.
--
--   For any encoded search relation S and one fixed natural exponent k, its bounded version accepts exactly the same solutions whose total bit length satisfies
--
--   $$|y|\le (|x|+1)^k+k.$$
--
--   Existence of a suitable k is asserted in the classification theorems. It is never an input promise, and cannot depend on an instance. This bounds support size and all probability encodings together. The DAG search restricts only the valid network inputs to acyclic networks without parallel edges. Published all-answer search reductions and actual polynomial-time machine computations are reused unchanged.
-- source:
--   Ioannis Anagnostides, Ioannis Panageas, Jingming Yan, STOC 2027 submission #653 (October 2026), p.2 (PDF 3), §1.1 input/output conventions; p.6 (PDF 7), §2 reduction convention; p.14 (PDF 15), Theorem 5.1. Binary layout is an explicit encoding convention.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Games
import Definitions.Def_CardinalMatching_SearchReduces

open Finset

noncomputable section

namespace NetworkEquilibriumCLS.LinearNash

/-- Self-delimiting binary natural, followed by data; prefix length is logarithmic. -/
def encNat (n : ℕ) : List Bool := List.replicate n.bits.length true ++ false :: n.bits

def encInt (z : ℤ) : List Bool := (z < 0) :: encNat z.natAbs

def encRat (r : ℚ) : List Bool := encInt r.num ++ encNat r.den

def encList {α : Type*} (f : α → List Bool) (xs : List α) : List Bool :=
  encNat xs.length ++ xs.flatMap f

def encVector {n : ℕ} (x : Fin n → ℚ) : List Bool := encList encRat (List.ofFn x)

def encQuadratic {m : ℕ} (p : Quadratic m) : List Bool :=
  encNat m ++ encList (encList encRat) (List.ofFn (fun i => List.ofFn (p.Q i))) ++ encVector p.c

def encBoolean {n : ℕ} (h : BooleanPolynomial n) : List Bool :=
  encNat n ++ encList encInt (List.ofFn h.beta) ++
    encList (encList encInt) (List.ofFn (fun i => List.ofFn (h.weight i)))

def encCoordination {N : ℕ} (G : Coordination N) : List Bool :=
  encList encNat (List.range N) ++ encList (fun ij : Fin N × Fin N =>
    encNat ij.1.val ++ encNat ij.2.val ++
      encList encRat [G.payoff ij.1 ij.2 false false, G.payoff ij.1 ij.2 false true,
        G.payoff ij.1 ij.2 true false, G.payoff ij.1 ij.2 true true])
    ((List.finRange N).flatMap fun i =>
      ((List.finRange N).filter (fun j => i < j ∧ G.edge i j = true)).map (i, ·))

def encNetwork (G : Network) : List Bool :=
  encList encNat (List.range G.vertices) ++
    encList (fun e => encNat (G.tail e).val ++ encNat (G.head e).val ++ encRat (G.alpha e))
      (List.finRange G.edges) ++
    encList (fun i => encNat (G.source i).val ++ encNat (G.sink i).val) (List.finRange G.players)

abbrev SparseAnswer (G : Network) := Fin G.players → List (List ℕ × ℚ)

def encSparseAnswer (G : Network) (a : SparseAnswer G) : List Bool :=
  encList (encList (fun e => encList encNat e.1 ++ encRat e.2)) (List.ofFn a)

def listEdgeSet (G : Network) (es : List ℕ) : Finset (Fin G.edges) :=
  univ.filter (fun e => e.val ∈ es)

def PathListValid (G : Network) (i : Fin G.players) (es : List ℕ) : Prop :=
  ∃ ps : List (Fin G.edges), ps.map Fin.val = es ∧ IsPath G i ps

def sparseProfile (G : Network) (a : SparseAnswer G) (i : Fin G.players)
    (P : PathAction G i) : ℝ :=
  ((a i).filter (fun entry => listEdgeSet G entry.1 = P.val)).foldl
    (fun sum entry => sum + (entry.2 : ℝ)) 0

def SparseAnswerValid (G : Network) (a : SparseAnswer G) : Prop :=
  (∀ i, (∀ entry ∈ a i, PathListValid G i entry.1 ∧ 0 ≤ entry.2) ∧
    ((a i).map Prod.snd).sum = 1) ∧ NetworkNash G (sparseProfile G a)

abbrev SearchProblem := TetrisHard.Rows.SearchProblem
abbrev SearchReduces := CardinalMatching.SearchReduces
abbrev PolyTime {A B : Type} (f : List A → List B) := CookPvsNP.PolyTimeComputable f

def quadraticSearch : SearchProblem where
  valid x := ∃ m, 0 < m ∧ ∃ p : Quadratic m, encQuadratic p = x
  answer x y := ∃ m, 0 < m ∧ ∃ p : Quadratic m, encQuadratic p = x ∧
    ∃ z : Fin m → ℚ, encVector z = y ∧ QuadraticKKT p (fun i => (z i : ℝ))

def bilinearSearch : SearchProblem where
  valid x := ∃ m, 0 < m ∧ ∃ p : Quadratic m, IsBilinear p ∧ encQuadratic p = x
  answer x y := quadraticSearch.answer x y

def coordinationSearch : SearchProblem where
  valid x := ∃ N, 0 < N ∧ ∃ G : Coordination N, CoordinationValid G ∧ encCoordination G = x
  answer x y := ∃ N, 0 < N ∧ ∃ G : Coordination N, CoordinationValid G ∧ encCoordination G = x ∧
    ∃ z : Fin N → ℚ, encVector z = y ∧ CoordinationNash G (fun i => (z i : ℝ))

def networkSearch : SearchProblem where
  valid x := ∃ G, NetworkValid G ∧ encNetwork G = x
  answer x y := ∃ G, NetworkValid G ∧ encNetwork G = x ∧
    ∃ a : SparseAnswer G, encSparseAnswer G a = y ∧ SparseAnswerValid G a

def dagSearch : SearchProblem where
  valid x := ∃ G, NetworkValid G ∧ NetworkDAG G ∧ NetworkSimple G ∧ encNetwork G = x
  answer x y := networkSearch.answer x y

/-- One uniform exponent, chosen before the instance. It bounds support, probabilities and all bits. -/
def bounded (S : SearchProblem) (k : ℕ) : SearchProblem where
  valid := S.valid
  answer x y := S.answer x y ∧ y.length ≤ (x.length + 1)^k + k

/-- Rational approximate answers to one fixed quadratic instance and tolerance. -/
def approxAnswers {m : ℕ} (p : Quadratic m) (ε : ℚ) (y : List Bool) : Prop :=
  ∃ z : Fin m → ℚ, encVector z = y ∧ ApproxQuadraticKKT p (ε : ℝ) (fun i => (z i : ℝ))

/-- Tagged source/answer pair, the published reduction interface. -/
def pairCode (x y : List Bool) : List (Option (Bool ⊕ Bool)) :=
  x.map (some ∘ Sum.inl) ++ none :: y.map (some ∘ Sum.inr)

end NetworkEquilibriumCLS.LinearNash


