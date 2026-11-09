-- Prove2me | Definitions.Def_MultipleUnicast_Counterexample_Graph
-- name    : MultipleUnicast_Counterexample_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:18:37.715767+00:00
-- url     : https://prove2.me/theorems/696028bb-8444-4aa1-a468-1cb3c273863d
-- title:
--   Ordered F9 incidence graph and the Appendix A causal instance
-- statement:
--   The field is $\mathbb F_9=\mathbb F_3[\theta]/(\theta^2+1)$, with the source's order $\eta_r=(r\bmod3)+\lfloor r/3\rfloor\theta$. The normalized triples, in their prescribed order, index the 91 point vertices and 91 line vertices. An incidence edge joins triples with dot product zero. The edge list is increasing first in point index and then in line index.
--
--   Appendix A's exact deleted set $R$ and vertex list $\pi$, and §4's sets $C,J$, define
--   $$B=R\setminus(C\cup J),\qquad E(G)=E(H)\setminus R.$$
--   For each session in $B$, its source is the earlier endpoint and its destination the later endpoint in $\pi$. The artificial orientation directs physical edges earlier to later and deleted edges later to earlier. Degrees count this full oriented candidate graph, while physical adjacency contains only undeleted edges.
--
--   This file fixes the finite data for every subsequent item. No permutation, cardinality, balanced-degree or successful-communication assertion is a field of the data.
--
--   **Formalization Note** The quadratic algebra implements the exact quotient presentation, with its field instance justified by the absence of roots of $X^2+1$ over $\mathbb F_3$. Vertex and edge labels use `Fin 182` and `Fin 910`. List lookups have explicit total defaults; the source's list-length, uniqueness and permutation facts are conclusions of the orientation item.
-- source:
--   Mark Braverman, Zhongtian He, STOC 2027 submission #286 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/286.pdf, §3, PDF pp. 5–6 / printed pp. 4–5; §4, PDF pp. 10–11 / printed pp. 9–10; Appendix A, PDF pp. 14–15 / printed pp. 13–14

import Mathlib
set_option maxRecDepth 2048

namespace MultipleUnicast.Counterexample

/-- The quadratic presentation F₃[θ]/(θ²+1), not Z/9Z. -/
abbrev F9 := QuadraticAlgebra (ZMod 3) (-1) 0
instance fieldPolynomial : Fact (∀ r : ZMod 3, r ^ 2 ≠ -1 + 0 * r) := ⟨by decide⟩
instance : Fintype F9 := Fintype.ofEquiv (ZMod 3 × ZMod 3)
  (QuadraticAlgebra.equivProd (-1) 0).symm

def theta : F9 := ⟨0, 1⟩
def eta (r : ℕ) : F9 := ⟨(r % 3 : ℕ), (r / 3 : ℕ)⟩
abbrev Vertex := Fin 182
abbrev Edge := Fin 910
abbrev Triple := Fin 3 → F9

def triple (i : Fin 91) : Triple :=
  if i.val = 0 then ![0, 0, 1]
  else if i.val < 10 then ![0, 1, eta (i.val - 1)]
  else ![1, eta ((i.val - 10) / 9), eta ((i.val - 10) % 9)]

def dot (x y : Triple) : F9 := ∑ r, x r * y r

/-- Lexicographic edge order: increasing point, then increasing line. -/
def incidenceList : List (Fin 91 × Fin 91) :=
  (List.finRange 91).flatMap fun i =>
    ((List.finRange 91).filter fun j => dot (triple i) (triple j) = 0).map (i, ·)

def edgePair (q : Edge) : Fin 91 × Fin 91 := incidenceList.getD q.val (0, 0)
def pointEnd (q : Edge) : Vertex := ⟨(edgePair q).1.val, by omega⟩
def lineEnd (q : Edge) : Vertex := ⟨91 + (edgePair q).2.val, by omega⟩
def incident (v : Vertex) (q : Edge) : Prop := v = pointEnd q ∨ v = lineEnd q
instance (v : Vertex) (q : Edge) : Decidable (incident v q) := inferInstanceAs (Decidable (_ ∨ _))

def deleted : Finset Edge := {7, 8, 9, 30, 31, 38, 39, 56, 57, 60, 68, 75, 79, 84, 88, 94, 102, 103, 117, 122, 127, 128, 141, 151, 154, 155, 157, 163, 164, 166, 167, 168, 176, 179, 183, 187, 203, 207, 208, 212, 215, 221, 224, 225, 231, 234, 236, 237, 238, 242, 243, 251, 253, 266, 282, 290, 300, 309, 318, 321, 324, 325, 330, 333, 338, 341, 349, 380, 386, 387, 389, 396, 398, 400, 401, 406, 407, 409, 411, 412, 418, 425, 426, 428, 439, 444, 454, 458, 464, 465, 468, 470, 476, 480, 481, 492, 502, 503, 504, 513, 517, 521, 522, 527, 539, 541, 544, 548, 552, 557, 559, 569, 579, 583, 585, 588, 592, 593, 598, 602, 603, 606, 607, 612, 619, 620, 632, 634, 643, 646, 670, 672, 673, 674, 682, 685, 688, 694, 695, 701, 702, 703, 709, 716, 718, 737, 746, 754, 757, 759, 773, 790, 821, 835, 837, 838, 839, 841, 842, 843, 846, 850, 853, 856, 857, 861, 862, 882, 884, 885, 887, 900, 901, 904, 907}

def processingOrder : List Vertex := [93, 23, 16, 143, 107, 54, 88, 38, 157, 40, 171, 124, 123, 118, 90, 32, 15, 146, 114, 179, 181, 39, 128, 0, 119, 83, 21, 6, 132, 160, 17, 79, 22, 42, 41, 174, 5, 167, 26, 96, 8, 61, 168, 101, 75, 43, 102, 127, 99, 12, 30, 57, 147, 92, 138, 159, 113, 31, 172, 7, 116, 78, 28, 126, 19, 120, 89, 117, 9, 14, 122, 56, 72, 115, 153, 47, 65, 103, 74, 137, 97, 10, 110, 154, 135, 95, 4, 125, 86, 139, 34, 162, 80, 87, 129, 27, 134, 140, 36, 13, 148, 149, 82, 37, 176, 91, 73, 1, 51, 141, 105, 109, 35, 44, 130, 66, 11, 98, 121, 25, 76, 169, 49, 53, 150, 2, 104, 29, 158, 69, 180, 81, 52, 106, 112, 131, 164, 63, 71, 170, 155, 24, 64, 156, 62, 48, 46, 145, 163, 45, 77, 175, 33, 142, 18, 178, 166, 144, 152, 55, 67, 70, 177, 85, 111, 20, 136, 84, 100, 58, 151, 68, 50, 133, 165, 94, 60, 173, 3, 59, 161, 108]

def C : Finset Edge := {102,163,164,341,386,406,476,513,862}
def J : Finset Edge := {103,349,470,517,603,606,674,716,861}
def B : Finset Edge := deleted \ (C ∪ J)
def physical : Finset Edge := Finset.univ \ deleted
abbrev Session := {q : Edge // q ∈ B}
def position (v : Vertex) : ℕ := processingOrder.idxOf v
def earlier (q : Edge) : Vertex :=
  if position (pointEnd q) < position (lineEnd q) then pointEnd q else lineEnd q
def later (q : Edge) : Vertex :=
  if position (pointEnd q) < position (lineEnd q) then lineEnd q else pointEnd q
/-- Artificial orientation on ALL candidate edges; deleted edges are reversed. -/
def tail (q : Edge) : Vertex := if q ∈ deleted then later q else earlier q
def head (q : Edge) : Vertex := if q ∈ deleted then earlier q else later q

def inDegree (S : Finset Edge) (v : Vertex) : ℕ := (S.filter (head · = v)).card
def outDegree (S : Finset Edge) (v : Vertex) : ℕ := (S.filter (tail · = v)).card

def physicalAdj (u v : Vertex) : Prop :=
  ∃ q ∈ physical, (u = pointEnd q ∧ v = lineEnd q) ∨ (u = lineEnd q ∧ v = pointEnd q)
instance (u v : Vertex) : Decidable (physicalAdj u v) := by unfold physicalAdj; infer_instance

def graph : SimpleGraph Vertex where
  Adj := physicalAdj
  symm := ⟨by
    intro u v h
    change physicalAdj u v at h
    rcases h with ⟨q,hq,h⟩
    exact ⟨q,hq,h.elim (fun h => Or.inr ⟨h.2,h.1⟩) (fun h => Or.inl ⟨h.2,h.1⟩)⟩⟩
  loopless := ⟨by
    intro v ⟨q,_,h⟩
    have hp := (edgePair q).1.isLt
    have hl := (edgePair q).2.isLt
    rcases h with ⟨a,b⟩ | ⟨b,a⟩ <;>
      have he := congrArg Fin.val (a.symm.trans b) <;>
      simp only [pointEnd, lineEnd] at he <;> omega⟩

end MultipleUnicast.Counterexample


