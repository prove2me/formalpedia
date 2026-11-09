-- Prove2me | Definitions.Def_PfaffianRecognition_Recognition_polynomial_model
-- name    : PfaffianRecognition_Recognition_polynomial_model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T04:40:48.140199+00:00
-- url     : https://prove2.me/theorems/17e39302-2bb6-41aa-ad60-52fd211703d6
-- title:
--   Wrong-sign polynomial and vertex-deletion principal minors
-- statement:
--   Let $G$ be a finite simple ordered graph, $D$ an orientation, $F$ a fixed perfect matching and $K$ a coefficient ring. Assign an independent formal variable $x_e$ to each undirected graph edge. Define
--   $$
--   P_{D,F}(x)=\sum_{\substack{M\in\mathcal M(G)\\\operatorname{sign}_D(M)\ne\operatorname{sign}_D(F)}}\prod_{e\in M}x_e^2.
--   $$
--   The matrix $A_D$ has entry $x_{ij}$ on an arc $i\to j$, entry $-x_{ij}$ on the reverse arc, and zero on nonedges. Deleting an edge in a matrix expression deletes both endpoint rows and columns; deleting two crossing edges deletes their four distinct endpoints. Write $R_D$ for the backward edges, $C(G)$ for the unordered crossing pairs, and $s$ for the reference parity. The minor expression is
--   $$
--   s\det A_D+\sum_{e\in R_D}x_e^2\det(A_D-e)
--    +\sum_{\{e,f\}\in C(G)}x_e^2x_f^2\det(A_D-e-f).
--   $$
--   This bundle supplies the objects on the two sides of the paper's identity; their equality is a separate theorem. It also supplies formal polynomial equality for the zero-polynomial characterization.
--
--   **Formalization Note** The helpers are defined over commutative rings, while the theorems impose the paper's characteristic-two field hypotheses. Integer signs are computed before introducing $K$, where $-1=1$ in characteristic two. The reference matching remains an explicit parameter; theorem hypotheses require it to be perfect. Principal determinants are indexed by the complement of the deleted vertex set, including determinant 1 when the complement is empty. Zero is coefficientwise polynomial zero, not vanishing of every evaluation over a small field.
-- source:
--   Priyanshu Pant, Ranveer Singh, Pfaffian Recognition is in coRP, STOC 2027 submission #858 (October 2026), §1, p. 2; §2.2, pp. 5–6, equation (1); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/858.pdf

import Definitions.Def_PfaffianRecognition_Recognition_graph_model

noncomputable section

open scoped BigOperators

namespace PfaffianRecognition.Recognition

/-- Formal wrong-sign polynomial with one independent variable per undirected graph edge.
The reference matching F is explicit. Its validity is imposed at every theorem using this helper. -/
def wrongSignPolynomial {N : ℕ} {G : SimpleGraph (Fin N)} (K : Type*) [CommRing K]
    (D : Orientation G) (F : Finset G.edgeSet) : MvPolynomial G.edgeSet K := by
  classical
  exact ∑ M ∈ (MulmuleyVV.Matching.perfectMatchings G).filter
      (fun M => matchingSign D M ≠ matchingSign D F),
    ∏ e ∈ M, (MvPolynomial.X e : MvPolynomial G.edgeSet K) ^ 2

/-- Weighted skew-adjacency matrix over the formal polynomial ring. Signs remain meaningful
in this general definition even though the minor identity specializes to characteristic two. -/
def skewAdjacency {N : ℕ} {G : SimpleGraph (Fin N)} (K : Type*) [CommRing K]
    (D : Orientation G) : Matrix (Fin N) (Fin N) (MvPolynomial G.edgeSet K) := by
  classical
  exact fun i j => if h : G.Adj i j then
    let e : G.edgeSet := ⟨s(i, j), G.mem_edgeSet.mpr h⟩
    if D.val i j then MvPolynomial.X e else -MvPolynomial.X e
    else 0

/-- Delete all vertices in S from both row and column indices. The empty matrix has determinant 1. -/
def principalDet {N : ℕ} {G : SimpleGraph (Fin N)} (K : Type*) [CommRing K]
    (D : Orientation G) (S : Finset (Fin N)) : MvPolynomial G.edgeSet K := by
  classical
  exact ((skewAdjacency K D).submatrix
    (fun i : {v : Fin N // v ∉ S} => i.val)
    (fun i : {v : Fin N // v ∉ S} => i.val)).det

/-- Vertices removed by deleting an edge's two endpoints. -/
def edgeVertices {N : ℕ} {G : SimpleGraph (Fin N)} (e : G.edgeSet) : Finset (Fin N) :=
  {edgeLo e, edgeHi e}

/-- The determinant/principal-minor expression in §2.2, equation (1). Unordered crossing pairs
are counted once, and edge deletion always means vertex deletion in both rows and columns. -/
def minorExpression {N : ℕ} {G : SimpleGraph (Fin N)} (K : Type*) [CommRing K]
    (D : Orientation G) (F : Finset G.edgeSet) : MvPolynomial G.edgeSet K := by
  classical
  exact MvPolynomial.C (referenceParity D F : K) * (skewAdjacency K D).det +
    (∑ e ∈ backwardEdges D, (MvPolynomial.X e : MvPolynomial G.edgeSet K) ^ 2 *
      principalDet K D (edgeVertices e)) +
    ∑ ef ∈ crossingPairs G,
      (MvPolynomial.X ef.1 : MvPolynomial G.edgeSet K) ^ 2 * MvPolynomial.X ef.2 ^ 2 *
        principalDet K D (edgeVertices ef.1 ∪ edgeVertices ef.2)

end PfaffianRecognition.Recognition


