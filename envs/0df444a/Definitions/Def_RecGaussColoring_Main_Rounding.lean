-- Prove2me | Definitions.Def_RecGaussColoring_Main_Rounding
-- name    : RecGaussColoring_Main_Rounding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:24:20.434796+00:00
-- url     : https://prove2.me/theorems/fc09986a-7874-41b9-8e86-dfb50f46095c
-- title:
--   Strict vector colorings and arbitrary-selector KMS′ rounding
-- statement:
--   For a graph $G$ on $n$ vertices and any dimension $d$, a strict vector three-coloring assigns vectors $v_i\in\mathbb R^d$ with $\|v_i\|=1$ and $\langle v_i,v_j\rangle=-1/2$ on every edge. Define $u_{j\mid i}=(2/\sqrt3)(v_j+v_i/2)$. For threshold $t$ and standard Gaussian $\gamma$, KMS′ selects $S=\{i:\langle\gamma,v_i\rangle\ge t\}$. A matching selector maps every vertex set $S$ to an inclusion-maximal matching $M(S)$ of the induced graph $G[S]$. Its output is $I=S\setminus V(M(S))$, with expectation
--   $$
--   \mathbb E|I|=\sum_{S\subseteq V}\Pr[\{i:\langle\gamma,v_i\rangle\ge t\}=S]\,|S\setminus V(M(S))|.
--   $$
--   The local-cover predicate on an induced vertex set $W$ requires $\{u_{j\mid i}:j\in W,\ ij\in E\}$ to be a $(\sqrt3t,1/8)$-cover for each $i\in W$.
--
--   This is the actual rounding procedure. Matching validity is independent of the output guarantee, and every selector remains available to the theorem quantifiers.
-- source:
--   Ijay Narang, Yukai Tang, STOC 2027 submission #295 (October 2026), §1.1, Algorithm 2, (1.1); Lemma 1.3, p. 4, p. 3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/295.pdf

import Definitions.Def_RecGaussColoring_Main_Gaussian
import Definitions.Def_RecGaussColoring_Main_Graph

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
noncomputable section

namespace RecGaussColoring.Main

/-- Strict vector coloring from §1.1; all dimensions, including zero, are allowed. -/
def StrictVectorColoring {n d : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n → Space d) : Prop :=
  (∀ i, ‖v i‖ = 1) ∧ ∀ i j, G.Adj i j → ⟪v i, v j⟫ = -(1/2 : ℝ)

/-- Explicit edge direction from (1.1); its norm and orthogonality are not assumptions. -/
def edgeDirection {n d : ℕ} (v : Fin n → Space d) (j i : Fin n) : Space d :=
  (2 / Real.sqrt 3) • (v j + (1/2 : ℝ) • v i)

/-- An edge set in G[S] is a matching exactly when distinct edges have disjoint endpoints. -/
def IsMatchingOn (I : Graph3) (S : Finset (Fin I.n))
    (M : Finset (Sym2 (Fin I.n))) : Prop :=
  (∀ e ∈ M, e ∈ I.G.edgeSet ∧ ∀ i ∈ e, i ∈ S) ∧
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e.toFinset f.toFinset

/-- Inclusion maximality, rather than maximum cardinality. -/
def IsMaximalMatchingOn (I : Graph3) (S : Finset (Fin I.n))
    (M : Finset (Sym2 (Fin I.n))) : Prop :=
  IsMatchingOn I S M ∧ ∀ M', IsMatchingOn I S M' → M ⊆ M' → M' = M

abbrev MatchingSelector (I : Graph3) :=
  Finset (Fin I.n) → Finset (Sym2 (Fin I.n))

def ValidSelector (I : Graph3) (M : MatchingSelector I) : Prop :=
  ∀ S, IsMaximalMatchingOn I S (M S)

def matchedVertices {n : ℕ} (M : Finset (Sym2 (Fin n))) : Finset (Fin n) :=
  M.biUnion Sym2.toFinset

def selected {n d : ℕ} (v : Fin n → Space d) (t : ℝ) (g : Space d) : Finset (Fin n) := by
  classical exact Finset.univ.filter fun i => t ≤ ⟪g, v i⟫

def kmsOutput (I : Graph3) (M : MatchingSelector I) (S : Finset (Fin I.n)) : Finset (Fin I.n) :=
  S \ matchedVertices (M S)

/-- Finite distribution of the selected set; no integrability convention is involved. -/
def kmsExpectation (I : Graph3) {d : ℕ} (v : Fin I.n → Space d)
    (t : ℝ) (M : MatchingSelector I) : ℝ :=
  ∑ S : Finset (Fin I.n), gaussProb {g | selected v t g = S} * ((kmsOutput I M S).card : ℝ)

def localDirections (I : Graph3) {d : ℕ} (v : Fin I.n → Space d)
    (W : Finset (Fin I.n)) (i : Fin I.n) : Finset (Space d) := by
  classical exact (W.filter fun j => I.G.Adj i j).image fun j => edgeDirection v j i

def LocalCovers (I : Graph3) {d : ℕ} (v : Fin I.n → Space d)
    (W : Finset (Fin I.n)) (t : ℝ) : Prop :=
  ∀ i ∈ W, IsCover (localDirections I v W i) (Real.sqrt 3 * t) (1/8)

end RecGaussColoring.Main


