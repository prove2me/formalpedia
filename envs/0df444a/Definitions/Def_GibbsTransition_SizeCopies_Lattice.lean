-- Prove2me | Definitions.Def_GibbsTransition_SizeCopies_Lattice
-- name    : GibbsTransition_SizeCopies_Lattice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T21:50:56.100048+00:00
-- url     : https://prove2.me/theorems/8bbcd6c8-455d-497d-b6ee-f54b5719d04c
-- title:
--   Cubic qutrit sites, tensor embeddings and common boundary
-- statement:
--   A cube has sites $\Lambda_L=\{1,\ldots,L\}^3$ and one three-level system with basis $A,B,C$ at each site. A basis configuration assigns a level to every site. Positively oriented nearest-neighbour edges are counted once. The edge boundary of a subset includes edges to the infinite-lattice exterior.
--
--   For $P=\operatorname{diag}(0,1,1)$ and $\kappa=1/16$, the public operators are
--
--   $$M_L=\sum_{x\in\Lambda_L}P_x,\qquad B_L=\kappa\sum_{x\in\Lambda_L}n_{\rm ext}(x)|C\rangle\langle C|_x.$$
--
--   The file gives actual tensor matrix entries for one-site and two-site embeddings and the projectors onto the three uniform configurations. At $L=1$, the unique site has six exterior incidences. These objects are shared by the hard instances and the general noncommuting family.
--
--   **Formalization Note** A site is `Fin 3 → Fin L`; adding one to each coordinate recovers the source coordinates. Levels $A,B,C$ are $0,1,2$. Matrices are indexed by all qutrit configurations, with dimension $3^{L^3}$. Only $L\ge1$ is a physical query.
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), §2.1, Equations (2), (3), (6), printed pp. 3–4 (PDF pp. 5–6); §4.1, printed p. 7 (PDF p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib

noncomputable section

namespace GibbsTransition.SizeCopies

/-- Coordinates `0,...,L-1` represent the source's `1,...,L`. -/
abbrev Site (L : ℕ) := Fin 3 → Fin L
abbrev Configuration (L : ℕ) := Site L → Fin 3
abbrev QutritMatrix := Matrix (Fin 3) (Fin 3) ℂ
abbrev EdgeMatrix := Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ
abbrev CubeMatrix (L : ℕ) := Matrix (Configuration L) (Configuration L) ℂ

/-- Integer coordinates, with the same translation by one on each axis. -/
def latticeSite {L : ℕ} (x : Site L) : Fin 3 → ℤ := fun i => (x i).val

def unitStep (i : Fin 3) : Fin 3 → ℤ := fun j => if j = i then 1 else 0

/-- Each positively oriented edge has a unique initial vertex and direction.
The initial vertex may be just outside the cube. -/
def boundaryCandidates (L : ℕ) : Finset ((Fin 3 → ℤ) × Fin 3) := by
  classical
  exact (Finset.univ : Finset (Site L × Fin 3)).biUnion fun xi =>
    { (latticeSite xi.1, xi.2), (latticeSite xi.1 - unitStep xi.2, xi.2) }

/-- Edges with exactly one endpoint in S, including edges to the exterior. -/
def edgeBoundary {L : ℕ} (S : Finset (Site L)) : Finset ((Fin 3 → ℤ) × Fin 3) := by
  classical
  let T := S.image latticeSite
  exact (boundaryCandidates L).filter fun e =>
    (e.1 ∈ T ∧ e.1 + unitStep e.2 ∉ T) ∨
    (e.1 ∉ T ∧ e.1 + unitStep e.2 ∈ T)

/-- Number of exterior incidences; at L=1 each axis contributes two. -/
def exteriorIncidences {L : ℕ} (x : Site L) : ℕ :=
  ∑ i : Fin 3, ((if (x i).val = 0 then 1 else 0) +
    (if (x i).val + 1 = L then 1 else 0))

/-- The matrix of an operator acting at a specified site. -/
def atSite {L : ℕ} (A : QutritMatrix) (x : Site L) : CubeMatrix L := by
  classical
  exact fun s t => if ∀ y, y ≠ x → s y = t y then A (s x) (t x) else 0

/-- The ordered edge operator, identity on all other tensor factors. -/
def atEdge {L : ℕ} (A : EdgeMatrix) (x y : Site L) : CubeMatrix L := by
  classical
  exact fun s t => if ∀ z, z ≠ x → z ≠ y → s z = t z
    then A (s x, s y) (t x, t y) else 0

/-- Positively oriented internal edges; a pair of sites occurs once. -/
def internalEdges (L : ℕ) (i : Fin 3) : Finset (Site L × Site L) := by
  classical
  exact Finset.univ.filter fun xy =>
    (xy.2 i).val = (xy.1 i).val + 1 ∧ ∀ j, j ≠ i → xy.2 j = xy.1 j

def kappa : ℝ := 1 / 16

def publicP : QutritMatrix := Matrix.diagonal fun s => if s = 0 then 0 else 1

def publicC : QutritMatrix := Matrix.diagonal fun s => if s = 2 then 1 else 0

def magnetization (L : ℕ) : CubeMatrix L := ∑ x : Site L, atSite publicP x

def boundaryTerm (L : ℕ) : CubeMatrix L :=
  ∑ x : Site L, (kappa * exteriorIncidences x) • atSite publicC x

/-- The projector onto the all-s basis configuration. -/
def uniformProjector (L : ℕ) (s : Fin 3) : CubeMatrix L := by
  classical
  exact Matrix.diagonal fun t => if ∀ x, t x = s then 1 else 0

end GibbsTransition.SizeCopies


