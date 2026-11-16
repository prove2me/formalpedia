-- Prove2me | Definitions.Def_TermCycDich_Supplement_Rendition
-- name    : TermCycDich_Supplement_Rendition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:45:32.176086+00:00
-- url     : https://prove2.me/theorems/a14ca3e3-d680-4fcc-b36e-e7f0120d45e0
-- title:
--   Paintings, $\Sigma$-renditions with tie-breakers, vortices, breadth and blank renditions
-- statement:
--   A **painting** in a surface $\Sigma$ is a pair $\Gamma=(U,N)$ with $N\subseteq U\subseteq\Sigma$, $N$ finite, $U$ closed, such that $U\setminus N$ has finitely many arcwise-connected components, the **cells**, and the closure $\bar c$ of every cell $c$ is a closed disc with $N(c):=\bar c\cap N\subseteq \mathrm{bd}(\bar c)$. A cell with $|N(c)|\ge4$ is a **vortex**.
--
--   Let $H$ be a graph. A **$\Sigma$-rendition** of $H$ is a triple $\rho=(\Gamma,\sigma,\pi)$ where $\Gamma$ is a painting in $\Sigma$, $\sigma(c)$ is a subgraph of $H$ for each cell $c$, and $\pi:N\to V(H)$ is injective, such that
--
--   1. (R1) $H=\bigcup_c\sigma(c)$;
--   2. (R2) the graphs $\sigma(c)$ of distinct cells are edge-disjoint;
--   3. (R3) $\pi(N(c))\subseteq V(\sigma(c))$ for every cell $c$;
--   4. (R4) $V\big(\sigma(c)\cap\bigcup_{c'\ne c}\sigma(c')\big)\subseteq\pi(N(c))$ for every cell $c$.
--
--   Every rendition carries a **tie-breaker**: for every cell $c$ with $|N(c)|=2$, a chosen component of $\mathrm{bd}(\bar c)-N(c)$. The **breadth** of $\rho$ is its number of vortices. For a set $R$ of red vertices, $\rho$ is **blank** if $\pi(N)\cup\bigcup\{V(\sigma(c)) : c \text{ not a vortex}\}$ is disjoint from $R$.
--
--   These are the paper's renditions; villages are blank renditions of $(G-A,R\setminus A)$.
--
--   **Formalization Note** $H$ is a subgraph of an ambient graph $G$ (for $G-A$ the public `minusVerts G A`), so vertices stay in $V(G)$. Unlike the public `GMSTFramework` renditions there is no floating-cell convention and no condition that distinct cell closures meet only in nodes; $\mathrm{bd}(\bar c)$ is the manifold boundary of the closed disc $\bar c$.
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), §2.2, "Paintings in surfaces" p.18 (PDF 20); "Σ-renditions", "Blank renditions", tie-breaker p.19 (PDF 21); breadth p.21 (PDF 23)

import Mathlib
import Definitions.Def_GMSTFramework_LocalStructure_Surfaces
import Definitions.Def_GMSTFramework_LocalStructure_Renditions

open scoped Classical

noncomputable section

namespace TermCycDich

namespace Supplement

open GMSTFramework.LocalStructure

/-!
# Paintings, `Σ`-renditions with tie-breakers, vortices, breadth, blank renditions

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held
version, sha256 34a10f1a…4d4ea1), §2.2, "Paintings in surfaces" p.18 (PDF 20), "Σ-renditions",
"Blank renditions" and "Traces of paths and cycles" (tie-breaker) p.19 (PDF 21), "breadth" p.21
(PDF 23).

* `Painting X`: `Γ = (U, N)` with `N ⊆ U ⊆ X`, `N` finite, `U` closed, finitely many cells (the
  arcwise-connected components of `U ∖ N`, the public `cellsOf`), and for every cell `c` the
  closure `c̄` a closed disc with `N(c) = c̄ ∩ N ⊆ bd(c̄)`. A cell with `|N(c)| ≥ 4` is a vortex.
* `Rendition X H`: a `X`-rendition `ρ = (Γ, σ, π)` of the graph `H` (a subgraph of the ambient
  graph `G`, for instance `G − A`): `σ(c) ⊆ H` for every cell, `π : N → V(H)` injective, and
  R1 `H = ⋃ σ(c)`, R2 distinct cells edge-disjoint, R3 `π(N(c)) ⊆ V(σ(c))`, R4
  `V(σ(c) ∩ ⋃_{c' ≠ c} σ(c')) ⊆ π(N(c))`; it carries a tie-breaker ("we assume that every
  rendition comes equipped with a tie-breaker"): for every cell with `|N(c)| = 2` a selected
  component of `bd(c̄) − N(c)`.
* `breadth ρ`: the number of vortices. `IsBlank ρ R`: `π(N(ρ)) ∪ ⋃{V(σ(c)) : c not a vortex}` is
  disjoint from `R`.

**Formalization Note** Unlike the public `GMSTFramework.LocalStructure.Rendition` (which this
module does not reuse), there is no floating-cell convention and no condition that distinct cell
closures meet only in nodes, and `U` is required to be closed: these are this paper's R1–R4 as
printed. `bd(c̄)` is the manifold boundary `manifoldBd (closure c)` of the closed disc `c̄`, i.e. its
boundary circle. The rendered graph is a `G.Subgraph` so that vertices stay in `V(G)` (for
`G − A` it is the public `minusVerts G A`).
-/

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable {X : Type} [TopologicalSpace X]

/-- A painting `Γ = (U, N)` in `X` (p.18). -/
structure Painting (X : Type) [TopologicalSpace X] where
  /-- the drawn set `U` -/
  U : Set X
  /-- the nodes `N` -/
  N : Set X
  N_sub : N ⊆ U
  N_finite : N.Finite
  U_closed : IsClosed U
  cells_finite : (cellsOf U N).Finite
  closure_disk : ∀ c ∈ cellsOf U N,
    IsClosedDisk (closure c) ∧ closure c ∩ N ⊆ manifoldBd (closure c)

namespace Painting

/-- The cells `C(Γ)`. -/
def cells (Γ : Painting X) : Set (Set X) := cellsOf Γ.U Γ.N

/-- `N_Γ(c) = c̄ ∩ N`. -/
def nodesOf (Γ : Painting X) (c : Set X) : Set X := closure c ∩ Γ.N

/-- A vortex: a cell with `|N(c)| ≥ 4`. -/
def IsVortex (Γ : Painting X) (c : Set X) : Prop := c ∈ Γ.cells ∧ 4 ≤ (Γ.nodesOf c).ncard

/-- The vortex cells. -/
def vortices (Γ : Painting X) : Set (Set X) := {c | Γ.IsVortex c}

end Painting

/-- A `X`-rendition `ρ = (Γ, σ, π)` of the graph `H ≤ G`, with a tie-breaker (pp.18–19). -/
structure Rendition (X : Type) [TopologicalSpace X] (H : G.Subgraph) extends Painting X where
  /-- the graph `σ(c)` drawn in each cell -/
  σ : Set X → G.Subgraph
  /-- the vertex `π(x)` of each node -/
  π : X → V
  π_inj : Set.InjOn π N
  π_mem : ∀ x ∈ N, π x ∈ H.verts
  σ_le : ∀ c ∈ cellsOf U N, σ c ≤ H
  R1_verts : H.verts = ⋃ c ∈ cellsOf U N, (σ c).verts
  R1_edges : H.edgeSet = ⋃ c ∈ cellsOf U N, (σ c).edgeSet
  R2 : ∀ c ∈ cellsOf U N, ∀ c' ∈ cellsOf U N, c ≠ c' → Disjoint (σ c).edgeSet (σ c').edgeSet
  R3 : ∀ c ∈ cellsOf U N, π '' (closure c ∩ N) ⊆ (σ c).verts
  R4 : ∀ c ∈ cellsOf U N,
    (σ c).verts ∩ (⋃ c' ∈ cellsOf U N \ {c}, (σ c').verts) ⊆ π '' (closure c ∩ N)
  /-- the tie-breaker -/
  tie : Set X → Set X
  tie_spec : ∀ c ∈ cellsOf U N, (closure c ∩ N).ncard = 2 →
    ∃ y ∈ manifoldBd (closure c) \ (closure c ∩ N),
      tie c = connectedComponentIn (manifoldBd (closure c) \ (closure c ∩ N)) y

namespace Rendition

variable {H : G.Subgraph} (ρ : Rendition X H)

/-- The vertices `π(N(ρ))` of the nodes. -/
def nodeVerts : Set V := ρ.π '' ρ.N

/-- The vertices `π(N(c))` of the nodes of a cell. -/
def cellNodeVerts (c : Set X) : Set V := ρ.π '' ρ.nodesOf c

/-- The breadth of `ρ`: the number of vortex cells. -/
def breadth : ℕ := ρ.vortices.ncard

/-- `ρ` is a blank rendition of `(H, R)`: `π(N(ρ)) ∪ ⋃{V(σ(c)) : c a non-vortex cell}` is disjoint
from `R`. -/
def IsBlank (R : Set V) : Prop :=
  Disjoint (ρ.nodeVerts ∪ ⋃ c ∈ {c | c ∈ ρ.cells ∧ ¬ ρ.IsVortex c}, (ρ.σ c).verts) R

end Rendition

end Supplement

end TermCycDich


