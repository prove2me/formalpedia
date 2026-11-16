-- Prove2me | Definitions.Def_TermCycDich_Supplement_Society
-- name    : TermCycDich_Supplement_Society
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:46:32.606688+00:00
-- url     : https://prove2.me/theorems/6e1cccae-1675-442e-b61f-5e40ec884e08
-- title:
--   Segments, transactions, depth of societies and of renditions
-- statement:
--   A **society** $(K,\Omega)$ is a graph $K$ with a cyclic ordering $\Omega$ of a set $V(\Omega)\subseteq V(K)$. A **segment** of $\Omega$ is a set of consecutive vertices of $\Omega$. A **transaction** in $(K,\Omega)$ is an $A$-$B$-linkage of $V(\Omega)$-paths of $K$ for two disjoint segments $A,B$; the **depth** of $(K,\Omega)$ is the maximum order of a transaction.
--
--   For a vortex $c_0$ of a rendition $\rho$, the **vortex society** is $(\sigma(c_0),\Omega_{c_0})$, where $\Omega_{c_0}$ orders $\pi(N(c_0))$ along the boundary of $\bar c_0$. The **depth** of $\rho$ is the maximum depth of its vortex societies, and $0$ if there is no vortex.
--
--   Villages bound the depth of their rendition by $\mathrm{depth}_{2.4}(3,6(b+1)^2+1,b)$.
--
--   **Formalization Note** "Depth at most $d$" is stated as: every transaction has order at most $d$. A cyclic ordering is a duplicate-free list read cyclically; the order along $\mathrm{bd}(\bar c_0)$ is taken for some parametrisation of the disc, which covers both orientations (depth does not depend on the orientation). The public `GMSTFramework` segment ("at most two endpoints") admits non-consecutive sets and is not reused.
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), §2.2 "Societies" p.19 (PDF 21); "Transactions and nests" p.20 (PDF 22); "Depth of vortices" p.21 (PDF 23)

import Mathlib
import Definitions.Def_GMSTFramework_LocalStructure_Graphs
import Definitions.Def_TermCycDich_Supplement_Rendition

open scoped Classical

noncomputable section

namespace TermCycDich

namespace Supplement

open GMSTFramework.LocalStructure

/-!
# Segments, transactions, depth of societies, vortex societies, depth of a rendition

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held
version, sha256 34a10f1a…4d4ea1), §2.2 "Societies" p.19 (PDF 21), "Transactions and nests" p.20
(PDF 22), "Depth of vortices" p.21 (PDF 23).

* A cyclic ordering `Ω` is a duplicate-free list read cyclically. `IsSegment Ω S`: `S` is a set of
  consecutive vertices of `Ω`, i.e. the set of the first `m` entries of some rotation of `Ω`.
* `Transaction K Ω n`: an `A`-`B`-linkage of order `n` of `V(Ω)`-paths of `K`, for disjoint
  segments `A`, `B` of `Ω` (paths and linkages are the public `GMSTFramework` ones).
* `DepthLE K Ω d`: every transaction of `(K, Ω)` has order at most `d` (the depth, the maximum
  order of a transaction, is at most `d`).
* `IsVortexOrder ρ c₀ Ω`: `Ω` lists `π(N(c₀))` in the order in which the nodes occur along the
  boundary circle of the closed disc `c̄₀`, for some parametrisation of `c̄₀` (this covers both
  orientations; depth is invariant under reversal).
* `RenditionDepthLE ρ d`: every vortex society `(σ(c₀), Ω_{c₀})` has depth at most `d` (the depth of
  `ρ` is at most `d`; it is `0` without vortices).

**Formalization Note** The public `GMSTFramework.LocalStructure.IsSegment` ("at most two
endpoints") also admits non-consecutive sets such as two isolated vertices, so it is not reused;
this module uses the paper's "set of consecutive vertices".
-/

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable {X : Type} [TopologicalSpace X]

/-- `S` is a segment of the cyclic ordering `Ω`: a set of consecutive vertices. -/
def IsSegment (Ω : List V) (S : Finset V) : Prop :=
  ∃ k m : ℕ, S = ((Ω.rotate k).take m).toFinset

/-- A transaction of order `n` in the society `(K, Ω)`. -/
structure Transaction (K : G.Subgraph) (Ω : List V) (n : ℕ) where
  /-- the paths -/
  L : Linkage G n
  /-- one end segment -/
  A : Finset V
  /-- the other end segment -/
  B : Finset V
  segA : IsSegment Ω A
  segB : IsSegment Ω B
  disjAB : Disjoint A B
  inK : ∀ i, (L.path i).sub ≤ K
  ΩPath : ∀ i, IsAPath {v | v ∈ Ω} (L.path i)
  ABPath : ∀ i, IsABPath (A : Set V) (B : Set V) (L.path i)

/-- The society `(K, Ω)` has depth at most `d`. -/
def DepthLE (K : G.Subgraph) (Ω : List V) (d : ℕ) : Prop :=
  ∀ n, Transaction K Ω n → n ≤ d

namespace Rendition

variable {H : G.Subgraph} (ρ : Rendition X H)

/-- `Ω` is the cyclic ordering of the vortex society of the vortex `c₀`. -/
def IsVortexOrder (c₀ : Set X) (Ω : List V) : Prop :=
  ρ.IsVortex c₀ ∧ Ω.Nodup ∧ {v | v ∈ Ω} = ρ.cellNodeVerts c₀ ∧
    ∃ e : C(TheDisk, X), Function.Injective e ∧ Set.range e = closure c₀ ∧
      ∃ pts : List X, pts.map ρ.π = Ω ∧ (∀ x ∈ pts, x ∈ ρ.nodesOf c₀) ∧
        ArrangedAlong (fun z : Circle => e ⟨(z : ℂ), by
          rw [Metric.mem_closedBall, dist_zero_right, Circle.norm_coe]⟩) pts

/-- `ρ` has depth at most `d`: every vortex society has depth at most `d`. -/
def RenditionDepthLE (d : ℕ) : Prop :=
  ∀ c ∈ ρ.vortices, ∀ Ω, ρ.IsVortexOrder c Ω → DepthLE (ρ.σ c) Ω d

end Rendition

end Supplement

end TermCycDich


