-- Prove2me | Definitions.Def_WeldedPath_singSupport
-- name    : WeldedPath_singSupport
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:15:28.396618+00:00
-- url     : https://prove2.me/theorems/214995ab-672e-4bf6-8b90-0088257f3b54
-- title:
--   The distributions $D_{\mathrm{prod}}$ and $D_{\mathrm{sing}}$ over welded trees oracles
-- statement:
--   The distribution $D_{\mathrm{prod}}$ samples $\sigma=(\sigma_{\mathrm{label}},\sigma_{\mathrm{edge}})$ uniformly from $S^{(0)}_M\times S_{\mathrm{edge}}$, where $S^{(0)}_M=\{\pi\in\mathrm{Sym}([0,M]):\pi(0)=0\}$ and $S_{\mathrm{edge}}=\prod_{b\in B_{\mathrm{edge}}}\mathrm{Sym}(E_b)$. Permuting the weld classes may split the weld into several cycles. Let $S$ be the event that the permuted weld edges, joining $\mathrm{tail}(e)$ to $\mathrm{head}(\sigma_b(e))$ for every weld edge $e$, form one cycle. Then
--   $$
--   D_{\mathrm{sing}}=D_{\mathrm{prod}}\mid S .
--   $$
--   Both are uniform distributions on finite sets, and averages over them are written $\mathbb E_{\sigma\sim D}$.
--
--   $D_{\mathrm{sing}}$ is the distribution of the main theorem; $D_{\mathrm{prod}}$ is the product distribution used inside the proof.
--
--   **Formalization Note** The supports are finite sets of pairs (label permutation, edge permutation). $S$ is encoded as: the graph of permuted weld edges connects all leaves; it is $2$-regular, so this is one cycle (a parallel pair is a $2$-cycle and disconnects it).
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), pp.16–17

import Mathlib
import Definitions.Def_WeldedPath_oracleFn

namespace WeldedPath

namespace WeldedInstance

variable {n : ℕ}

/-- The graph on the leaves formed by the permuted weld edges: for each weld edge `e`, the edge
`{tail(e), head(σ_{(wld, Color(e))}(e))}` (arXiv:2611.05912 (sha256 b31400a0…), (25), p.17: a weld
edge is traversed from `tail(e)` to `head(σ_b(e))`). -/
def permWeldGraph (G : WeldedInstance n) (π : Equiv.Perm G.edges) : SimpleGraph ℕ :=
  SimpleGraph.fromRel fun a b =>
    ∃ e : G.edges, e.1 ∈ G.weldEdges ∧ a = e.1.tail ∧ b = (π e).1.head n

/-- The event `S` that the weld edges form one cycle (arXiv:2611.05912 (sha256 b31400a0…), p.17).

**Formalization Note.** Every leaf is the tail or head of exactly one permuted weld edge of each
of its two non-parent colors, so the permuted weld multigraph is 2-regular; it is one cycle exactly
when it connects all leaves. A parallel pair (footnote 2, p.23) is a 2-cycle, which leaves the
other leaves unreached. -/
def SingleCycle (G : WeldedInstance n) (π : Equiv.Perm G.edges) : Prop :=
  ∀ a b, IsLeaf n a → IsLeaf n b → (G.permWeldGraph π).Reachable a b

open Classical in
/-- The support of `D_prod`: all `σ = (σ_label, σ_edge) ∈ S^{(0)}_M × S_edge`, i.e. `σ_label` a
permutation of `[0, M]` with `σ_label(0) = 0` and `σ_edge` an edge permutation (arXiv:2611.05912
(sha256 b31400a0…), p.16–17). `D_prod` is the uniform distribution on it. -/
noncomputable def prodSupport (l : ℕ) (G : WeldedInstance n) :
    Finset (Equiv.Perm (Label n) × Equiv.Perm G.edges) :=
  Finset.univ.filter fun σ => σ.1 0 = 0 ∧ G.IsEdgePerm l σ.2

open Classical in
/-- The support of `D_sing = D_prod | S` (arXiv:2611.05912 (sha256 b31400a0…), p.17): the `σ` of
`prodSupport` whose weld edges form one cycle. `D_sing` is the uniform distribution on it. -/
noncomputable def singSupport (l : ℕ) (G : WeldedInstance n) :
    Finset (Equiv.Perm (Label n) × Equiv.Perm G.edges) :=
  (G.prodSupport l).filter fun σ => G.SingleCycle σ.2

end WeldedInstance

/-- The uniform average `E_{σ ∼ S}[g(σ)] = (1/|S|) Σ_{σ ∈ S} g(σ)` over a finite set. -/
noncomputable def avgOver {α : Type*} (S : Finset α) (g : α → ℝ) : ℝ :=
  (∑ x ∈ S, g x) / S.card

end WeldedPath


