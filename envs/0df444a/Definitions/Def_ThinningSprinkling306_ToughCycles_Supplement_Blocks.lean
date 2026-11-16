-- Prove2me | Definitions.Def_ThinningSprinkling306_ToughCycles_Supplement_Blocks
-- name    : ThinningSprinkling306_ToughCycles_Supplement_Blocks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:42:10.559205+00:00
-- url     : https://prove2.me/theorems/8b069ff4-1626-41ac-8357-a8277cf686b4
-- title:
--   Invariant block partitions and crossing-edge count
-- statement:
--   For a finite simple graph $G$, a vertex partition is a disjoint cover by nonempty sets. It is an invariant block partition when every automorphism of $G$ sends every part to a part. This permits disconnected graphs and the empty partition of the empty graph. For disjoint sets $U,W$, define
--   $$
--   e_G(U,W)=\sum_{u\in U}|N_G(u)\cap W|.
--   $$
--   Each crossing undirected edge is counted once. These notions express the symmetry and edge-boundary clauses of Lemma 7.1 without assuming its conclusions. Vertex transitivity itself is the separately published predicate quantifying over all graph automorphisms.
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 13, Section 7.1, preamble to Lemma 7.1 (PDF p. 15); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Definitions.Def_ThinningSprinkling306_ToughCycles_Supplement_GraphParameters
import Definitions.Def_DerandSq_IsVertexTransitive

namespace ThinningSprinkling306.ToughCycles.Supplement

/-- A partition into nonempty vertex sets; the empty graph has the empty partition. -/
noncomputable def VertexPartition {n : ℕ}
    (B : Finset (Finset (Fin n))) : Prop :=
  (∀ A ∈ B, A.Nonempty) ∧
  (∀ A ∈ B, ∀ C ∈ B, A ≠ C → Disjoint A C) ∧
  B.biUnion (fun A => A) = Finset.univ

/-- Each automorphism permutes the blocks (closure implies a permutation, by finiteness). -/
noncomputable def InvariantBlocks {n : ℕ} (G : SimpleGraph (Fin n))
    (B : Finset (Finset (Fin n))) : Prop :=
  VertexPartition B ∧ ∀ φ : G ≃g G, ∀ A ∈ B, A.image (fun v => φ v) ∈ B

/-- For disjoint U and W, the number of crossing undirected edges, each counted once. -/
noncomputable def crossingEdges {n : ℕ} (G : SimpleGraph (Fin n))
    (U W : Finset (Fin n)) : ℕ :=
  U.sum fun v => (CharonChurn.Main.nbrsIn G W v).card

end ThinningSprinkling306.ToughCycles.Supplement


