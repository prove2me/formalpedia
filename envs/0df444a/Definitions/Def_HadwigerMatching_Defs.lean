-- Prove2me | Definitions.Def_HadwigerMatching_Defs
-- name    : HadwigerMatching_Defs
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T21:54:29.54737+00:00
-- url     : https://prove2.me/theorems/96f31935-032c-4538-b31b-50c0ab1497ff
-- title:
--   Touching matchings and the connected-matching number
-- statement:
--   A **connected matching** in a simple graph $G$ is a matching whose edges are pairwise *touching*: two disjoint edges touch when some edge of $G$ joins an endpoint of one to an endpoint of the other. Formally, a finite family $M$ of vertex sets is a touching matching when every member is a two-vertex clique (an edge), distinct members are disjoint, and every two distinct members are joined by an edge of $G$.
--
--   The **connected-matching number** $\mathrm{cm}(G)$ is the largest cardinality of a touching matching,
--   $$\mathrm{cm}(G)=\sup\{\,|M| : M\text{ is a touching matching of }G\,\}.$$
--   For a finite vertex type this supremum is attained. This is the quantity bounded above by $m/100$ in the counterexample construction (Theorem 1.1 of the source preprint, p. 3).
--
--   **Formalization Note.** Transcribed verbatim from the authors' Lean development (`OAI.Combinatorics.HadwigerMatching.Definitions`). The number is a natural-valued `sSup`; on finite graphs the set of achievable cardinalities is nonempty (the empty matching) and bounded by the order, so the supremum is a maximum.
-- source:
--   https://github.com/openai/math/blob/main/preprints/A-counterexample-to-Hadwigers-conjecture-September-23-2026/paper.pdf , p. 3 (definition of connected matching and cm(G)); authors' Lean: https://github.com/openai/math/blob/main/lean/OAI/Combinatorics/HadwigerMatching/Definitions.lean

import Mathlib.Combinatorics.SimpleGraph.Clique

namespace OAI

namespace HadwigerMatching

universe u
variable {V : Type u}

/-- A finite matching whose edges are pairwise touching: each member is a
two-vertex clique, and distinct members are disjoint and joined by an edge. -/
def IsTouchingMatching (G : SimpleGraph V) (M : Finset (Finset V)) : Prop :=
  (∀ e ∈ M, e.card = 2 ∧ G.IsClique (e : Set V)) ∧
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) ∧
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f →
    ∃ v ∈ e, ∃ w ∈ f, G.Adj v w)

/-- The supremum of the cardinalities of pairwise touching matchings.
For finite vertex types, this supremum is attained. -/
noncomputable def connectedMatchingNumber (G : SimpleGraph V) : ℕ :=
  sSup {n : ℕ | ∃ M : Finset (Finset V), IsTouchingMatching G M ∧ M.card = n}

end HadwigerMatching

end OAI


