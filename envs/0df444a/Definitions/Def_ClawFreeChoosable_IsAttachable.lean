-- Prove2me | Definitions.Def_ClawFreeChoosable_IsAttachable
-- name    : ClawFreeChoosable_IsAttachable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:54.21263+00:00
-- url     : https://prove2.me/theorems/404b7659-a941-49c1-a28a-142b56b78b67
-- title:
--   Attachable clique
-- statement:
--   A clique $Q$ of a graph $G$ is **attachable** if $N_G(v) \setminus Q$ is a clique for every $v \in Q$. By convention the empty clique is attachable.
--
--   Attachable cliques are the cliques along which a clique of simplicial vertices can be glued to a claw-free graph (Lemma 7.3); they carry the short lists of the mixed-list property (Mk).
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, Definition 7.1, p.9

import Mathlib

set_option autoImplicit false

namespace ClawFreeChoosable

/-- **Attachable clique** (arXiv:2611.01068v1, Definition 7.1, p.9): a clique `Q` of `G` such
that `N_G(v) \ Q` is a clique for every `v ∈ Q`. The empty clique is attachable (here
vacuously, as the paper's convention requires). -/
def IsAttachable {V : Type} (G : SimpleGraph V) (Q : Set V) : Prop :=
  G.IsClique Q ∧ ∀ v ∈ Q, G.IsClique (G.neighborSet v \ Q)

end ClawFreeChoosable


