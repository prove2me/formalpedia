-- Prove2me | Definitions.Def_SeymourThomas1993_Brambles
-- name    : SeymourThomas1993_Brambles
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-13T19:56:55.500691+00:00
-- url     : https://prove2.me/theorems/5c416fa9-7081-4f53-be3d-e5dd6333ee24
-- title:
--   Finite brambles and their hitting-set order
-- statement:
--   A bramble in a finite graph is a finite family of nonempty connected vertex sets, any two of which touch: they intersect or an edge joins them. Its order is at least k if every vertex set of size less than k is disjoint from some member of the family. Thus no set of fewer than k vertices hits all its members.
-- source:
--   Seymour and Thomas, Graph searching and a min-max theorem for tree-width, JCTB 58 (1993), pp. 22-33. Definitions as in Dvorak--Norin, https://arxiv.org/pdf/1408.3869v2, Section 2.1, PDF p. 3.

import Definitions.Def_DvorakNorin2018_HavenCloudConfiguration
set_option autoImplicit false
namespace StableMSR.Recovery.Brambles
open StableMSR.Recovery.Havens
variable {V : Type} [DecidableEq V]
/-- A finite family of nonempty connected vertex sets that pairwise touch. -/
structure IsBramble (G : SimpleGraph V) (family : Finset (Finset V)) : Prop where
  connected : ∀ C ∈ family, ConnectedSet G C
  touch : ∀ C ∈ family, ∀ D ∈ family, Touch G C D
/-- Every deletion set of size less than `k` misses a member of the family. -/
def OrderAtLeast (family : Finset (Finset V)) (k : ℕ) : Prop :=
  ∀ W : Finset V, W.card < k → ∃ C ∈ family, Disjoint W C
end StableMSR.Recovery.Brambles


