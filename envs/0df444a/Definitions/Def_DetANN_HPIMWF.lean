-- Prove2me | Definitions.Def_DetANN_HPIMWF
-- name    : DetANN_HPIMWF
-- status  : Definition
-- author  : @milia
-- created : 2026-11-16T19:16:30.431227+00:00
-- url     : https://prove2.me/theorems/8585cb26-333b-4fa1-b394-701a90edaafd
-- title:
--   Well-formed HPIM trees
-- statement:
--   Let $T$ be an HPIM tree (definition `DetANN_HPIMFormat`).
--   - A box decision tree satisfies $\mathrm{AnsLt}_n$ if every leaf answer $\mathrm{some}\ i$ has $i<n$.
--   - $T$ is **well formed** if, at every inner node with $n$ local points, every lookup $Z_i$ satisfies $\mathrm{AnsLt}_n$, recursively in all children and in the representatives' child.
--
--   The memory layout of `DetANN_HPIMLayout` does not store $n$, so a query program cannot check that a lookup answer is a valid local index. Well-formedness guarantees that it always is. The tree `hpimTree` is well formed, because the leaves of its lookup structures answer the least good local point.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). It corrects DetANN.HPIM.hpim_query_program, which is false because the layout does not store the number of local points.

import Mathlib
import Definitions.Def_DetANN_HPIMFormat

/-!
# Well-formed HPIM trees

The memory layout of `DetANN_HPIMLayout` does not store the number `n` of local points of a node, so a
query program cannot test whether a lookup answer `i` is a valid local index. `HTree.WF` says that it
always is: at every inner node with `n` local points, every leaf answer of every lookup is `< n`.
The tree `hpimTree` of `DetANN_HPIMTree` is well formed.

* `BoxTree.AnsLt n T`: every leaf answer `some i` of `T` has `i < n`.
* `HTree.WF T`: `AnsLt n` for all lookups of every inner node, recursively.
-/

namespace DetANN.HPIM

/-- Every leaf answer `some i` of the box decision tree has `i < n`. -/
def BoxTree.AnsLt {m : ℕ} (n : ℕ) : BoxTree m → Prop
  | .leaf none => True
  | .leaf (some i) => i < n
  | .test _ _ y t => BoxTree.AnsLt n y ∧ BoxTree.AnsLt n t

/-- A well-formed HPIM tree: at every inner node with `n` local points, every lookup answers local
indices `< n`. -/
def HTree.WF {m : ℕ} : HTree m → Prop
  | .single _ => True
  | .node n _ _ Z _ kidOf reps => (∀ i, (Z i).AnsLt n) ∧ (∀ i, (kidOf i).WF) ∧ reps.WF

end DetANN.HPIM


