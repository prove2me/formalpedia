-- Prove2me | Definitions.Def_AKSZigZag_NetworkOps
-- name    : AKSZigZag_NetworkOps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:19.402002+00:00
-- url     : https://prove2.me/theorems/608c8b67-b6b9-40ca-a004-78d8a6c7dbc0
-- title:
--   Running networks inside parts, in parallel and in sequence
-- statement:
--   This module provides the operations used to describe the algorithm.
--
--   1. **Inside a part.** A network on $m$ registers is run inside a set $P$ of $m$ registers by identifying $P$ with $\{1,\dots,m\}$ through its registers in increasing order. This identification preserves $i<j$, so standard switches stay standard.
--   2. **In parallel.** Networks on disjoint parts run in the same parallel steps: step $k$ of the combined network consists of step $k$ of each part's network, and a shorter network contributes nothing to the later steps.
--   3. **In sequence.** Steps are concatenated.
--   4. **Validity.** A list of steps is a comparator network when no switch has equal ends and no register occurs twice in one step.
--   5. **Prefixes.** The first $\ell$ parallel steps of a network form the network "after $\ell$ steps".
--
--   These operations express "the application of $\varepsilon$-nearsort simultaneously within the parts" of a partition (§7, p.7).
--
--   **Formalization Note** `mkNet` returns the given steps when they are valid and the empty network otherwise. The algorithm's steps are always valid, because parts are disjoint; a verification file checks this on an instance. The empty network does not sort two or more registers, so the fallback cannot make a sorting statement true.
-- source:
--   Ajtai, Komlós, Szemerédi, An O(n log n) Sorting Network, STOC 1983, doi:10.1145/800061.808726, §7, p.7 (simultaneous application of ε-nearsort within the parts of a partition)

import Mathlib
import Definitions.Def_AKSSorting_Core_ComparatorNetwork

namespace AKSZigZag

open AKSSorting.Core

/-- Merge two layered schedules layer by layer: layer `k` of the result is layer `k` of the first
followed by layer `k` of the second; the shorter one is padded with empty layers. Used to run
networks on disjoint register sets simultaneously (AKS, STOC 1983, §7, p.7: "application of
ε-nearsort simultaneously within the parts"). -/
def mergeLayers {β : Type} : List (List β) → List (List β) → List (List β)
  | [], l => l
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a ++ b) :: mergeLayers as bs

/-- The layers of a network on `m = |P|` registers, run inside the register set `P ⊆ Fin n`:
`P` is identified with `Fin |P|` through its registers in increasing order
(`Finset.orderEmbOfFin`), so a comparator `(i, j)` becomes `(P_i, P_j)` and `i < j` is
preserved. -/
def partLayers {n : ℕ} (P : Finset (Fin n)) (N : ComparatorNetwork P.card) :
    List (List (Fin n × Fin n)) :=
  N.layers.map (List.map fun p => (P.orderEmbOfFin rfl p.1, P.orderEmbOfFin rfl p.2))

/-- Run, simultaneously, the network `ns |P|` inside every part `P` of the list `parts`. -/
def parallelLayers {n : ℕ} (ns : (m : ℕ) → ComparatorNetwork m)
    (parts : List (Finset (Fin n))) : List (List (Fin n × Fin n)) :=
  parts.foldr (fun P acc => mergeLayers (partLayers P (ns P.card)) acc) []

/-- The comparator network with the given layers, when they are valid (no comparator `(i, i)`,
no register twice in a layer); otherwise the empty network.

**Formalization Note.** Every schedule this mission builds is valid, because it runs networks on
pairwise disjoint register sets. The fallback is the empty network, which sorts nothing on two
or more registers, so it can never make a sorting claim true by accident. -/
noncomputable def mkNet {n : ℕ} (ls : List (List (Fin n × Fin n))) : ComparatorNetwork n := by
  classical
  exact if h : (∀ L ∈ ls, ∀ p ∈ L, p.1 ≠ p.2) ∧ (∀ L ∈ ls, (L.flatMap fun p => [p.1, p.2]).Nodup)
    then ⟨ls, h.1, h.2⟩
    else ⟨[], by simp, by simp⟩

/-- The network formed by the first `ℓ` layers of `N` (the state "after `ℓ` parallel steps"). -/
def prefixNet {n : ℕ} (N : ComparatorNetwork n) (ℓ : ℕ) : ComparatorNetwork n :=
  ⟨N.layers.take ℓ, fun L hL => N.ne L (List.mem_of_mem_take hL),
    fun L hL => N.disjoint L (List.mem_of_mem_take hL)⟩

end AKSZigZag


