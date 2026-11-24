-- Prove2me | Definitions.Def_KernelRamsey_Ram
-- name    : KernelRamsey_Ram
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:26:35.744807+00:00
-- url     : https://prove2.me/theorems/782bba4f-0cff-4837-b3e4-ea61f38a1203
-- title:
--   Ramsey-type predicates for vertex sets
-- statement:
--   `Ram t m` says that in every graph every set of at least $m$ vertices contains a triangle or an independent set of size $t$. `Ram2 s t m` says that in every graph every set of at least $m$ vertices contains an $s$-clique or an independent $t$-set.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic

namespace KernelRamsey

/-- Every set of at least `m` vertices of every graph contains a triangle or an independent set
of size `t`. -/
def Ram (t m : Nat) : Prop :=
  ∀ {V : Type} (G : SimpleGraph V) (A : Finset V), m ≤ A.card →
    (∃ T ⊆ A, G.IsNClique 3 T) ∨ (∃ I ⊆ A, Gᶜ.IsNClique t I)

/-- Every set of at least `m` vertices contains an `s`-clique or an independent `t`-set. -/
def Ram2 (s t m : Nat) : Prop :=
  ∀ {V : Type} (G : SimpleGraph V) (A : Finset V), m ≤ A.card →
    (∃ T ⊆ A, G.IsNClique s T) ∨ (∃ I ⊆ A, Gᶜ.IsNClique t I)

end KernelRamsey


