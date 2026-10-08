-- Prove2me | Definitions.Def_QLLL_LocalLemma_Infinite
-- name    : QLLL_LocalLemma_Infinite
-- status  : Definition
-- author  : @sattath
-- created : 2026-10-06T17:41:58.383992+00:00
-- url     : https://prove2.me/theorems/544c6082-142f-4247-b0e5-24876f011586
-- title:
--   Dependency graphs for families indexed by an arbitrary type
-- statement:
--   **Dependency graph on an arbitrary index set** (`IsDependencyGraphOn`). Let $L$ be a bounded lattice with a valuation $R$, let $(X_i)_{i \in I}$ be a family in $L$ indexed by an arbitrary set $I$, and let $\Gamma(i) \subseteq I$ be finite sets. They form a dependency graph if, for every $i$ and every finite $S \subseteq I$ with $i \notin S$ and $S \cap \Gamma(i) = \emptyset$,
--   $$R\Big(X_i \wedge \bigwedge_{j \in S} X_j\Big) = R(X_i)\, R\Big(\bigwedge_{j \in S} X_j\Big).$$
--
--   For a finite index set this agrees with the dependency graph of `QLLL_LocalLemma_Basic`. It is the hypothesis of the local lemma for infinite families.
-- source:
--   Not in the paper; the dependency-graph notion for infinite families. Formalization companion to Ambainis, Kempe and Sattath, A Quantum Lovász Local Lemma, arXiv:0911.1696; see the blueprint https://sattath.github.io/Quantum-Lovasz-Local-Lemma/blueprint/

import Definitions.Def_QLLL_LocalLemma_Basic
import Mathlib

/-
Copyright (c) 2026 Or Sattath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Or Sattath
-/

/-!
# The local lemma for an infinite index set

`QuantumLocalLemma.LocalLemma.Basic` proves the local lemma for finitely many events, indexed by
`Fin n`. This file removes the finiteness of the index set.

The observation that makes it work: the proof of `key_mul` uses the dependency
hypothesis at exactly one point, to say that `X i` is independent of the finite
family `S \ Γ i` when `i ∉ S`. Phrased as "independent of every finite set of
non-neighbours not containing `i`", that condition never mentions `univ`, so the
index type need not be finite at all. `prod_le_inf_of` therefore bounds every
finite meet, for an arbitrary index type.

Only the last step, passing from all finite meets to the meet of the whole
family, needs anything new, and what it needs is continuity from above. That is
supplied here as an explicit hypothesis rather than assumed silently, because it
is exactly the axiom the finite theory lacks:

* `QuantumLocalLemma.Quantum.NoCompactness` shows the classical compactness route is unavailable
  for subspaces, so continuity cannot be dodged.
* `relDim X = dim X / dim V` cannot satisfy it, since it requires finite
  dimension in the first place.
* A normalised trace on a finite von Neumann algebra can: it is a `[0,1]`-valued
  dimension on a complete projection lattice, modularity is the Kaplansky
  formula, and normality of the trace is precisely continuity from above.

So the combinatorial content is proved unconditionally, and the analytic content
is isolated in one named hypothesis.
-/

namespace QLLL

open Finset

variable {α : Type*} [Lattice α] [BoundedOrder α] (R : Valuation α)
variable {ι : Type*} {X : ι → α} {Γ : ι → Finset ι} {y : ι → ℝ}

/-- A dependency graph, with no finiteness assumption on the index type: `X i` is
independent of any finite set of non-neighbours not containing `i`.

For a finite index type this is equivalent to `Valuation.IsDependencyGraph`,
since `S ⊆ (univ \ Γ i).erase i` says exactly `i ∉ S` and `Disjoint S (Γ i)`. -/
def IsDependencyGraphOn (X : ι → α) (Γ : ι → Finset ι) : Prop :=
  ∀ (i : ι) (S : Finset ι), i ∉ S → Disjoint S (Γ i) →
    R (X i ⊓ S.inf X) = R (X i) * R (S.inf X)

end QLLL

namespace QLLL

open Finset

variable {α : Type*} [CompleteLattice α] (R : Valuation α)
variable {ι : Type*} {X : ι → α} {Γ : ι → Finset ι} {y : ι → ℝ}

end QLLL


