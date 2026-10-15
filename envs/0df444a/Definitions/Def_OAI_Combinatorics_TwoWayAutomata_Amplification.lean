-- Prove2me | Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification
-- name    : OAI_Combinatorics_TwoWayAutomata_Amplification
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T08:18:30.435674+00:00
-- url     : https://prove2.me/theorems/f3e5af3f-442f-4a7c-ab68-3e5d3db6a70b
-- title:
--   The loss bound $2^{\lfloor (h-2)/127\rfloor}$ and permutation units in the relation monoid
-- statement:
--   1. **Loss bound.** For $h\in\mathbb{N}$,
--   $$\mathrm{LB}(h)=2^{\lfloor \max(h-2,\,0)/127\rfloor},$$
--   that is, $h-2$ is truncated at $0$ and the quotient by $127$ is rounded down. Thus $\mathrm{LB}(h)=1$ for $h\le128$, and $\mathrm{LB}(h)=2^k$ for $127k+2\le h\le127k+128$, $k\ge1$.
--   2. **Permutation units.** Let $H$ be a set and let $\mathcal R(H)$ be the monoid of relations on $H$ under composition in path order, with identity $\mathrm{Id}_H$. For a permutation $\sigma$ of $H$, its graph $\Gamma_\sigma=\{(x,\sigma(x)):\ x\in H\}$ is a unit of $\mathcal R(H)$ whose inverse is the graph of $\sigma^{-1}$:
--   $$\Gamma_\sigma\,\Gamma_{\sigma^{-1}}=\mathrm{Id}_H=\Gamma_{\sigma^{-1}}\,\Gamma_\sigma .$$
--
--   $\mathrm{LB}(h)$ is the quantity in the final lower bound when the letters are relations on an $h$-element set: later results show, for $h\ge2$ and $m\ge1$, that any representation of words by boundary diagrams on $m$ points from which the complement of the liveness language can be read off satisfies $\mathrm{LB}(h)\le2m$. The permutation units are the elements of $\mathcal R(H)$ that are lifted along homomorphisms in order to conjugate one single-edge idempotent into another.
--
--   **Formalization Note** `lossBound h` is `2 ^ ((h - 2) / 127)` with natural-number subtraction and division. `permutationUnit σ` is the unit of `RelationMonoid H` with value `RelationMonoid.ofRel (Function.graph σ)` and inverse `RelationMonoid.ofRel (Function.graph σ.symm)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Amplification.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Amplification.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TwoWayComplementation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid

namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- The exponential lower bound for `2 ≤ h`. -/
def lossBound (h : ℕ) : ℕ := 2 ^ ((h - 2) / 127)

/-- A permutation and its inverse form a unit in the full relation monoid. -/
def permutationUnit {H : Type*} (σ : Equiv.Perm H) : (RelationMonoid H)ˣ where
  val := .ofRel (Function.graph σ)
  inv := .ofRel (Function.graph σ.symm)
  val_inv := by
    apply RelationMonoid.ext
    change Function.graph σ ○ Function.graph σ.symm = SetRel.id
    ext ⟨a, b⟩
    simp [SetRel.comp, Function.graph, SetRel.id]
  inv_val := by
    apply RelationMonoid.ext
    change Function.graph σ.symm ○ Function.graph σ = SetRel.id
    ext ⟨a, b⟩
    simp [SetRel.comp, Function.graph, SetRel.id]

end TwoWayComplementation

end OAI


