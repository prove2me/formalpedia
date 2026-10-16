-- Prove2me | Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification__TwoWayDeterminization
-- name    : OAI_Combinatorics_TwoWayAutomata_Amplification__TwoWayDeterminization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:41:20.705002+00:00
-- url     : https://prove2.me/theorems/a1eeeee2-8153-4fba-bc2e-433d26a1571a
-- title:
--   The loss bound $2^{\lfloor (h-2)/127\rfloor}$ and permutation units of the relation monoid
-- statement:
--   1. **Loss bound.** For $h\in\mathbb N$,
--   $$\mathrm{loss}(h)=2^{\lfloor (h-2)/127\rfloor},$$
--   computed in the natural numbers: $h-2$ is truncated subtraction (it equals $0$ when $h<2$) and the division is floor division. The bound is meant for $h\ge 2$; it equals $1$ for $h\le 128$.
--   2. **Permutation units.** Let $H$ be a set and let $\mathcal R(H)$ be the monoid of all binary relations on $H$ under composition in path order, $(x,z)\in RS$ iff $(x,y)\in R$ and $(y,z)\in S$ for some $y$, with identity $\mathrm{Id}_H=\{(x,x):x\in H\}$. For a permutation $\sigma$ of $H$ let $\Gamma_\sigma=\{(x,\sigma(x)):\ x\in H\}$ be its graph. Then $\Gamma_\sigma$ is a unit of $\mathcal R(H)$ with inverse $\Gamma_{\sigma^{-1}}$:
--   $$\Gamma_\sigma\,\Gamma_{\sigma^{-1}}=\mathrm{Id}_H=\Gamma_{\sigma^{-1}}\,\Gamma_\sigma .$$
--
--   For $n\ge 4$ and $h=n-2$ one has $\mathrm{loss}(n-2)=2^{\lfloor (n-4)/127\rfloor}$, which is the exponential quantity in the state lower bounds for two-way automata over the alphabet of all relations on an $(n-2)$-element set. Permutation graphs are invertible letters of that alphabet: they are units of the relation monoid.
--
--   **Formalization Note** `lossBound h` is `2 ^ ((h - 2) / 127)` in `ℕ`. `permutationUnit σ : (RelationMonoid H)ˣ` has value `RelationMonoid.ofRel (Function.graph σ)` and inverse `RelationMonoid.ofRel (Function.graph σ.symm)`, where `Function.graph σ` is the relation $\{(a,b): \sigma(a)=b\}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Amplification.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Amplification.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TwoWayDeterminization mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid__TwoWayDeterminization

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


