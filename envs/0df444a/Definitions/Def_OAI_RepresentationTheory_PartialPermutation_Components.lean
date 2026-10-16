-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Components
-- name    : OAI_RepresentationTheory_PartialPermutation_Components
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:53:29.622376+00:00
-- url     : https://prove2.me/theorems/be43a84d-6f41-4fdb-80a5-e84dbdd6bf27
-- title:
--   Isotypic components correspond bijectively to the irreducible characters occurring in a representation
-- statement:
--   Let $G$ be a finite group, $V$ a finite-dimensional complex vector space, and $\rho$ a representation of $G$ on $V$, viewed as a module $V_\rho$ over the group algebra $\mathbb{C}[G]$ (with $g$ acting as $\rho(g)$). For a simple submodule $S\subseteq V_\rho$, the isotypic component of type $S$ is the sum of all simple submodules of $V_\rho$ isomorphic to $S$; let $\mathrm{Iso}(\rho)$ be the set of all isotypic components of $V_\rho$. For each $c\in\mathrm{Iso}(\rho)$ a simple submodule $S_c$ is chosen once and for all such that $c$ is the isotypic component of type $S_c$. Finally, let $\mathcal{T}(\rho)$ be the set of occurring types of $\rho$, i.e. the characters $\chi_{\rho|_W}(g)=\operatorname{tr}(\rho(g)|_W)$ of the irreducible subrepresentations $W$ of $\rho$.
--
--   1. **Chosen constituents.** For every $c\in\mathrm{Iso}(\rho)$, the module $S_c$ is simple and $c$ is the isotypic component of type $S_c$.
--   2. **Component character.** The map $\kappa\colon\mathrm{Iso}(\rho)\to\mathcal{T}(\rho)$ sends $c$ to the character of the (irreducible) subrepresentation of $\rho$ on $S_c$.
--   3. **Injectivity.** Distinct isotypic components have distinct characters.
--   4. **Surjectivity.** Every irreducible character occurring in $\rho$ is the character of some component.
--   5. **Finiteness.** Consequently the set $\mathcal{T}(\rho)$ is finite.
--
--   In formulas, the component character is
--
--   $$
--   \kappa(c)=\chi_{\rho|_{S_c}},\qquad \kappa\colon\mathrm{Iso}(\rho)\xrightarrow{\ \sim\ }\mathcal{T}(\rho)\ \text{ is a bijection.}
--   $$
--
--   This is the bookkeeping that indexes the irreducible constituents of a representation by its isotypic components; applied to the regular representation it gives a concrete index set for all irreducible representations of $G$.
--
--   **Formalization Note** The choice $c\mapsto S_c$ is `componentSimple` from the base definitions; items 1 to 5 are `componentSimple_simple`, `componentSimple_component`, `componentCharacter`, `componentCharacter_injective`, `componentCharacter_surjective` and the instance `occurringTypes_finite`. Isotypic components are Mathlib's `isotypicComponents` of the module `ρ.asModule`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/Components.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/Components.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the PartialPermutation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ModuleTransport

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators

namespace PartialPermutation
noncomputable section
section Components
variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma componentSimple_simple (c : isotypicComponents ℂ[G] ρ.asModule) :
    IsSimpleModule ℂ[G] (componentSimple ρ c) := c.property.choose_spec.1

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma componentSimple_component (c : isotypicComponents ℂ[G] ρ.asModule) :
    c.val = isotypicComponent ℂ[G] ρ.asModule (componentSimple ρ c) :=
  c.property.choose_spec.2

noncomputable def componentCharacter (c : isotypicComponents ℂ[G] ρ.asModule) : OccurringTypes ρ :=
  ⟨(Subrepresentation.ofSubmodule' (componentSimple ρ c)).toRepresentation.character,
    Subrepresentation.ofSubmodule' (componentSimple ρ c),
    (subrep_irreducible_iff ρ _).mpr (componentSimple_simple ρ c), rfl⟩

lemma componentCharacter_injective : Function.Injective (componentCharacter ρ) := by
  intro c d h
  let σ := Subrepresentation.ofSubmodule' (componentSimple ρ c)
  let τ := Subrepresentation.ofSubmodule' (componentSimple ρ d)
  have : Representation.IsIrreducible σ.toRepresentation :=
    (subrep_irreducible_iff ρ σ).mpr (componentSimple_simple ρ c)
  have : Representation.IsIrreducible τ.toRepresentation :=
    (subrep_irreducible_iff ρ τ).mpr (componentSimple_simple ρ d)
  obtain ⟨e⟩ := irreducible_equiv_of_character_eq σ.toRepresentation τ.toRepresentation
    (congrArg Subtype.val h)
  apply Subtype.ext
  rw [componentSimple_component ρ c, componentSimple_component ρ d]
  exact (moduleEquivOfSubrepEquiv ρ τ σ e).symm.isotypicComponent_eq

omit [Fintype G] in
lemma componentCharacter_surjective : Function.Surjective (componentCharacter ρ) := by
  intro χ
  obtain ⟨σ, hirr, hχ⟩ := χ.property
  have := hirr
  have : IsSimpleModule ℂ[G] σ.asSubmodule := (subrep_irreducible_iff ρ σ).mp hirr
  let c : isotypicComponents ℂ[G] ρ.asModule :=
    ⟨isotypicComponent ℂ[G] ρ.asModule σ.asSubmodule, σ.asSubmodule, inferInstance, rfl⟩
  have := componentSimple_simple ρ c
  have hs : σ.asSubmodule ≤ c.val := σ.asSubmodule.le_isotypicComponent
  rw [componentSimple_component ρ c] at hs
  obtain ⟨e⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent ℂ[G] ρ.asModule (componentSimple ρ c))
    σ.asSubmodule hs
  refine ⟨c, Subtype.ext ?_⟩
  change (Subrepresentation.ofSubmodule' (componentSimple ρ c)).toRepresentation.character = χ.val
  rw [hχ]
  exact Representation.char_iso
    (subrepEquivOfModuleEquiv ρ (Subrepresentation.ofSubmodule' (componentSimple ρ c)) σ e.symm)

instance occurringTypes_finite : Finite (OccurringTypes ρ) :=
  Finite.of_surjective (componentCharacter ρ) (componentCharacter_surjective ρ)

end Components

end
end PartialPermutation

end

end OAI


