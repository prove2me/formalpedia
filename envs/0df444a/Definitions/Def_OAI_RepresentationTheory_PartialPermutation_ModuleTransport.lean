-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ModuleTransport
-- name    : OAI_RepresentationTheory_PartialPermutation_ModuleTransport
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:52:40.952609+00:00
-- url     : https://prove2.me/theorems/913a1ad7-c9de-46b8-8e6c-531c69a05742
-- title:
--   Subrepresentations as group-algebra submodules, and irreducible representations with equal characters are equivalent
-- statement:
--   Throughout, $G$ is a group, $V$ is a complex vector space and $\rho\colon G\to\mathrm{GL}(V)$ is a representation. Let $\mathbb{C}[G]$ be the complex group algebra; $V$ becomes a $\mathbb{C}[G]$-module $V_\rho$ through
--
--   $$
--   \Big(\sum_{g}a_g\,g\Big)\cdot v=\sum_{g}a_g\,\rho(g)v .
--   $$
--
--   A subrepresentation of $\rho$ is a $\rho$-invariant subspace $W\subseteq V$; it carries the restricted representation $\rho|_W$ and is at the same time a $\mathbb{C}[G]$-submodule of $V_\rho$. The file sets up the dictionary between these two points of view and defines the set of irreducible characters occurring in $\rho$.
--
--   1. **Module identification.** For every subrepresentation $W$, the $\mathbb{C}[G]$-module attached to the representation $\rho|_W$ is $\mathbb{C}[G]$-linearly isomorphic to the submodule $W$ of $V_\rho$, via the identity on vectors.
--   2. **Irreducibility criterion.** $\rho|_W$ is irreducible if and only if $W$ is a simple $\mathbb{C}[G]$-module.
--   3. **Transport of isomorphisms.** For two subrepresentations $W_1,W_2$, every $\mathbb{C}[G]$-module isomorphism $W_1\cong W_2$ yields an equivalence of representations $\rho|_{W_1}\cong\rho|_{W_2}$ (a bijective intertwining operator), and conversely every such equivalence yields a $\mathbb{C}[G]$-module isomorphism $W_1\cong W_2$.
--   4. **Characters determine irreducibles.** Let $G$ be finite and let $\rho$ (on $V$) and $\sigma$ (on $W$) be irreducible representations on finite-dimensional complex vector spaces, with characters $\chi_\rho(g)=\operatorname{tr}\rho(g)$ and $\chi_\sigma(g)=\operatorname{tr}\sigma(g)$. If $\chi_\rho=\chi_\sigma$ as functions on $G$, then $\sigma\cong\rho$.
--   5. **Occurring types.** For finite-dimensional $V$, the set of occurring types of $\rho$ is the set of characters of the irreducible subrepresentations of $\rho$:
--
--   $$
--   \mathcal{T}(\rho)=\big\{\chi_{\rho|_W}\ :\ W\subseteq V\ \text{a }\rho\text{-invariant subspace with }\rho|_W\ \text{irreducible}\big\},
--   $$
--
--   a set of functions $G\to\mathbb{C}$.
--
--   These translations let the module-theoretic structure theory (simple submodules, isotypic components) be applied to representations, and item 4 is the tool used to recognise an irreducible constituent from its character alone.
--
--   **Formalization Note** Item 1 is `subrepModuleEquiv`, item 2 is `subrep_irreducible_iff`, the two directions of item 3 are `subrepEquivOfModuleEquiv` and `moduleEquivOfSubrepEquiv`, item 4 is `irreducible_equiv_of_character_eq` (stated as the existence of an equivalence from $\sigma$ to $\rho$), and `OccurringTypes ρ` is the subtype of functions $G\to\mathbb{C}$ described in item 5. The private lemma `ite_eq_left` is a local restatement of `if_pos`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/ModuleTransport.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/ModuleTransport.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the PartialPermutation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators

namespace PartialPermutation
noncomputable section

section ModuleTransport
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V)

noncomputable def subrepModuleEquiv (σ : Subrepresentation ρ) :
    σ.toRepresentation.asModule ≃ₗ[ℂ[G]] σ.asSubmodule where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    apply Subtype.ext
    change ((σ.toRepresentation.asAlgebraHom a) x).val =
      (ρ.asAlgebraHom a) x.val
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp only [map_zero]; rfl
    | add a b ha hb =>
      simp only [map_add]
      change ((σ.toRepresentation.asAlgebraHom a) x).val +
        ((σ.toRepresentation.asAlgebraHom b) x).val = _ + _
      rw [ha, hb]
    | single g c =>
      rw [Representation.asAlgebraHom_single, Representation.asAlgebraHom_single]
      rfl

lemma subrep_irreducible_iff (σ : Subrepresentation ρ) :
    Representation.IsIrreducible σ.toRepresentation ↔ IsSimpleModule ℂ[G] σ.asSubmodule := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact ⟨fun _ => IsSimpleModule.congr (subrepModuleEquiv ρ σ).symm,
    fun _ => IsSimpleModule.congr (subrepModuleEquiv ρ σ)⟩

noncomputable def subrepEquivOfModuleEquiv (σ τ : Subrepresentation ρ)
    (e : σ.asSubmodule ≃ₗ[ℂ[G]] τ.asSubmodule) :
    Representation.Equiv σ.toRepresentation τ.toRepresentation := by
  let e' := (subrepModuleEquiv ρ σ).trans (e.trans (subrepModuleEquiv ρ τ).symm)
  exact ((Representation.IntertwiningMap.equivLinearMapAsModule _ _).symm
    e'.toLinearMap).ofBijective e'.bijective

noncomputable def moduleEquivOfSubrepEquiv (σ τ : Subrepresentation ρ)
    (e : Representation.Equiv σ.toRepresentation τ.toRepresentation) :
    σ.asSubmodule ≃ₗ[ℂ[G]] τ.asSubmodule := by
  let f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ e.toIntertwiningMap
  let e' := LinearEquiv.ofBijective f e.bijective
  exact (subrepModuleEquiv ρ σ).symm.trans (e'.trans (subrepModuleEquiv ρ τ))

end ModuleTransport

lemma irreducible_equiv_of_character_eq {G V W : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ]
    (h : ρ.character = σ.character) : Nonempty (Representation.Equiv σ ρ) := by
  classical
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := G)).ne')
  have hself := Representation.char_orthonormal ρ ρ
  have hother := Representation.char_orthonormal ρ σ
  rw [h] at hself
  rw [h] at hother
  have he : Nonempty (ρ.Equiv ρ) := ⟨Representation.Equiv.refl ρ⟩
  simp only [he, ite_eq_left] at hself
  by_contra hn
  simp only [hn] at hother
  exact one_ne_zero (hself.symm.trans hother)

def OccurringTypes {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :=
  {χ : G → ℂ // ∃ σ : Subrepresentation ρ,
    Representation.IsIrreducible σ.toRepresentation ∧ χ = σ.toRepresentation.character}

end
end PartialPermutation
end

end OAI


