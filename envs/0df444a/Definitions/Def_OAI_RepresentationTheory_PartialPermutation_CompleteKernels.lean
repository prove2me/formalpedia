-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CompleteKernels
-- name    : OAI_RepresentationTheory_PartialPermutation_CompleteKernels
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:56:20.997261+00:00
-- url     : https://prove2.me/theorems/23eb1590-a70a-4f69-a59e-069ac40fe9db
-- title:
--   Component representations and the completeness identity for central character kernels
-- statement:
--   Let $G$ be a finite group, $V$ a finite-dimensional complex vector space and $\rho$ a representation of $G$ on $V$, regarded as a module over the group algebra $\mathbb{C}[G]$. For each isotypic component $c$ of this module let $S_c\subseteq V$ be the simple submodule chosen to represent its type, and let $\rho_c$ be the restriction of $\rho$ to $S_c$ (the component representation of $c$). For $a\colon G\to\mathbb{C}$ write $\widehat{a}(\rho)=\sum_{g\in G}a(g)\rho(g)$, and for a representation $\pi$ on a finite-dimensional space $U$ write $e_\pi(g)=\frac{\dim U}{|G|}\chi_\pi(g^{-1})$ for its central character kernel, where $\chi_\pi(g)=\operatorname{tr}\pi(g)$.
--
--   1. **Component representations.** For every isotypic component $c$, the representation $\rho_c$ is irreducible, and for components $c,d$ one has $\rho_c\cong\rho_d$ if and only if $c=d$.
--   2. **Restriction to subrepresentations.** If $W\subseteq V$ is a $\rho$-invariant subspace and $x\in W$, then $\widehat{a}(\rho|_W)\,x=\widehat{a}(\rho)\,x$ for every $a\colon G\to\mathbb{C}$.
--   3. **Linearity.** For a finite family of functions $a_i\colon G\to\mathbb{C}$, $i\in I$, the Fourier transform of $g\mapsto\sum_i a_i(g)$ is $\sum_i\widehat{a_i}(\rho)$.
--   4. **Completeness of the kernels.** Summing the central character kernels of all component representations gives a function whose Fourier transform at $\rho$ is the identity:
--
--   $$
--   \sum_{g\in G}\Big(\sum_{c}e_{\rho_c}(g)\Big)\rho(g)=I_V,
--   $$
--
--   where $c$ runs over all isotypic components of $V$.
--
--   Thus the sum of the central idempotents of the irreducible types occurring in $\rho$ acts as the identity on $V$, a resolution of the identity along irreducible types. Applied to the regular representation this yields the character form of Fourier inversion and the completeness of the list of irreducible representations.
--
--   **Formalization Note** The component representation is `componentRep ρ c`, the representation on `componentSimple ρ c`, and its irreducibility is the instance `componentRep_irreducible`; the other items are `componentRep_equiv_iff`, `complexFourier_subrep`, `complexFourier_sum` and `sum_character_kernels_identity`. The last one takes a `Fintype` structure on the set of isotypic components as an argument (such a structure exists, since this set is finite). The private lemmas `ite_eq_left` and `ite_eq_right` restate `if_pos` and `if_neg`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/CompleteKernels.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/CompleteKernels.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the PartialPermutation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ModuleTransport
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Components
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CentralKernels

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators

namespace PartialPermutation
noncomputable section
open scoped MonoidAlgebra BigOperators

section CompleteKernels
variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)

def componentRep (c : isotypicComponents ℂ[G] ρ.asModule) :=
  (Subrepresentation.ofSubmodule' (componentSimple ρ c)).toRepresentation

instance componentRep_irreducible (c : isotypicComponents ℂ[G] ρ.asModule) :
    Representation.IsIrreducible (componentRep ρ c) :=
  (subrep_irreducible_iff ρ _).mpr (componentSimple_simple ρ c)

lemma componentRep_equiv_iff (c d : isotypicComponents ℂ[G] ρ.asModule) :
    Nonempty (Representation.Equiv (componentRep ρ c) (componentRep ρ d)) ↔ c = d := by
  constructor
  · rintro ⟨e⟩
    apply componentCharacter_injective ρ
    exact Subtype.ext (Representation.char_iso e)
  · rintro rfl
    exact ⟨Representation.Equiv.refl _⟩

omit [FiniteDimensional ℂ V] in
lemma complexFourier_subrep (σ : Subrepresentation ρ) (a : G → ℂ) (x : σ) :
    ((complexFourier σ.toRepresentation a x : σ) : V) = complexFourier ρ a x := by
  simp only [complexFourier, LinearMap.sum_apply, LinearMap.smul_apply,
    Submodule.coe_sum, Submodule.coe_smul]
  rfl

omit [FiniteDimensional ℂ V] in
lemma complexFourier_sum {ι : Type*} [Fintype ι] (a : ι → G → ℂ) :
    complexFourier ρ (fun g => ∑ i, a i g) = ∑ i, complexFourier ρ (a i) := by
  simp only [complexFourier, Finset.sum_smul]
  exact Finset.sum_comm

lemma sum_character_kernels_identity
    [Fintype (isotypicComponents ℂ[G] ρ.asModule)] :
    complexFourier ρ (fun g => ∑ c, centralCharacterKernel (componentRep ρ c) g) = 1 := by
  classical
  let K : G → ℂ := fun g => ∑ c, centralCharacterKernel (componentRep ρ c) g
  have hs (σ : Subrepresentation ρ) [Representation.IsIrreducible σ.toRepresentation] :
      complexFourier σ.toRepresentation K = 1 := by
    let χ : OccurringTypes ρ := ⟨σ.toRepresentation.character, σ, inferInstance, rfl⟩
    obtain ⟨c, hc⟩ := componentCharacter_surjective ρ χ
    have he : Nonempty (Representation.Equiv (componentRep ρ c) σ.toRepresentation) := by
      exact irreducible_equiv_of_character_eq σ.toRepresentation (componentRep ρ c)
        (congrArg Subtype.val hc).symm
    rw [complexFourier_sum]
    rw [Finset.sum_eq_single c]
    · rw [centralCharacterKernel_fourier, ite_eq_left he]
    · intro d _ hdc
      rw [centralCharacterKernel_fourier, ite_eq_right]
      rintro ⟨e⟩
      obtain ⟨ec⟩ := he
      exact hdc ((componentRep_equiv_iff ρ d c).mp ⟨e.trans ec.symm⟩)
    · simp
  let E (S : {S : Submodule ℂ[G] ρ.asModule // IsSimpleModule ℂ[G] S}) : Submodule ℂ V :=
    S.val.restrictScalars ℂ
  have htop : (⨆ S, E S) = ⊤ := by
    change (⨆ S : {S : Submodule ℂ[G] ρ.asModule // IsSimpleModule ℂ[G] S},
      S.val.restrictScalars ℂ) = ⊤
    rw [← Submodule.restrictScalars_iSup]
    have ht : (⨆ S : {S : Submodule ℂ[G] ρ.asModule // IsSimpleModule ℂ[G] S}, S.val) = ⊤ :=
      (sSup_eq_iSup' {S : Submodule ℂ[G] ρ.asModule | IsSimpleModule ℂ[G] S}).symm.trans
        (IsSemisimpleModule.sSup_simples_eq_top ℂ[G] ρ.asModule)
    rw [ht, Submodule.restrictScalars_top]
  have hker : (⊤ : Submodule ℂ V) ≤ LinearMap.ker (complexFourier ρ K - 1) := by
    rw [← htop]
    refine iSup_le fun S => ?_
    intro x hx
    let σ := Subrepresentation.ofSubmodule' S.val
    have : Representation.IsIrreducible σ.toRepresentation :=
      (subrep_irreducible_iff ρ σ).mpr S.property
    have ht := congrArg (fun A : Module.End ℂ σ.toSubmodule => ((A ⟨x, hx⟩ : σ.toSubmodule) : V)) (hs σ)
    rw [complexFourier_subrep] at ht
    simpa using sub_eq_zero.mpr ht
  ext x
  have hx := hker (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ V))
  simpa [LinearMap.mem_ker, sub_eq_zero] using hx

end CompleteKernels
end
end PartialPermutation

end

end OAI


