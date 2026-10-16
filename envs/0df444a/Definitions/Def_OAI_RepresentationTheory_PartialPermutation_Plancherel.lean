-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Plancherel
-- name    : OAI_RepresentationTheory_PartialPermutation_Plancherel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:59:37.002346+00:00
-- url     : https://prove2.me/theorems/2a304a14-3554-4501-9b2f-ae3d5196357d
-- title:
--   Irreducible representations indexed by the regular representation: completeness and the character sum identity
-- statement:
--   Let $G$ be a finite group. Let $\operatorname{Irr}(G)$ be the set of isotypic components of the left regular representation $\lambda$ of $G$ on $\ell^2(G)$ (complex functions on $G$, with $(\lambda(g)f)(h)=f(g^{-1}h)$), regarded as a module over the group algebra $\mathbb{C}[G]$. For $c\in\operatorname{Irr}(G)$ let $S_c\subseteq\ell^2(G)$ be the simple submodule chosen to represent the type of $c$, let $\pi_c$ be the restriction of $\lambda$ to $S_c$, and write $d_c=\dim_{\mathbb{C}}S_c$ for its degree and $\chi_c(g)=\operatorname{tr}\pi_c(g)$ for its character. For $a\colon G\to\mathbb{C}$ and a representation $\rho$ write $\widehat{a}(\rho)=\sum_{g\in G}a(g)\rho(g)$, and let $\delta_1\in\ell^2(G)$ be the point mass at the identity.
--
--   1. **Recovering a function from its regular Fourier transform.** For every $a\colon G\to\mathbb{C}$, $\widehat{a}(\lambda)\,\delta_1=a$ as functions on $G$.
--   2. **Indexed irreducibles.** For $c\in\operatorname{Irr}(G)$, $\pi_c$ is the irreducible representation of $G$ with index $c$.
--   3. **Character sum identity.** For every $g\in G$ the identity displayed below holds.
--   4. **Completeness without repetition.** For every irreducible representation $\rho$ of $G$ on a finite-dimensional complex vector space there is exactly one $c\in\operatorname{Irr}(G)$ with $\pi_c\cong\rho$.
--
--   The character sum identity of item 3 reads
--
--   $$
--   \sum_{c\in\operatorname{Irr}(G)}\frac{d_c}{|G|}\,\chi_c(g^{-1})=\begin{cases}1,& g=1,\\ 0,& g\neq 1.\end{cases}
--   $$
--
--   Together these say that $(\pi_c)_{c\in\operatorname{Irr}(G)}$ is a complete list of irreducible representations of $G$ up to equivalence, with each equivalence class appearing exactly once, and item 3 is the Fourier inversion formula for the point mass at the identity (equivalently $\sum_c d_c\,\chi_c=|G|\,\delta_1$). This gives a concrete finite index set for sums over irreducible representations, such as $\sum_c d_c^{-u}$.
--
--   **Formalization Note** $\operatorname{Irr}(G)$ is `IrreducibleIndex G` and $d_c$ is `irreducibleDegree c` from the base definitions; $\pi_c$ is the abbreviation `irreducibleRep c` for `componentRep (regularRep G) c`. Items 1, 3, 4 are `complexFourier_regular_delta`, `sum_regular_character_kernels` (stated as a sum of the central character kernels of the $\pi_c$) and `irreducibleRep_complete` (a unique-existence statement). The private lemma `ite_eq_right` restates `if_neg`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/Plancherel.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/Plancherel.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the PartialPermutation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ModuleTransport
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Components
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CentralKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CompleteKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RegularRepresentation

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

namespace PartialPermutation
noncomputable section
open scoped BigOperators MonoidAlgebra Classical

variable {G : Type*} [Group G] [Fintype G]

lemma complexFourier_regular_delta (a : G → ℂ) (g : G) :
    complexFourier (regularRep G) a (deltaOne G) g = a g := by
  simp [complexFourier, deltaOne, inv_mul_eq_one, eq_comm]

abbrev irreducibleRep (c : IrreducibleIndex G) := componentRep (regularRep G) c

lemma sum_regular_character_kernels (g : G) :
    ∑ c : IrreducibleIndex G, centralCharacterKernel (irreducibleRep c) g =
      if g = 1 then 1 else 0 := by
  have ht := congrArg (fun A : Module.End ℂ (EuclideanSpace ℂ G) => A (deltaOne G) g)
    (sum_character_kernels_identity (regularRep G))
  rw [complexFourier_regular_delta] at ht
  exact ht

lemma irreducibleRep_complete {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ] :
    ∃! c : IrreducibleIndex G, Nonempty (Representation.Equiv (irreducibleRep c) ρ) := by
  have : Nontrivial V := IsSimpleModule.nontrivial ℂ[G] ρ.asModule
  have hex : ∃ c : IrreducibleIndex G, Nonempty (Representation.Equiv (irreducibleRep c) ρ) := by
    by_contra hn
    push Not at hn
    have hs : complexFourier ρ (fun g => ∑ c : IrreducibleIndex G,
        centralCharacterKernel (irreducibleRep c) g) = 1 := by
      simp only [sum_regular_character_kernels]
      simp [complexFourier]
    rw [complexFourier_sum] at hs
    have hz : (∑ c : IrreducibleIndex G, complexFourier ρ
        (centralCharacterKernel (irreducibleRep c))) = 0 := by
      apply Finset.sum_eq_zero
      intro c _
      rw [centralCharacterKernel_fourier, ite_eq_right (fun ⟨e⟩ => (hn c).false e)]
    rw [hz] at hs
    exact zero_ne_one hs
  obtain ⟨c, hc⟩ := hex
  refine ⟨c, hc, ?_⟩
  intro d hd
  obtain ⟨e⟩ := hc
  obtain ⟨f⟩ := hd
  exact (componentRep_equiv_iff (regularRep G) d c).mp ⟨f.trans e.symm⟩

end
end PartialPermutation
end

end OAI


