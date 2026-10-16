-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CentralKernels
-- name    : OAI_RepresentationTheory_PartialPermutation_CentralKernels
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:55:18.022403+00:00
-- url     : https://prove2.me/theorems/d87dbc1b-983e-42bb-96ce-8ab9f7e6d90b
-- title:
--   Central character kernels and their Fourier transforms at irreducible representations
-- statement:
--   Let $G$ be a finite group. For a representation $\rho$ of $G$ on a complex vector space $V$ and a function $a\colon G\to\mathbb{C}$, the Fourier transform of $a$ at $\rho$ is the operator
--
--   $$
--   \widehat{a}(\rho)=\sum_{g\in G}a(g)\,\rho(g)\in\operatorname{End}_{\mathbb{C}}(V).
--   $$
--
--   A function $a$ is a class function if $a(gh)=a(hg)$ for all $g,h\in G$. For a representation $\rho$ on a finite-dimensional space $V$ with character $\chi_\rho(g)=\operatorname{tr}\rho(g)$, the central character kernel of $\rho$ is the function $e_\rho\colon G\to\mathbb{C}$,
--
--   $$
--   e_\rho(g)=\frac{\dim V}{|G|}\,\chi_\rho(g^{-1}).
--   $$
--
--   1. **Class functions give intertwiners.** If $a$ is a class function, then $\widehat{a}(\rho)\,\rho(g)=\rho(g)\,\widehat{a}(\rho)$ for every $g\in G$, for any representation $\rho$.
--   2. **Schur's lemma for class functions.** If moreover $V$ is finite-dimensional and $\rho$ is irreducible, then $\widehat{a}(\rho)=c\,I_V$ for some scalar $c\in\mathbb{C}$.
--   3. **Central character kernel.** The function $e_\rho$ defined above.
--   4. **$e_\rho$ is a class function:** $e_\rho(gh)=e_\rho(hg)$ for all $g,h\in G$.
--   5. **Orthogonality in Fourier form.** If $\rho$ (on $V$) and $\sigma$ (on $W$) are irreducible representations on finite-dimensional complex vector spaces, then $\widehat{e_\rho}(\sigma)=I_W$ when $\rho\cong\sigma$, and $\widehat{e_\rho}(\sigma)=0$ otherwise.
--
--   The kernel $e_\rho$ is the function on $G$ corresponding to the central idempotent of $\mathbb{C}[G]$ attached to the irreducible type of $\rho$: by item 5 it acts as the identity on representations of that type and annihilates every other irreducible representation. This is the basis of the Fourier inversion and Plancherel formulas for finite groups.
--
--   **Formalization Note** The Fourier transform is `complexFourier ρ a` from the base definitions; the kernel is `centralCharacterKernel ρ`, where $\dim V$ is `Module.finrank` cast to $\mathbb{C}$ and the division is in $\mathbb{C}$. Items 1, 2, 4, 5 are `centralFourier_commute`, `centralFourier_scalar`, `centralCharacterKernel_comm` and `centralCharacterKernel_fourier` (an if-then-else on the existence of an equivalence $\rho\cong\sigma$). The private lemmas `ite_eq_left` and `ite_eq_right` restate `if_pos` and `if_neg`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/CentralKernels.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/CentralKernels.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the PartialPermutation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ModuleTransport
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Components

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

section CentralFourier
variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)

omit [FiniteDimensional ℂ V] in
lemma centralFourier_commute (a : G → ℂ)
    (ha : ∀ g h, a (g * h) = a (h * g)) (g : G) :
    complexFourier ρ a * ρ g = ρ g * complexFourier ρ a := by
  classical
  simp only [complexFourier, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, ← map_mul]
  calc
    _ = ∑ h : G, a (g * h * g⁻¹) • ρ (g * h * g⁻¹ * g) := by
      exact (Fintype.sum_equiv (Equiv.mulLeft g |>.trans (Equiv.mulRight g⁻¹)) _ _
        (fun h => rfl)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h _
      rw [ha (g * h) g⁻¹]
      simp [mul_assoc]

lemma centralFourier_scalar [Representation.IsIrreducible ρ] (a : G → ℂ)
    (ha : ∀ g h, a (g * h) = a (h * g)) :
    ∃ c : ℂ, complexFourier ρ a = c • (1 : Module.End ℂ V) := by
  let T : Representation.IntertwiningMap ρ ρ :=
    { toLinearMap := complexFourier ρ a
      isIntertwining' := fun g => by
        simpa only [Module.End.mul_eq_comp] using centralFourier_commute ρ a ha g }
  obtain ⟨c, hc⟩ := Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ) |>.surjective T
  refine ⟨c, ?_⟩
  rw [Representation.IntertwiningMap.algebraMap_apply] at hc
  exact (congrArg Representation.IntertwiningMap.toLinearMap hc).symm

end CentralFourier

def centralCharacterKernel {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) : ℂ :=
  (Module.finrank ℂ V : ℂ) / Fintype.card G * ρ.character g⁻¹

lemma centralCharacterKernel_comm {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g h : G) :
    centralCharacterKernel ρ (g * h) = centralCharacterKernel ρ (h * g) := by
  simp only [centralCharacterKernel, mul_inv_rev]
  rw [Representation.char_mul_comm]

lemma centralCharacterKernel_fourier {G V W : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ] :
    complexFourier σ (centralCharacterKernel ρ) =
      if Nonempty (Representation.Equiv ρ σ) then 1 else 0 := by
  classical
  obtain ⟨c, hc⟩ := centralFourier_scalar σ (centralCharacterKernel ρ)
    (centralCharacterKernel_comm ρ)
  have : Nontrivial W := IsSimpleModule.nontrivial ℂ[G] σ.asModule
  have hD : (Module.finrank ℂ W : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := W)).ne'
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := G)).ne')
  have ht := congrArg (LinearMap.trace ℂ W) hc
  have ho := Representation.char_orthonormal σ ρ
  have htrace : LinearMap.trace ℂ W (complexFourier σ (centralCharacterKernel ρ)) =
      (Module.finrank ℂ V : ℂ) *
        (if Nonempty (Representation.Equiv ρ σ) then 1 else 0) := by
    simp only [complexFourier, map_sum, map_smul, smul_eq_mul, centralCharacterKernel]
    change (∑ g, (Module.finrank ℂ V : ℂ) / Fintype.card G *
      ρ.character g⁻¹ * σ.character g) = _
    calc
      _ = (Module.finrank ℂ V : ℂ) * ((Fintype.card G : ℂ)⁻¹ *
          ∑ g, σ.character g * ρ.character g⁻¹) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g _
        ring
      _ = _ := by rw [Fintype.card_eq_nat_card, ho]
  rw [htrace, map_smul, LinearMap.trace_one, smul_eq_mul] at ht
  split_ifs with he
  · obtain ⟨e⟩ := he
    have hd := e.toLinearEquiv.finrank_eq
    have hcd : c = 1 := by
      rw [ite_eq_left ⟨e⟩, mul_one, hd] at ht
      apply (mul_right_cancel₀ hD)
      simpa using ht.symm
    simpa [hcd] using hc
  · have hcd : c = 0 := by
      rw [ite_eq_right he, mul_zero] at ht
      exact (mul_eq_zero.mp ht.symm).resolve_right hD
    simpa [hcd] using hc

end
end PartialPermutation
end

end OAI


