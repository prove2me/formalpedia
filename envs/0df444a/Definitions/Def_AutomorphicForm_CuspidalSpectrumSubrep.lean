-- Prove2me | Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
-- name    : AutomorphicForm_CuspidalSpectrumSubrep
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/f3292003-dcbd-5141-a56f-23b52b367c0b
-- title:
--   Closed and irreducible cuspidal subrepresentations of the weighted carrier
-- statement:
--   Throughout, $F$ is a number field, $\alpha,\beta$ are reals, $\Phi_0 \subseteq \mathrm{GL}_2(\mathbb{A}_F)$ carries a witness $h_{\Phi_0}$ that it is a slab fundamental domain (that is, $0<\alpha<\beta$, $\Phi_0$ lies in the set where the idelic norm of the determinant belongs to $[\alpha,\beta]$, and $\Phi_0$ is a fundamental domain for the global points acting on that slab with respect to the restricted adelic Haar measure), $\sigma \in \mathbb{R}$, and $\xi$ is a homomorphism from the full unit group of $\mathbb{A}_F$, viewed as the top subgroup, to $\mathbb{C}^\times$. The ambient Hilbert space is `cuspSubcarrier`, the closure inside the weighted $L^2$-space on $\Phi_0$ of the image of the continuous smooth cuspidal $\xi$-members. First, `IsCuspLift` is a relation between an arbitrary operation `op` on functions $\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ and a continuous $\mathbb{C}$-linear endomorphism $S$ of that subcarrier: it asserts that for every member $\varphi$ of `cuspMemberSubmodule` and every proof that `op` $\varphi$ is again such a member, $S$ sends the class of $\varphi$ to the class of `op` $\varphi$. Thus no lift is constructed; stability is demanded against all lifts. Two helper results record that this unfolds to itself and that it follows from the existential form 'for each $\varphi$ there is a membership witness with the identity holding'. Second, `IsClosedCuspSubrep` is a structure on a $\mathbb{C}$-submodule $M$ of the subcarrier with four fields: $M$ is topologically closed; and $M$ is mapped into itself by every continuous operator lifting right translation by a finite-adelic element, by every continuous operator lifting right translation by the inclusion at an infinite place $w$ of an element of `rowIsometrySubgroup₀` of $w$'s completion, and by every continuous operator lifting right convolution by a function $f$ that is a factorizable test function and is archimedean bi-finite for some archimedean type family. Third, `IsIrreducibleCuspSubrep` asserts that $M$ is such a closed subrepresentation, $M \ne \bot$, and every closed cuspidal subrepresentation contained in $M$ equals $\bot$ or $M$. Accompanying lemmas: $\top$ and $\bot$ are closed cuspidal subrepresentations, $\bot$ is not irreducible, an irreducible one is closed and non-zero, and the intersection of two closed cuspidal subrepresentations is again one.
--
--   **Relation to Mathlib.** Mathlib has no notion of cuspidal subrepresentation of an adelic $L^2$-carrier; these predicates are the project's own, phrased with Mathlib's `Submodule`, `IsClosed` and continuous linear maps.
--
--   **Where it is used.** These are the Hilbert-space counterparts of the function-level notions `IsCuspSubrep` and `IsCuspConstituent`, used when an eigenvector of a compact smoothing operator is decomposed into irreducible closed pieces and when such pieces are matched with cuspidal constituents carrying a Hecke eigensystem, on the automorphic side of the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_CuspidalSpectrumSubrep.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm.CuspidalConstituent

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace AutomorphicForm

namespace CuspidalSpectrum

variable (F : Type) [Field F] [NumberField F]

def IsCuspLift {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (op : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ))
    (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Prop :=
  ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) (h : op φ ∈ cuspMemberSubmodule F Φ₀ ξ),
    S (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨op φ, h⟩

theorem isCuspLift_iff {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (op : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ))
    (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) :
    IsCuspLift F hΦ₀ σ ξ op S ↔
      ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) (h : op φ ∈ cuspMemberSubmodule F Φ₀ ξ),
        S (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨op φ, h⟩ := Iff.rfl

theorem isCuspLift_of_forall_exists {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (op : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ))
    (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hS : ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ), ∃ h : op φ ∈ cuspMemberSubmodule F Φ₀ ξ,
      S (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨op φ, h⟩) :
    IsCuspLift F hΦ₀ σ ξ op S := fun φ h => by
  obtain ⟨h', e⟩ := hS φ
  exact e

structure IsClosedCuspSubrep {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Prop where
  isClosed : IsClosed (M : Set ↥(cuspSubcarrier F hΦ₀ σ ξ))
  map_le_of_rightTranslate_fin : ∀ g ∈ finiteAdelicGL2Subgroup F,
    ∀ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      IsCuspLift F hΦ₀ σ ξ (rightTranslate F g) S →
        M.map (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ M
  map_le_of_rightTranslate_arch : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
    ∀ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      IsCuspLift F hΦ₀ σ ξ (rightTranslate F (rowIsometryInclAt₀ F w k)) S →
        M.map (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ M
  map_le_of_rightConv : ∀ (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F),
    IsFactorizableTestFn F f → IsArchBiFinite F tys f →
      ∀ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
        IsCuspLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) S →
          M.map (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ M

def IsIrreducibleCuspSubrep {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Prop :=
  IsClosedCuspSubrep F hΦ₀ σ ξ M ∧ M ≠ ⊥ ∧
    ∀ M' : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ), IsClosedCuspSubrep F hΦ₀ σ ξ M' → M' ≤ M → M' = ⊥ ∨ M' = M

theorem isClosedCuspSubrep_top {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) : IsClosedCuspSubrep F hΦ₀ σ ξ ⊤ :=
  ⟨isClosed_univ, fun _ _ _ _ => le_top, fun _ _ _ _ => le_top, fun _ _ _ _ _ _ => le_top⟩

theorem isClosedCuspSubrep_bot {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) : IsClosedCuspSubrep F hΦ₀ σ ξ ⊥ :=
  ⟨by simp, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp, fun _ _ _ _ _ _ => by simp⟩

theorem not_isIrreducibleCuspSubrep_bot {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) :
    ¬ IsIrreducibleCuspSubrep F hΦ₀ σ ξ ⊥ := fun h => h.2.1 rfl

theorem IsIrreducibleCuspSubrep.isClosedCuspSubrep {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    {hΦ₀ : IsSlabFundamentalDomain F α β Φ₀} {σ : ℝ} {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ}
    {M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)} (h : IsIrreducibleCuspSubrep F hΦ₀ σ ξ M) :
    IsClosedCuspSubrep F hΦ₀ σ ξ M := h.1

theorem IsIrreducibleCuspSubrep.ne_bot {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    {hΦ₀ : IsSlabFundamentalDomain F α β Φ₀} {σ : ℝ} {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ}
    {M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)} (h : IsIrreducibleCuspSubrep F hΦ₀ σ ξ M) : M ≠ ⊥ := h.2.1

theorem IsClosedCuspSubrep.inf {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    {hΦ₀ : IsSlabFundamentalDomain F α β Φ₀} {σ : ℝ} {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ}
    {M M' : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)}
    (h : IsClosedCuspSubrep F hΦ₀ σ ξ M) (h' : IsClosedCuspSubrep F hΦ₀ σ ξ M') :
    IsClosedCuspSubrep F hΦ₀ σ ξ (M ⊓ M') := by
  refine ⟨h.isClosed.inter h'.isClosed, fun g hg S hS => ?_, fun w k S hS => ?_, fun f tys hf hft S hS => ?_⟩
  · exact le_inf ((Submodule.map_mono inf_le_left).trans (h.map_le_of_rightTranslate_fin g hg S hS))
      ((Submodule.map_mono inf_le_right).trans (h'.map_le_of_rightTranslate_fin g hg S hS))
  · exact le_inf ((Submodule.map_mono inf_le_left).trans (h.map_le_of_rightTranslate_arch w k S hS))
      ((Submodule.map_mono inf_le_right).trans (h'.map_le_of_rightTranslate_arch w k S hS))
  · exact le_inf ((Submodule.map_mono inf_le_left).trans (h.map_le_of_rightConv f tys hf hft S hS))
      ((Submodule.map_mono inf_le_right).trans (h'.map_le_of_rightConv f tys hf hft S hS))

end CuspidalSpectrum

end AutomorphicForm

end


