-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsIndex
-- name    : GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsIndex
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T09:19:53.975029+00:00
-- url     : https://prove2.me/theorems/9e0650d5-303a-50e6-8eb7-a8e20a7e94bd
-- title:
--   Statements Index
-- statement:
--   Definitions and structural lemmas for Statements Index, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsIndex.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField IsDedekindDomain TensorProduct
open GroundTheory.Heights₂.Heights
universe u v
noncomputable section
section Scale
set_option linter.unusedSectionVars false
variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
def localScalar (v : HeightOneSpectrum (𝓞 K)) (b : 𝓞 K) : v.adicCompletion K :=
  (algebraMap (𝓞 K) (v.adicCompletionIntegers K) b : v.adicCompletion K)
theorem localScalar_eq (v : HeightOneSpectrum (𝓞 K)) (b : 𝓞 K) :
    localScalar v b = FinitePlace.embedding v (b : K) := rfl
theorem localScalar_ne_zero (v : HeightOneSpectrum (𝓞 K)) {b : 𝓞 K} (hb : b ≠ 0) :
    localScalar v b ≠ 0 := by
  rw [localScalar_eq]
  exact (map_ne_zero _).mpr (by exact_mod_cast hb)
def localSmul (v : HeightOneSpectrum (𝓞 K)) {b : 𝓞 K} (hb : b ≠ 0) :
    (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V) :=
  LinearEquiv.smulOfNeZero _ _ (localScalar v b) (localScalar_ne_zero v hb)
theorem toLocal_smul_eq (v : HeightOneSpectrum (𝓞 K)) (b : 𝓞 K) (x : V) :
    toLocal v (b • x) = localScalar v b • toLocal v x := by
  rw [← algebraMap_smul K b x, map_smul,
    ← algebraMap_smul (v.adicCompletion K) (algebraMap (𝓞 K) K b) (toLocal v x)]
  rfl
def smulSub (b : 𝓞 K) (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) V :=
  L.map (b • LinearMap.id)
theorem mem_smulSub_of_mem (b : 𝓞 K) {L : Submodule (𝓞 K) V} {x : V} (hx : x ∈ L) :
    b • x ∈ smulSub b L :=
  ⟨x, hx, rfl⟩
theorem smulSub_le (b : 𝓞 K) (L : Submodule (𝓞 K) V) : smulSub b L ≤ L := by
  rintro _ ⟨x, hx, rfl⟩
  exact L.smul_mem b hx
theorem localLattice_smulSub (v : HeightOneSpectrum (𝓞 K)) {b : 𝓞 K} (hb : b ≠ 0)
    (L : Submodule (𝓞 K) V) :
    (localLattice v (smulSub b L) : Set (v.adicCompletion K ⊗[K] V)) =
      localSmul v hb '' localLattice v L := by
  set f := ((localSmul v hb : (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] _).toLinearMap.restrictScalars
    (v.adicCompletionIntegers K))
  have h1 : toLocal v '' (smulSub b L : Set V) = f '' (toLocal v '' (L : Set V)) := by
    rw [Set.image_image]
    ext w
    simp only [Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      simp only [LinearMap.smul_apply, LinearMap.id_apply]
      rw [toLocal_smul_eq]
      rfl
    · rintro ⟨x, hx, rfl⟩
      refine ⟨b • x, mem_smulSub_of_mem b hx, ?_⟩
      rw [toLocal_smul_eq]
      rfl
  have h2 : localLattice v (smulSub b L) = (localLattice v L).map f := by
    rw [localLattice, localLattice, Submodule.map_span, h1]
  rw [h2, Submodule.map_coe]
  rfl
def scaledLattice (M : FullLattice K V) {b : 𝓞 K} (hb : b ≠ 0) : FullLattice K V where
  carrier := smulSub b M.carrier
  fg := M.fg.map _
  span_eq := by
    rw [eq_top_iff, ← M.span_eq, Submodule.span_le]
    intro x hx
    have hb' : (b : K) ≠ 0 := by exact_mod_cast hb
    have : x = (b : K)⁻¹ • (b • x) := by
      rw [← algebraMap_smul K b x, smul_smul]
      simp [hb']
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_smulSub_of_mem b hx))
end Scale
def LocalIndex.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (V : Type v) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M₁ M₂ : FullLattice K V)
    (g : ∀ v : HeightOneSpectrum (𝓞 K),
      (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)),
    M₂.carrier ≤ M₁.carrier →
    (∀ v, (localLattice v M₂.carrier : Set (v.adicCompletion K ⊗[K] V)) =
      g v '' localLattice v M₁.carrier) →
      (Nat.card (M₁.carrier ⧸ M₂.carrier.comap M₁.carrier.subtype) : ℝ) =
        ∏ᶠ v, ‖LinearMap.det
          ((g v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)))‖⁻¹
section Witness
variable (K : Type u) [Field K] [NumberField K]
theorem LocalIndex.witness :
    (scaledLattice (FullLattice.standard K 2) (two_ne_zero (α := 𝓞 K))).carrier ≤
        (FullLattice.standard K 2).carrier ∧
      ∀ v, (localLattice v (scaledLattice (FullLattice.standard K 2) (two_ne_zero (α := 𝓞 K))).carrier :
          Set (v.adicCompletion K ⊗[K] (Fin 2 → K))) = localSmul v (two_ne_zero (α := 𝓞 K)) '' localLattice v (FullLattice.standard K 2).carrier :=
  ⟨smulSub_le _ _, fun v ↦ localLattice_smulSub v _ _⟩
example := LocalIndex.witness ℚ
example := LocalIndex.witness GaussianField
end Witness
end
end GroundTheory.Heights₂.Heights.LatticeLemmas


