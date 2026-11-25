-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
-- name    : GroundTheory_GlobalFields_SemilocalAlgebras_Galois
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:29:01.891264+00:00
-- url     : https://prove2.me/theorems/9443ef14-3741-4258-9232-4c58b7b1dcb0
-- title:
--   Galois
-- statement:
--   Definitions and structural lemmas for Galois, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Galois.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7


set_option autoImplicit false
namespace GroundTheory.Global
open IsDedekindDomain NumberField WithZero Topology Filter TensorProduct
open scoped Pointwise
noncomputable section
namespace SemiLocal
variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]
section Action
instance : SMulCommClass (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) where
  smul_comm σ a x := by
    apply RingOfIntegers.ext
    have h : ∀ y : 𝓞 L, ((a • y : 𝓞 L) : L) = algebraMap K L (a : K) * (y : L) := fun y ↦ by
      rw [Algebra.smul_def]
      change algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) a * y) = _
      rw [map_mul, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
        IsScalarTower.algebraMap_apply (𝓞 K) K L]
    change σ ((a • x : 𝓞 L) : L) = ((a • (σ • x) : 𝓞 L) : L)
    rw [h, h, map_mul, AlgEquiv.commutes]
    rfl
instance : MulAction (L ≃ₐ[K] L) (HeightOneSpectrum (𝓞 L)) where
  smul σ w := ⟨σ • w.asIdeal, inferInstance, by
    intro h
    apply w.ne_bot
    rw [← inv_smul_smul σ w.asIdeal, h, Ideal.pointwise_smul_def, Ideal.map_bot]⟩
  one_smul w := HeightOneSpectrum.ext (one_smul _ w.asIdeal)
  mul_smul σ τ w := HeightOneSpectrum.ext (mul_smul σ τ w.asIdeal)
omit [NumberField L] in
theorem smul_asIdeal (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    (σ • w).asIdeal = σ • w.asIdeal := rfl
theorem intValuation_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) (x : 𝓞 L) :
    (σ • w).intValuation (σ • x) = w.intValuation x := by
  by_cases hx : x = 0
  · subst hx
    simp
  have hσx : σ • x ≠ 0 := fun h ↦ hx (by rw [← inv_smul_smul σ x, h, smul_zero])
  have key : ∀ n : ℕ, (σ • w).intValuation (σ • x) ≤ exp (-(n : ℤ)) ↔
      w.intValuation x ≤ exp (-(n : ℤ)) := by
    intro n
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem,
      HeightOneSpectrum.intValuation_le_pow_iff_mem, smul_asIdeal, ← smul_pow',
      Ideal.smul_mem_pointwise_smul_iff]
  rw [HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hσx,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hx] at key ⊢
  simp only [exp_le_exp, neg_le_neg_iff, Nat.cast_le] at key
  rw [le_antisymm ((key _).1 le_rfl) ((key _).2 le_rfl)]
theorem valuation_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) (x : L) :
    (σ • w).valuation L (σ x) = w.valuation L x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
  have h : ∀ c : 𝓞 L, σ (algebraMap (𝓞 L) L c) = algebraMap (𝓞 L) L (σ • c) := fun _ ↦ rfl
  rw [map_div₀, map_div₀, map_div₀, h, h, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_smul, intValuation_smul]
theorem absNorm_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    Ideal.absNorm (σ • w).asIdeal = Ideal.absNorm w.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv w.asIdeal (σ • w).asIdeal
    (MulSemiringAction.toRingEquiv _ (𝓞 L) σ)
    (by rw [smul_asIdeal, Ideal.pointwise_smul_def]; rfl)).toEquiv.symm
theorem norm_algebraMap_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) (x : L) :
    ‖algebraMap L ((σ • w).adicCompletion L) (σ x)‖ = ‖algebraMap L (w.adicCompletion L) x‖ := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion, HeightOneSpectrum.algebraMap_adicCompletion,
    Function.comp_apply, Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply,
    RingHom.id_apply, ← FinitePlace.embedding_apply, ← FinitePlace.embedding_apply,
    FinitePlace.norm_embedding', FinitePlace.norm_embedding', valuation_smul]
  have : ∀ (e₁ e₂ : NNReal) (h₁ : e₁ ≠ 0) (h₂ : e₂ ≠ 0), e₁ = e₂ → ∀ c : ℤᵐ⁰,
      WithZeroMulInt.toNNReal h₁ c = WithZeroMulInt.toNNReal h₂ c := by
    rintro _ _ _ _ rfl _
    rfl
  rw [this _ _ _ _ (by rw [absNorm_smul])]
variable [NumberField K] (v : HeightOneSpectrum (𝓞 K))
instance : MulAction (L ≃ₐ[K] L) (PlacesOver L v) where
  smul σ w := ⟨σ • w.1, show (σ • w.1.asIdeal).LiesOver v.asIdeal from inferInstance⟩
  one_smul w := Subtype.ext (one_smul _ w.1)
  mul_smul σ τ w := Subtype.ext (mul_smul σ τ w.1)
omit [NumberField K] [NumberField L] in
@[simp] theorem coe_smul_placesOver (σ : L ≃ₐ[K] L) (w : PlacesOver L v) :
    (σ • w).1 = σ • w.1 := rfl
instance [IsGalois K L] : MulAction.IsPretransitive (L ≃ₐ[K] L) (PlacesOver L v) where
  exists_smul_eq w₁ w₂ := by
    obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal w₁.1.asIdeal w₂.1.asIdeal
      (L ≃ₐ[K] L)
    exact ⟨σ, Subtype.ext (HeightOneSpectrum.ext hσ)⟩
end Action
section Completion
def galoisCompletionMap (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L)) :
    WithVal (w.valuation L) →+* w'.adicCompletion L :=
  (algebraMap L (w'.adicCompletion L)).comp
    (σ.toRingEquiv.toRingHom.comp (WithVal.equiv (w.valuation L)).toRingHom)
theorem isUniformInducing_algebraMap_withVal (w : HeightOneSpectrum (𝓞 L)) :
    IsUniformInducing (fun x : WithVal (w.valuation L) ↦
      algebraMap L (w.adicCompletion L) (WithVal.equiv _ x)) :=
  (HeightOneSpectrum.adicCompletion.uniformEquiv L w).symm.isUniformEmbedding.isUniformInducing.comp
    (UniformSpace.Completion.isUniformInducing_coe _)
theorem uniformContinuous_galoisCompletionMap (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L))
    (h : w' = σ • w) : UniformContinuous (galoisCompletionMap σ w w') := by
  subst h
  rw [UniformContinuous, ← (isUniformInducing_algebraMap_withVal w).comap_uniformity,
    ((Metric.uniformity_basis_dist).comap _).tendsto_iff Metric.uniformity_basis_dist]
  intro ε hε
  refine ⟨ε, hε, fun p hp ↦ ?_⟩
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, dist_eq_norm] at hp ⊢
  rw [← map_sub, ← map_sub] at hp
  rw [← map_sub]
  simp only [galoisCompletionMap, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv]
  rwa [norm_algebraMap_smul]
def galHom (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L)) (h : w' = σ • w) :
    w.adicCompletion L →+* w'.adicCompletion L :=
  (UniformSpace.Completion.extensionHom (galoisCompletionMap σ w w')
      (uniformContinuous_galoisCompletionMap σ w w' h).continuous).comp
    (HeightOneSpectrum.adicCompletion.equiv L w).toRingHom
theorem continuous_galHom (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L)) (h : w' = σ • w) :
    Continuous (galHom σ w w' h) :=
  UniformSpace.Completion.continuous_extension.comp
    (HeightOneSpectrum.adicCompletion.continuous_toCompletion L w)
theorem galHom_algebraMap (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L)) (h : w' = σ • w)
    (x : L) : galHom σ w w' h (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w'.adicCompletion L) (σ x) := by
  change UniformSpace.Completion.extensionHom (galoisCompletionMap σ w w')
    (uniformContinuous_galoisCompletionMap σ w w' h).continuous
    ((WithVal.equiv (w.valuation L)).symm x : UniformSpace.Completion _) = _
  rw [UniformSpace.Completion.extensionHom_coe]
  rfl
theorem galHom_comp_galHom (σ τ : L ≃ₐ[K] L) (hστ : τ * σ = 1) (w w' : HeightOneSpectrum (𝓞 L))
    (h : w' = σ • w) (h' : w = τ • w') :
    (galHom τ w' w h').comp (galHom σ w w' h) = RingHom.id _ := by
  have := (HeightOneSpectrum.denseRange_algebraMap L w).equalizer
    ((continuous_galHom τ w' w h').comp (continuous_galHom σ w w' h)) continuous_id
    (funext fun x ↦ by
      simp only [Function.comp_apply, galHom_algebraMap, id_eq]
      rw [← AlgEquiv.mul_apply, hστ, AlgEquiv.one_apply])
  exact RingHom.ext (congrFun this)
variable [NumberField K] (v : HeightOneSpectrum (𝓞 K))
theorem galHom_completionMap (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v.asIdeal] (h : w' = σ • w)
    (a : v.adicCompletion K) : galHom σ w w' h (completionMap v w a) = completionMap v w' a := by
  have := (HeightOneSpectrum.denseRange_algebraMap K v).equalizer
    ((continuous_galHom σ w w' h).comp (continuous_completionMap v w))
    (continuous_completionMap v w')
    (funext fun x ↦ by
      simp only [Function.comp_apply, completionMap_algebraMap,
        IsScalarTower.algebraMap_apply K L (w.adicCompletion L),
        IsScalarTower.algebraMap_apply K L (w'.adicCompletion L), galHom_algebraMap,
        AlgEquiv.commutes])
  exact congrFun this a
def galEquiv (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    [w'.asIdeal.LiesOver v.asIdeal] (h : w' = σ • w) :
    w.adicCompletion L ≃ₐ[v.adicCompletion K] w'.adicCompletion L :=
  AlgEquiv.ofRingEquiv
    (f := RingEquiv.ofRingHom (galHom σ w w' h) (galHom σ⁻¹ w' w (by rw [h, inv_smul_smul]))
      (galHom_comp_galHom σ⁻¹ σ (mul_inv_cancel σ) w' w _ h)
      (galHom_comp_galHom σ σ⁻¹ (inv_mul_cancel σ) w w' h _))
    (fun a ↦ galHom_completionMap v σ w w' h a)
theorem continuous_galEquiv (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v.asIdeal] (h : w' = σ • w) :
    Continuous (galEquiv v σ w w' h) :=
  continuous_galHom σ w w' h
theorem continuous_galEquiv_symm (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v.asIdeal] (h : w' = σ • w) :
    Continuous (galEquiv v σ w w' h).symm :=
  continuous_galHom σ⁻¹ w' w (by rw [h, inv_smul_smul])
def galContinuousEquiv (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v.asIdeal] (h : w' = σ • w) :
    ContinuousAlgEquiv (v.adicCompletion K) (w.adicCompletion L) (w'.adicCompletion L) where
  toAlgEquiv := galEquiv v σ w w' h
  continuous_toFun := continuous_galEquiv v σ w w' h
  continuous_invFun := continuous_galEquiv_symm v σ w w' h
end Completion
section Product
variable [NumberField K] (v : HeightOneSpectrum (𝓞 K))
omit [NumberField K] [NumberField L] in
theorem eq_smul_inv_smul (σ : L ≃ₐ[K] L) (u : PlacesOver L v) : u.1 = σ • (σ⁻¹ • u).1 := by
  rw [← coe_smul_placesOver, smul_inv_smul]
def piGal (σ : L ≃ₐ[K] L) : CompletionsOver L v →ₐ[v.adicCompletion K] CompletionsOver L v :=
  AlgHom.pi fun u ↦
    (galEquiv v σ (σ⁻¹ • u).1 u.1 (eq_smul_inv_smul v σ u)).toAlgHom.comp
      (Pi.evalAlgHom _ _ (σ⁻¹ • u))
end Product
end SemiLocal
end
end GroundTheory.Global


