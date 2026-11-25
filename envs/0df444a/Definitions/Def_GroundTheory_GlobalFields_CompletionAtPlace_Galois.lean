-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Galois
-- name    : GroundTheory_GlobalFields_CompletionAtPlace_Galois
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:46:06.73485+00:00
-- url     : https://prove2.me/theorems/13b0f3bc-e4a4-47a6-b569-fc989d7899c6
-- title:
--   Galois
-- statement:
--   Definitions and structural lemmas for Galois, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Galois.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Degree
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk


set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero Pointwise
namespace GroundTheory.Global
theorem eq_of_forall_le_exp_neg_iff {a b : ℤᵐ⁰} (ha : a ≤ 1) (hb : b ≤ 1)
    (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) : a = b := by
  have key : ∀ a b : ℤᵐ⁰, b ≤ 1 →
      (∀ n : ℕ, b ≤ WithZero.exp (-(n : ℤ)) → a ≤ WithZero.exp (-(n : ℤ))) → a ≤ b := by
    intro a b hb h
    by_cases hb0 : b = 0
    · by_contra hab
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact hab zero_le
      obtain ⟨n, hn⟩ := WithZero.exists_exp_neg_natCast_lt ha0
      exact absurd (h n (by rw [hb0]; exact zero_le)) (not_le.2 hn)
    · have hlog : WithZero.log b ≤ 0 := by
        rw [WithZero.log_le_iff_le_exp hb0, WithZero.exp_zero]
        exact hb
      have hn : (((-(WithZero.log b)).toNat : ℕ) : ℤ) = -WithZero.log b :=
        Int.toNat_of_nonneg (by omega)
      have hb' : WithZero.exp (-(((-(WithZero.log b)).toNat : ℕ) : ℤ)) = b := by
        rw [hn, neg_neg, WithZero.exp_log hb0]
      calc a ≤ _ := h _ hb'.ge
        _ = b := hb'
  exact le_antisymm (key a b hb fun n hn ↦ (h n).2 hn) (key b a ha fun n hn ↦ (h n).1 hn)
theorem uniformContinuous_of_valued_eq {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued R Γ₀] (f : R →+* R) (hf : ∀ x, Valued.v (f x) = Valued.v x) : UniformContinuous f := by
  refine uniformContinuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  refine Valued.mem_nhds_zero.2 ⟨γ, fun x hx ↦ Set.mem_preimage.2 (hγ ?_)⟩
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
  rwa [hf]
section Stabilizer
variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]
  (w : HeightOneSpectrum (𝓞 L))
theorem smul_mem_asIdeal_pow_iff {σ : L ≃ₐ[K] L} (hσ : σ • w.asIdeal = w.asIdeal) (r : 𝓞 L)
    (n : ℕ) : σ • r ∈ w.asIdeal ^ n ↔ r ∈ w.asIdeal ^ n := by
  have h : σ • (w.asIdeal ^ n) = w.asIdeal ^ n := by
    rw [Ideal.pointwise_smul_def, Ideal.map_pow, ← Ideal.pointwise_smul_def, hσ]
  conv_lhs => rw [← h]
  exact Ideal.smul_mem_pointwise_smul_iff
theorem intValuation_smul {σ : L ≃ₐ[K] L} (hσ : σ • w.asIdeal = w.asIdeal) (r : 𝓞 L) :
    w.intValuation (σ • r) = w.intValuation r :=
  eq_of_forall_le_exp_neg_iff (w.intValuation_le_one _) (w.intValuation_le_one _) fun n ↦ by
    rw [intValuation_le_pow_iff_mem, intValuation_le_pow_iff_mem, smul_mem_asIdeal_pow_iff w hσ]
theorem valuation_algEquiv_apply_of_smul_eq {σ : L ≃ₐ[K] L} (hσ : σ • w.asIdeal = w.asIdeal)
    (x : L) : w.valuation L (σ x) = w.valuation L x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
  have hs : ∀ c : 𝓞 L, σ (algebraMap (𝓞 L) L c) = algebraMap (𝓞 L) L (σ • c) := fun c ↦ rfl
  rw [map_div₀, map_div₀, map_div₀, hs, hs, valuation_of_algebraMap, valuation_of_algebraMap,
    valuation_of_algebraMap, valuation_of_algebraMap, intValuation_smul w hσ,
    intValuation_smul w hσ]
end Stabilizer
section CompletionMap
variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]
  (w : HeightOneSpectrum (𝓞 L))
def adicCompletionRingHomOf (σ : L ≃ₐ[K] L) (hσ : σ • w.asIdeal = w.asIdeal) :
    w.adicCompletion L →+* w.adicCompletion L :=
  (adicCompletion.equiv L w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom
        (WithVal.map (w.valuation L) (w.valuation L) (σ : L →+* L))
        (uniformContinuous_of_valued_eq _
          fun x ↦ valuation_algEquiv_apply_of_smul_eq w hσ (WithVal.equiv _ x)).continuous).comp
      (adicCompletion.equiv L w).toRingHom)
variable {w}
theorem continuous_adicCompletionRingHomOf (σ : L ≃ₐ[K] L) (hσ : σ • w.asIdeal = w.asIdeal) :
    Continuous (adicCompletionRingHomOf w σ hσ) :=
  (adicCompletion.continuous_ofCompletion L w).comp <|
    UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion L w)
theorem adicCompletionRingHomOf_algebraMap (σ : L ≃ₐ[K] L) (hσ : σ • w.asIdeal = w.asIdeal)
    (x : L) : adicCompletionRingHomOf w σ hσ (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w.adicCompletion L) (σ x) := by
  apply adicCompletion.ext
  change UniformSpace.Completion.mapRingHom _
    (uniformContinuous_of_valued_eq _
      fun x ↦ valuation_algEquiv_apply_of_smul_eq w hσ (WithVal.equiv _ x)).continuous
    ((algebraMap L (WithVal (w.valuation L)) x : WithVal (w.valuation L)) :
      UniformSpace.Completion (WithVal (w.valuation L))) = _
  rw [UniformSpace.Completion.mapRingHom_coe]
  rfl
variable (w) in

theorem ringHom_ext_adicCompletion {f g : w.adicCompletion L →+* w.adicCompletion L}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x : L, f (algebraMap L _ x) = g (algebraMap L _ x)) : f = g :=
  RingHom.ext (congrFun ((denseRange_algebraMap (R := 𝓞 L) (K := L) w).equalizer hf hg
    (funext h)))
end CompletionMap
section Decomposition
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]
omit [w.asIdeal.LiesOver v.asIdeal] in

theorem adicCompletionRingHomOf_algebraMap_adicCompletion (σ : L ≃ₐ[K] L)
    (hσ : σ • w.asIdeal = w.asIdeal) (c : v.adicCompletion K) :
    adicCompletionRingHomOf w σ hσ (algebraMap (v.adicCompletion K) (w.adicCompletion L) c) =
      algebraMap (v.adicCompletion K) (w.adicCompletion L) c := by
  have h := (denseRange_algebraMap (R := 𝓞 K) (K := K) v).equalizer
    ((continuous_adicCompletionRingHomOf σ hσ).comp
      (continuous_algebraMap (v.adicCompletion K) (w.adicCompletion L)))
    (continuous_algebraMap (v.adicCompletion K) (w.adicCompletion L)) (funext fun k ↦ ?_)
  · exact congrFun h c
  · simp only [Function.comp_apply]
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K L (w.adicCompletion L),
      adicCompletionRingHomOf_algebraMap, AlgEquiv.commutes]
omit [NumberField K] in

theorem smul_asIdeal_of_mem_stabilizer (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) :
    (σ : Gal(L/K)) • w.asIdeal = w.asIdeal :=
  MulAction.mem_stabilizer_iff.1 σ.2
def decompositionAlgEquiv (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) :
    w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom (adicCompletionRingHomOf w σ.1 (smul_asIdeal_of_mem_stabilizer w σ))
    (adicCompletionRingHomOf w (σ⁻¹).1 (smul_asIdeal_of_mem_stabilizer w σ⁻¹))
    (ringHom_ext_adicCompletion w
      ((continuous_adicCompletionRingHomOf σ.1 (smul_asIdeal_of_mem_stabilizer w σ)).comp
      (continuous_adicCompletionRingHomOf (σ⁻¹).1 (smul_asIdeal_of_mem_stabilizer w σ⁻¹)))
      continuous_id fun x ↦ by
        rw [RingHom.comp_apply, adicCompletionRingHomOf_algebraMap,
          adicCompletionRingHomOf_algebraMap]
        simp)
    (ringHom_ext_adicCompletion w
      ((continuous_adicCompletionRingHomOf (σ⁻¹).1 (smul_asIdeal_of_mem_stabilizer w σ⁻¹)).comp
      (continuous_adicCompletionRingHomOf σ.1 (smul_asIdeal_of_mem_stabilizer w σ)))
      continuous_id fun x ↦ by
        rw [RingHom.comp_apply, adicCompletionRingHomOf_algebraMap,
          adicCompletionRingHomOf_algebraMap]
        simp))
    (adicCompletionRingHomOf_algebraMap_adicCompletion v w σ.1 (smul_asIdeal_of_mem_stabilizer w σ))
omit [w.asIdeal.LiesOver v.asIdeal] in
@[simp]
theorem decompositionAlgEquiv_algebraMap (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) (x : L) :
    decompositionAlgEquiv v w σ (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w.adicCompletion L) ((σ : Gal(L/K)) x) :=
  adicCompletionRingHomOf_algebraMap σ.1 (smul_asIdeal_of_mem_stabilizer w σ) x
omit [w.asIdeal.LiesOver v.asIdeal] in
theorem continuous_decompositionAlgEquiv (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) :
    Continuous (decompositionAlgEquiv v w σ) :=
  continuous_adicCompletionRingHomOf σ.1 (smul_asIdeal_of_mem_stabilizer w σ)
omit [w.asIdeal.LiesOver v.asIdeal] in

theorem algEquiv_ext_adicCompletion {f g : w.adicCompletion L ≃ₐ[v.adicCompletion K]
    w.adicCompletion L} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x : L, f (algebraMap L _ x) = g (algebraMap L _ x)) : f = g :=
  AlgEquiv.ext fun y ↦ congrFun (congrArg DFunLike.coe
    (ringHom_ext_adicCompletion w (f := (f : w.adicCompletion L →+* w.adicCompletion L))
      (g := (g : w.adicCompletion L →+* w.adicCompletion L)) hf hg h)) y
def decompositionToLocal :
    MulAction.stabilizer Gal(L/K) w.asIdeal →* Gal(w.adicCompletion L/v.adicCompletion K) where
  toFun := decompositionAlgEquiv v w
  map_one' := algEquiv_ext_adicCompletion v w (continuous_decompositionAlgEquiv v w 1)
    continuous_id fun x ↦ by simp
  map_mul' σ τ := algEquiv_ext_adicCompletion v w (continuous_decompositionAlgEquiv v w _)
    ((continuous_decompositionAlgEquiv v w σ).comp (continuous_decompositionAlgEquiv v w τ))
    fun x ↦ by simp
omit [w.asIdeal.LiesOver v.asIdeal] in
@[simp]
theorem decompositionToLocal_algebraMap (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) (x : L) :
    decompositionToLocal v w σ (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w.adicCompletion L) ((σ : Gal(L/K)) x) :=
  decompositionAlgEquiv_algebraMap v w σ x
omit [w.asIdeal.LiesOver v.asIdeal] in

theorem decompositionToLocal_injective : Function.Injective (decompositionToLocal v w) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  have := congrArg (fun f : Gal(w.adicCompletion L/v.adicCompletion K) ↦
    f (algebraMap L (w.adicCompletion L) x)) hσ
  simp only [decompositionToLocal_algebraMap, AlgEquiv.one_apply] at this
  exact (algebraMap L (w.adicCompletion L)).injective this
end Decomposition
section Galois
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]
omit [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)] in
include v in

theorem card_decompositionGroup :
    Nat.card (MulAction.stabilizer Gal(L/K) w.asIdeal) =
      w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) := by
  rw [Ideal.card_stabilizer_eq v.asIdeal w.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal Gal(L/K),
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.asIdeal Gal(L/K)]
theorem decompositionToLocal_bijective : Function.Bijective (decompositionToLocal v w) := by
  refine (decompositionToLocal_injective v w).bijective_of_nat_card_le ?_
  rw [card_decompositionGroup v w, ← finrank_adicCompletion v w, Nat.card_eq_fintype_card]
  exact AlgEquiv.card_le
def decompositionMulEquiv :
    MulAction.stabilizer Gal(L/K) w.asIdeal ≃* Gal(w.adicCompletion L/v.adicCompletion K) :=
  MulEquiv.ofBijective (decompositionToLocal v w) (decompositionToLocal_bijective v w)
instance isGalois_adicCompletion : IsGalois (v.adicCompletion K) (w.adicCompletion L) :=
  IsGalois.of_card_aut_eq_finrank _ _ (by
    rw [← Nat.card_congr (decompositionMulEquiv v w).toEquiv, card_decompositionGroup v w,
      finrank_adicCompletion v w])
end Galois
end GroundTheory.Global


