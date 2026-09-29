-- Prove2me | solution 1 for AutomorphicForm.TwistedBruhat.exists_isCompact_forall_mem_of_mem_smul_normOneUnits_of_congr_mul_inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/9900ccb0-4c2f-53de-b7a8-5ce74d20033b

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_NumberField_PlaceTransport
import Theorems.Thm_TwistedUnipotentTerm_isCompact_isOpen_integralUnits_and_mem_iff_forall_valued_eq_one
import Theorems.Thm_HeightOneSpectrum_adicCompletion_baseChangeAlgEquiv_congr_apply_eq_transport
import Theorems.Thm_NumberField_PlaceTransport_exists_pow_smul_eq_of_forall_mem_zpowers
import Theorems.Thm_Algebra_TensorProduct_algebraMap_norm_eq_prod_congr_apply_of_isGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_mem_of_mem_smul_normOneUnits_of_congr_mul_inv_mem

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm.AdelicTracePushforward
open scoped ENNReal

namespace LocFinAux

open scoped NumberField.PlaceTransport

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

theorem smul_algebraMap (σ : L ≃ₐ[K] L) (a : 𝓞 K) :
    σ • (algebraMap (𝓞 K) (𝓞 L) a) = algebraMap (𝓞 K) (𝓞 L) a := by
  apply Subtype.ext
  show σ (algebraMap (𝓞 K) (𝓞 L) a : L) = _
  exact σ.commutes (a : K)

theorem under_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    HeightOneSpectrum.under (𝓞 K) (σ • w) = HeightOneSpectrum.under (𝓞 K) w := by
  apply HeightOneSpectrum.ext
  ext a
  rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.under_def,
    Ideal.mem_comap, Ideal.mem_comap, NumberField.PlaceTransport.mem_smul_asIdeal_iff, smul_algebraMap]

noncomputable def smulExt (σ : L ≃ₐ[K] L) (w : v.Extension (𝓞 L)) : v.Extension (𝓞 L) :=
  ⟨σ • w.1, by rw [under_smul K L σ w.1]; exact w.2⟩

theorem smulExt_val (σ : L ≃ₐ[K] L) (w : v.Extension (𝓞 L)) : (smulExt K L v σ w).1 = σ • w.1 := rfl

theorem smulExt_mul (σ τ : L ≃ₐ[K] L) (w : v.Extension (𝓞 L)) :
    smulExt K L v (σ * τ) w = smulExt K L v σ (smulExt K L v τ w) :=
  Subtype.ext (mul_smul σ τ w.1)

theorem smulExt_one (w : v.Extension (𝓞 L)) : smulExt K L v 1 w = w := Subtype.ext (one_smul _ w.1)

theorem iterate_smulExt (σ : L ≃ₐ[K] L) (n : ℕ) (w : v.Extension (𝓞 L)) :
    (smulExt K L v σ)^[n] w = smulExt K L v (σ ^ n) w := by
  induction n with
  | zero => rw [Function.iterate_zero, pow_zero, smulExt_one]; rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, ← smulExt_mul, ← pow_succ']

noncomputable def A (w : v.Extension (𝓞 L)) (z : (L ⊗[K] v.adicCompletion K)ˣ) : ℤ :=
  WithZero.log (Valued.v ((TwistedUnipotentTerm.semiLocalUnitComponent K L v w z : (w.1.adicCompletion L)ˣ) :
    w.1.adicCompletion L))

theorem v_ne_zero (w : v.Extension (𝓞 L)) (z : (L ⊗[K] v.adicCompletion K)ˣ) :
    Valued.v ((TwistedUnipotentTerm.semiLocalUnitComponent K L v w z : (w.1.adicCompletion L)ˣ) :
      w.1.adicCompletion L) ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr (Units.ne_zero _)

theorem comp_mul (w : v.Extension (𝓞 L)) (a b : (L ⊗[K] v.adicCompletion K)ˣ) :
    TwistedUnipotentTerm.semiLocalUnitComponent K L v w (a * b) =
      TwistedUnipotentTerm.semiLocalUnitComponent K L v w a * TwistedUnipotentTerm.semiLocalUnitComponent K L v w b := by
  simp only [TwistedUnipotentTerm.semiLocalUnitComponent, map_mul]

theorem comp_inv (w : v.Extension (𝓞 L)) (a : (L ⊗[K] v.adicCompletion K)ˣ) :
    TwistedUnipotentTerm.semiLocalUnitComponent K L v w a⁻¹ = (TwistedUnipotentTerm.semiLocalUnitComponent K L v w a)⁻¹ := by
  simp only [TwistedUnipotentTerm.semiLocalUnitComponent, map_inv]

theorem A_mul (w : v.Extension (𝓞 L)) (a b : (L ⊗[K] v.adicCompletion K)ˣ) :
    A K L v w (a * b) = A K L v w a + A K L v w b := by
  simp only [A, comp_mul, Units.val_mul, map_mul]
  exact WithZero.log_mul (v_ne_zero K L v w a) (v_ne_zero K L v w b)

theorem A_inv (w : v.Extension (𝓞 L)) (a : (L ⊗[K] v.adicCompletion K)ˣ) :
    A K L v w a⁻¹ = -A K L v w a := by
  simp only [A, comp_inv, Units.val_inv_eq_inv_val, map_inv₀]
  exact WithZero.log_inv _

theorem A_one (w : v.Extension (𝓞 L)) : A K L v w 1 = 0 := by
  simp only [A, TwistedUnipotentTerm.semiLocalUnitComponent, map_one, Units.val_one, WithZero.log_one]

theorem mem_integralUnits_iff (z : (L ⊗[K] v.adicCompletion K)ˣ) :
    z ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v ↔ ∀ w, A K L v w z = 0 := by
  rw [(TwistedUnipotentTerm.isCompact_isOpen_integralUnits_and_mem_iff_forall_valued_eq_one K L v).2.2]
  refine forall_congr' fun w => ?_
  constructor
  · intro h; simp only [A, h, WithZero.log_one]
  · intro h
    have := WithZero.exp_log (v_ne_zero K L v w z)
    rw [show WithZero.log _ = (0 : ℤ) from h, WithZero.exp_zero] at this
    exact this.symm

theorem coe_comp (w : v.Extension (𝓞 L)) (z : (L ⊗[K] v.adicCompletion K)ˣ) :
    ((TwistedUnipotentTerm.semiLocalUnitComponent K L v w z : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L) =
      HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v (z : L ⊗[K] v.adicCompletion K) w := by
  simp only [TwistedUnipotentTerm.semiLocalUnitComponent, Units.coe_map, MonoidHom.coe_coe, Pi.evalMonoidHom_apply,
    Units.coe_mapEquiv, RingEquiv.toMulEquiv_eq_coe, RingEquiv.coe_toMulEquiv, AlgEquiv.coe_ringEquiv]

noncomputable def σU (τ : L ≃ₐ[K] L) : (L ⊗[K] v.adicCompletion K)ˣ ≃* (L ⊗[K] v.adicCompletion K)ˣ :=
  Units.mapEquiv (Algebra.TensorProduct.congr τ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toMulEquiv

theorem coe_σU (τ : L ≃ₐ[K] L) (z : (L ⊗[K] v.adicCompletion K)ˣ) :
    ((σU K L v τ z : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) =
      Algebra.TensorProduct.congr τ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K) z := rfl

theorem A_σU (τ : L ≃ₐ[K] L) (w : v.Extension (𝓞 L)) (z : (L ⊗[K] v.adicCompletion K)ˣ) :
    A K L v (smulExt K L v τ w) (σU K L v τ z) = A K L v w z := by
  simp only [A, coe_comp, coe_σU]
  rw [HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv_congr_apply_eq_transport K L v τ w (smulExt K L v τ w) rfl,
    NumberField.PlaceTransport.valued_transport]

theorem exp_A (w : v.Extension (𝓞 L)) (z : (L ⊗[K] v.adicCompletion K)ˣ) :
    Valued.v ((TwistedUnipotentTerm.semiLocalUnitComponent K L v w z : (w.1.adicCompletion L)ˣ) :
      w.1.adicCompletion L) = WithZero.exp (A K L v w z) := by
  rw [A, WithZero.exp_log (v_ne_zero K L v w z)]

open scoped TensorProduct.RightActions in

theorem baseChangeAlgEquiv_algebraMap (w : v.Extension (𝓞 L)) (c : v.adicCompletion K) :
    HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
        (algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) c) w =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) c := by
  rw [TensorProduct.RightActions.algebraMap_eval, HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv,
    AlgEquiv.ofBijective_apply, HeightOneSpectrum.adicCompletion.baseChange_tmul_apply, map_one, one_mul]

theorem prod_exp {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, WithZero.exp (f i) = WithZero.exp (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ← WithZero.exp_add]

end LocFinAux

open LocFinAux in
open scoped NumberField.PlaceTransport in
open scoped TensorProduct.RightActions in
attribute [local instance] AutomorphicForm.TransversalMeasure.semiLocalUnitsBorel
  AutomorphicForm.TransversalMeasure.archUnitsBorel in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) (π : (L ⊗[K] v.adicCompletion K)ˣ)
    (C : Set (L ⊗[K] v.adicCompletion K)ˣ) (hC : IsCompact C) :
    ∃ B : Set (L ⊗[K] v.adicCompletion K)ˣ, IsCompact B ∧
      ∀ x : (L ⊗[K] v.adicCompletion K)ˣ,
        π⁻¹ * x ∈ AutomorphicForm.TransversalMeasure.normOneUnits K L v →
        Units.mapEquiv (Algebra.TensorProduct.congr σ
            (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toMulEquiv x * x⁻¹ ∈ C →
        x ∈ B := by
  classical
  letI : Fintype (v.Extension (𝓞 L)) := HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  obtain ⟨hUc, hUo, -⟩ := TwistedUnipotentTerm.isCompact_isOpen_integralUnits_and_mem_iff_forall_valued_eq_one K L v
  set U : Set (L ⊗[K] v.adicCompletion K)ˣ :=
    ((AutomorphicForm.TransversalMeasure.integralUnits K L v : Subgroup (L ⊗[K] v.adicCompletion K)ˣ) :
      Set (L ⊗[K] v.adicCompletion K)ˣ) with hUdef

  have hcov : C ⊆ ⋃ c ∈ C, (fun u => c * u) '' U := by
    intro c hc
    exact Set.mem_biUnion hc ⟨1, (AutomorphicForm.TransversalMeasure.integralUnits K L v).one_mem, mul_one c⟩
  have hopen : ∀ c : (L ⊗[K] v.adicCompletion K)ˣ, IsOpen ((fun u => c * u) '' U) :=
    fun c => (Homeomorph.mulLeft c).isOpenMap U hUo
  obtain ⟨t, htC, htfin, htcov⟩ := hC.elim_finite_subcover_image (fun c _ => hopen c) hcov

  obtain ⟨D, hD⟩ : ∃ D : ℤ, ∀ r ∈ C, ∀ w, |A K L v w r| ≤ D := by
    have hfin : (Set.image2 (fun (c : (L ⊗[K] v.adicCompletion K)ˣ) (w : v.Extension (𝓞 L)) => |A K L v w c|)
        t Set.univ).Finite := htfin.image2 _ Set.finite_univ
    obtain ⟨D, hD⟩ := hfin.bddAbove
    refine ⟨D, fun r hr w => ?_⟩
    obtain ⟨c, hct, hrc⟩ := Set.mem_iUnion₂.1 (htcov hr)
    obtain ⟨u, hu, rfl⟩ := hrc
    have hu0 : A K L v w u = 0 := (mem_integralUnits_iff K L v u).1 hu w
    rw [A_mul, hu0, add_zero]
    exact hD (Set.mem_image2_of_mem hct (Set.mem_univ w))

  set Nπ : v.adicCompletion K := Algebra.norm (v.adicCompletion K) ((π : (L ⊗[K] v.adicCompletion K)ˣ) :
    L ⊗[K] v.adicCompletion K) with hNπ
  set P : v.Extension (𝓞 L) → ℤ := fun w =>
    WithZero.log (Valued.v (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) Nπ)) with hP
  set m : ℕ := orderOf σ with hm
  set g : ℕ := Fintype.card (L ≃ₐ[K] L) with hg
  set R : ℤ := (∑ w : v.Extension (𝓞 L), |P w|) + (g : ℤ) * ((m : ℤ) * |D|) with hR

  refine ⟨{z | ∀ w, |A K L v w z| ≤ R}, ?_, ?_⟩
  ·
    set Q : Finset (v.Extension (𝓞 L) → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-R) R with hQ
    have hpiece : ∀ q : v.Extension (𝓞 L) → ℤ, IsCompact {z : (L ⊗[K] v.adicCompletion K)ˣ | ∀ w, A K L v w z = q w} := by
      intro q
      rcases Set.eq_empty_or_nonempty {z : (L ⊗[K] v.adicCompletion K)ˣ | ∀ w, A K L v w z = q w} with h | ⟨z₀, hz₀⟩
      · rw [h]; exact isCompact_empty
      · have heq : {z : (L ⊗[K] v.adicCompletion K)ˣ | ∀ w, A K L v w z = q w} = (fun u => z₀ * u) '' U := by
          ext z
          simp only [Set.mem_setOf_eq, Set.mem_image]
          constructor
          · intro hz
            refine ⟨z₀⁻¹ * z, (mem_integralUnits_iff K L v _).2 fun w => ?_, by group⟩
            rw [A_mul, A_inv, hz w, hz₀ w]; ring
          · rintro ⟨u, hu, rfl⟩ w
            rw [A_mul, hz₀ w, (mem_integralUnits_iff K L v u).1 hu w, add_zero]
        rw [heq]
        exact hUc.image (continuous_const.mul continuous_id)
    have hcover : {z : (L ⊗[K] v.adicCompletion K)ˣ | ∀ w, |A K L v w z| ≤ R} =
        ⋃ q ∈ Q, {z | ∀ w, A K L v w z = q w} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop, hQ, Fintype.mem_piFinset, Finset.mem_Icc]
      constructor
      · intro hz
        exact ⟨fun w => A K L v w z, fun w => abs_le.1 (hz w), fun w => rfl⟩
      · rintro ⟨q, hq, hzq⟩ w
        rw [hzq w]
        exact abs_le.2 (hq w)
    rw [hcover]
    exact Q.isCompact_biUnion fun q _ => hpiece q
  ·
    intro x hshell hC'

    have hstep : ∀ w, |A K L v (smulExt K L v σ w) x - A K L v w x| ≤ |D| := by
      intro w
      have h1 := hD _ hC' (smulExt K L v σ w)
      rw [A_mul, A_inv] at h1
      have hb : A K L v (smulExt K L v σ w) (σU K L v σ x) = A K L v w x := A_σU K L v σ w x
      have : A K L v (smulExt K L v σ w) (Units.mapEquiv (Algebra.TensorProduct.congr σ
          (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toMulEquiv x) = A K L v w x := hb
      rw [this] at h1
      rw [abs_sub_comm]
      have : A K L v w x - A K L v (smulExt K L v σ w) x = A K L v w x + -A K L v (smulExt K L v σ w) x := by ring
      rw [this]
      exact h1.trans (le_abs_self D)
    have hiter : ∀ (n : ℕ) (w), |A K L v ((smulExt K L v σ)^[n] w) x - A K L v w x| ≤ n * |D| := by
      intro n
      induction n with
      | zero => intro w; simp
      | succ n ih =>
        intro w
        rw [Function.iterate_succ_apply']
        calc |A K L v (smulExt K L v σ ((smulExt K L v σ)^[n] w)) x - A K L v w x|
            ≤ |A K L v (smulExt K L v σ ((smulExt K L v σ)^[n] w)) x - A K L v ((smulExt K L v σ)^[n] w) x|
              + |A K L v ((smulExt K L v σ)^[n] w) x - A K L v w x| := abs_sub_le _ _ _
          _ ≤ |D| + n * |D| := add_le_add (hstep _) (ih w)
          _ = (n + 1 : ℕ) * |D| := by push_cast; ring
    have hm0 : 0 < m := orderOf_pos σ
    have hband : ∀ w w', |A K L v w x - A K L v w' x| ≤ m * |D| := by
      intro w w'
      obtain ⟨n, hn⟩ := NumberField.PlaceTransport.exists_pow_smul_eq_of_forall_mem_zpowers K L σ hgen v w' w
      have hw : (smulExt K L v σ)^[n % m] w' = w := by
        rw [iterate_smulExt]
        apply Subtype.ext
        rw [smulExt_val, ← hn, hm, pow_mod_orderOf]
      have h := hiter (n % m) w'
      rw [hw] at h
      refine h.trans ?_
      have : ((n % m : ℕ) : ℤ) ≤ m := by exact_mod_cast (Nat.mod_lt n hm0).le
      exact mul_le_mul_of_nonneg_right this (abs_nonneg D)

    have hsum : ∀ w, ∑ τ : L ≃ₐ[K] L, A K L v (smulExt K L v τ w) x = P w := by
      intro w
      set y : L ⊗[K] v.adicCompletion K := ((x : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) with hy

      set u : v.adicCompletion K := Algebra.norm (v.adicCompletion K)
        (((π⁻¹ * x : (L ⊗[K] v.adicCompletion K)ˣ)) : L ⊗[K] v.adicCompletion K) with hu
      have hN : Algebra.norm (v.adicCompletion K) y = Nπ * u := by
        rw [hNπ, hu, hy, ← map_mul, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
      have hvu : Valued.v u = 1 := by
        have := hshell
        rw [AutomorphicForm.TransversalMeasure.normOneUnits, MonoidHom.mem_ker] at this
        exact this
      have hNπ0 : Nπ ≠ 0 := by
        rw [hNπ]
        exact ((Units.isUnit π).map (Algebra.norm (v.adicCompletion K))).ne_zero

      have hNG := Algebra.TensorProduct.algebraMap_norm_eq_prod_congr_apply_of_isGalois K L (v.adicCompletion K) y
      have hL : WithZero.log (Valued.v (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
          (algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) (Algebra.norm (v.adicCompletion K) y)) w))
          = P w := by
        rw [baseChangeAlgEquiv_algebraMap, hN, map_mul, map_mul,
          WithZero.log_mul ?_ ?_]
        · have h1 : Valued.v (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) u) = 1 := by
            have := w.valued_adicCompletionSemialgHom K L u
            rw [hvu, one_pow] at this
            exact this
          rw [h1, WithZero.log_one, add_zero]
        · rw [Valuation.ne_zero_iff, map_ne_zero]
          exact hNπ0
        · have := w.valued_adicCompletionSemialgHom K L u
          rw [hvu, one_pow] at this
          rw [show Valued.v (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) u) = 1 from this]
          exact one_ne_zero
      have hRt : WithZero.log (Valued.v (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
          (∏ τ : L ≃ₐ[K] L, Algebra.TensorProduct.congr τ
            (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K) y) w))
          = ∑ τ : L ≃ₐ[K] L, A K L v w (σU K L v τ x) := by
        rw [map_prod, Finset.prod_apply, map_prod]
        have : ∀ τ : L ≃ₐ[K] L, Valued.v (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
            (Algebra.TensorProduct.congr τ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K) y) w)
            = WithZero.exp (A K L v w (σU K L v τ x)) := by
          intro τ
          rw [← exp_A, coe_comp, coe_σU]
        simp only [this, prod_exp, WithZero.log_exp]
      have hmain : ∑ τ : L ≃ₐ[K] L, A K L v w (σU K L v τ x) = P w := by
        rw [← hRt, ← hNG, hL]

      have hre : ∀ τ : L ≃ₐ[K] L, A K L v w (σU K L v τ x) = A K L v (smulExt K L v τ⁻¹ w) x := by
        intro τ
        have h := A_σU K L v τ (smulExt K L v τ⁻¹ w) x
        rw [← smulExt_mul, mul_inv_cancel, smulExt_one] at h
        exact h
      rw [← hmain]
      simp only [hre]
      exact (Fintype.sum_equiv (Equiv.inv (L ≃ₐ[K] L)) _ _ fun τ => by simp).symm

    intro w
    have hg1 : (1 : ℤ) ≤ g := by
      rw [hg]; exact_mod_cast Fintype.card_pos
    have hdiff : |(g : ℤ) * A K L v w x - P w| ≤ g * (m * |D|) := by
      rw [← hsum w]
      have : (g : ℤ) * A K L v w x - ∑ τ : L ≃ₐ[K] L, A K L v (smulExt K L v τ w) x
          = ∑ τ : L ≃ₐ[K] L, (A K L v w x - A K L v (smulExt K L v τ w) x) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hg]
        simp
      rw [this]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ τ : L ≃ₐ[K] L, |A K L v w x - A K L v (smulExt K L v τ w) x|
          ≤ ∑ _τ : L ≃ₐ[K] L, (m : ℤ) * |D| := Finset.sum_le_sum fun τ _ => hband _ _
        _ = g * (m * |D|) := by rw [Finset.sum_const, Finset.card_univ, hg]; simp
    have hPle : |P w| ≤ ∑ w' : v.Extension (𝓞 L), |P w'| :=
      Finset.single_le_sum (f := fun w' => |P w'|) (fun w' _ => abs_nonneg _) (Finset.mem_univ w)
    have h1 : |A K L v w x| ≤ |(g : ℤ) * A K L v w x| := by
      rw [abs_mul]
      exact le_mul_of_one_le_left (abs_nonneg _) (by rw [abs_of_pos (by omega)]; exact hg1)
    have h2 : |(g : ℤ) * A K L v w x| ≤ |P w| + g * (m * |D|) := by
      have := abs_sub_abs_le_abs_sub ((g : ℤ) * A K L v w x) (P w)
      linarith
    rw [hR]
    linarith

end S_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_mem_of_mem_smul_normOneUnits_of_congr_mul_inv_mem
end P2MW
export P2MW.S_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_mem_of_mem_smul_normOneUnits_of_congr_mul_inv_mem (solution)
