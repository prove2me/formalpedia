-- Prove2me | solution 1 for AutomorphicForm.exists_pos_forall_mul_prod_le_ideleNorm_det_le_of_isSemiLocalFactorization_of_apply_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/2558b780-ca63-54b5-a51e-89506f8e2cb9

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_pos_forall_mul_prod_le_ideleNorm_det_le_of_isSemiLocalFactorization_of_apply_ne_zero
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm
open scoped TensorProduct NNReal
open scoped TensorProduct.RightActions

noncomputable section

namespace R1SuppDet

section Local

variable (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

theorem valued_algebraMap_uniformiser {ϖ : u.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    Valued.v (algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) ϖ) = WithZero.exp (-1 : ℤ) := by
  change Valued.v (ϖ : u.adicCompletion F) = WithZero.exp (-1 : ℤ)
  obtain ⟨p, hp⟩ := HeightOneSpectrum.intValuation_exists_uniformizer u
  have hpv : Valued.v ((p : 𝓞 F) : u.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap, hp]
  set p' : u.adicCompletionIntegers F := algebraMap (𝓞 F) (u.adicCompletionIntegers F) p with hp'
  have hp'v : Valued.v (p' : u.adicCompletion F) = WithZero.exp (-1 : ℤ) := hpv
  have hp'max : p' ∈ IsLocalRing.maximalIdeal (u.adicCompletionIntegers F) := by
    rw [NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one (𝓞 F) F u, hp'v, ← WithZero.exp_zero,
      WithZero.exp_lt_exp]
    norm_num
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hp'max
  obtain ⟨a, ha⟩ := hp'max
  have hle : WithZero.exp (-1 : ℤ) ≤ Valued.v (ϖ : u.adicCompletion F) := by
    rw [← hp'v, ← ha]
    push_cast
    rw [map_mul]
    calc Valued.v (a : u.adicCompletion F) * Valued.v (ϖ : u.adicCompletion F)
        ≤ 1 * Valued.v (ϖ : u.adicCompletion F) := mul_le_mul_of_nonneg_right a.2 zero_le'
      _ = Valued.v (ϖ : u.adicCompletion F) := one_mul _
  have hlt : Valued.v (ϖ : u.adicCompletion F) < 1 := by
    refine lt_of_le_of_ne ϖ.2 fun h => hϖ.not_isUnit ?_
    exact HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 h
  have hne : Valued.v (ϖ : u.adicCompletion F) ≠ 0 := by
    refine (Valuation.ne_zero_iff _).2 fun h => hϖ.ne_zero ?_
    exact_mod_cast h
  refine le_antisymm ?_ hle
  rw [← WithZero.log_le_iff_le_exp hne]
  have h0 : WithZero.log (Valued.v (ϖ : u.adicCompletion F)) < 0 := by
    rw [WithZero.log_lt_iff_lt_exp hne, WithZero.exp_zero]; exact hlt
  omega

theorem norm_eq_of_valued_eq_exp (x : u.adicCompletion F) (n : ℤ) (hx : Valued.v x = WithZero.exp n) :
    ‖x‖ = ((Ideal.absNorm u.asIdeal : ℝ≥0) : ℝ) ^ n := by
  rw [FinitePlace.norm_def, hx]
  have hne : (WithZero.exp n : WithZero (Multiplicative ℤ)) ≠ 0 := WithZero.exp_ne_zero
  rw [WithZeroMulInt.toNNReal_neg_apply _ hne]
  push_cast
  rfl

theorem norm_uniformiser {ϖ : u.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    ‖algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) ϖ‖ = ((Ideal.absNorm u.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [norm_eq_of_valued_eq_exp F u _ (-1) (valued_algebraMap_uniformiser F u hϖ), zpow_neg, zpow_one]
  rfl

theorem norm_eq_one_of_valued_eq_one (x : u.adicCompletion F) (hx : Valued.v x = 1) : ‖x‖ = 1 := by
  rw [← WithZero.exp_zero] at hx
  rw [norm_eq_of_valued_eq_exp F u x 0 hx, zpow_zero]

theorem valued_coe_units_integer (a : (u.adicCompletionIntegers F)ˣ) :
    Valued.v ((a : u.adicCompletionIntegers F) : u.adicCompletion F) = 1 :=
  HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 a.isUnit

theorem norm_coe_units_integer (a : (u.adicCompletionIntegers F)ˣ) :
    ‖((a : u.adicCompletionIntegers F) : u.adicCompletion F)‖ = 1 :=
  norm_eq_one_of_valued_eq_one F u _ (valued_coe_units_integer F u a)

end Local

section HeckeDet

variable (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

theorem norm_det_eq_one_of_mem_integralSubgroup {g : GL (Fin 2) (u.adicCompletion F)}
    (hg : g ∈ LocalGL2.integralSubgroup (u.adicCompletionIntegers F) (u.adicCompletion F)) :
    ‖((Matrix.GeneralLinearGroup.det g : (u.adicCompletion F)ˣ) : u.adicCompletion F)‖ = 1 := by
  obtain ⟨g₀, rfl⟩ := hg
  rw [Matrix.GeneralLinearGroup.map_det, Units.coe_map]
  exact norm_coe_units_integer F u (Matrix.GeneralLinearGroup.det g₀)

theorem coe_det_diagPi (ϖ : u.adicCompletionIntegers F)
    (hϖ0 : algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) ϖ ≠ 0) :
    ((Matrix.GeneralLinearGroup.det (LocalGL2.diagPi ϖ hϖ0) : (u.adicCompletion F)ˣ) : u.adicCompletion F) =
      algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) ϖ := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, LocalGL2.coe_diagPi, Matrix.det_fin_two_of]
  ring

theorem norm_det_of_mem_doubleCoset {ϖ : u.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) ϖ ≠ 0)
    {r : GL (Fin 2) (u.adicCompletion F)}
    (hr : r ∈ HeckePair.doubleCoset
      (LocalGL2.integralSubgroup (u.adicCompletionIntegers F) (u.adicCompletion F)) (LocalGL2.diagPi ϖ hϖ0)) :
    ‖((Matrix.GeneralLinearGroup.det r : (u.adicCompletion F)ˣ) : u.adicCompletion F)‖ =
      ((Ideal.absNorm u.asIdeal : ℕ) : ℝ)⁻¹ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hr
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, norm_mul, norm_mul,
    norm_det_eq_one_of_mem_integralSubgroup F u ha, norm_det_eq_one_of_mem_integralSubgroup F u hb,
    coe_det_diagPi, norm_uniformiser F u hϖ, one_mul, mul_one]

theorem norm_det_of_coe_eq_smul_one {ϖ : u.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
    {z : GL (Fin 2) (u.adicCompletion F)}
    (hz : (z : Matrix (Fin 2) (Fin 2) (u.adicCompletion F)) =
      algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) ϖ • (1 : Matrix (Fin 2) (Fin 2) _)) :
    ‖((Matrix.GeneralLinearGroup.det z : (u.adicCompletion F)ˣ) : u.adicCompletion F)‖ =
      (((Ideal.absNorm u.asIdeal : ℕ) : ℝ)⁻¹) ^ 2 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  rw [show z.val = (z : Matrix (Fin 2) (Fin 2) (u.adicCompletion F)) from rfl, hz, Matrix.det_smul,
    Matrix.det_one, mul_one, Fintype.card_fin, norm_pow, norm_uniformiser F u hϖ]

theorem norm_det_heckeWord {ϖ : u.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) ϖ ≠ 0)
    {n : ℕ} (rT : Fin n → GL (Fin 2) (u.adicCompletion F))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (u.adicCompletionIntegers F) (u.adicCompletion F)) (LocalGL2.diagPi ϖ hϖ0) rT)
    {z : GL (Fin 2) (u.adicCompletion F)}
    (hz : (z : Matrix (Fin 2) (Fin 2) (u.adicCompletion F)) =
      algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) ϖ • (1 : Matrix (Fin 2) (Fin 2) _))
    (k j : ℕ) (ι : Fin k → Fin n) :
    ‖((Matrix.GeneralLinearGroup.det ((List.ofFn fun m => rT (ι m)).prod * z ^ j) : (u.adicCompletion F)ˣ) :
        u.adicCompletion F)‖ = (((Ideal.absNorm u.asIdeal : ℕ) : ℝ)⁻¹) ^ (k + 2 * j) := by
  have hdet : Matrix.GeneralLinearGroup.det ((List.ofFn fun m => rT (ι m)).prod * z ^ j) =
      (∏ m : Fin k, Matrix.GeneralLinearGroup.det (rT (ι m))) * Matrix.GeneralLinearGroup.det z ^ j := by
    rw [map_mul, map_pow, map_list_prod, List.map_ofFn, List.prod_ofFn]
    rfl
  rw [hdet, Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_prod, norm_mul, norm_pow, norm_prod,
    norm_det_of_coe_eq_smul_one F u hϖ hz]
  simp only [norm_det_of_mem_doubleCoset F u hϖ hϖ0 (hrT.mem_doubleCoset _), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, ← pow_add, mul_comm 2 j]

end HeckeDet

section Support

open AutomorphicForm

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem support_decomposition (S' : Finset (HeightOneSpectrum (𝓞 K)))
    {φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ} {φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ}
    {φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ}
    {φS' : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}
    (h : IsSemiLocalFactorization K L S' φ φa φf φS') (g : GL (Fin 2) (AdeleRing (𝓞 L) L)) (hg : φ g ≠ 0) :
    φa (glArch (𝓞 L) L g) ≠ 0 ∧
      (∀ v ∉ S', semiLocalComponent K L v (glFin (𝓞 L) L g) ∈ semiLocalIntegralSet K L v) ∧
      ∀ v ∈ S', φS' v (semiLocalComponent K L v (glFin (𝓞 L) L g)) ≠ 0 := by
  obtain ⟨-, -, -, hprod, hzero, hfac⟩ := h
  rw [hfac g] at hg
  have ha : φa (glArch (𝓞 L) L g) ≠ 0 := left_ne_zero_of_mul hg
  have hf : φf (glFin (𝓞 L) L g) ≠ 0 := right_ne_zero_of_mul hg
  have hint : ∀ v ∉ S', semiLocalComponent K L v (glFin (𝓞 L) L g) ∈ semiLocalIntegralSet K L v := by
    by_contra hcon
    push Not at hcon
    obtain ⟨v, hv, hnot⟩ := hcon
    exact hf (hzero _ ⟨v, hv, hnot⟩)
  refine ⟨ha, hint, fun v hv => ?_⟩
  rw [hprod _ hint] at hf
  exact (Finset.prod_ne_zero_iff.mp hf) v hv

theorem exists_inv_mul_mem_of_sum_indicator_ne_zero (v : HeightOneSpectrum (𝓞 K)) {κ : Type} [Fintype κ]
    (a : κ → GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (h : ∑ ι : κ, (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) ((a ι)⁻¹ * x) ≠ 0) :
    ∃ ι : κ, (a ι)⁻¹ * x ∈ semiLocalIntegralSet K L v := by
  obtain ⟨ι, -, hι⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨ι, Set.mem_of_indicator_ne_zero hι⟩

end Support

section Arch
variable (L : Type) [Field L] [NumberField L]

def archMod (x : GL (Fin 2) (InfiniteAdeleRing L)) : ℝ :=
  ∏ w : InfinitePlace L, ‖((Matrix.GeneralLinearGroup.det x : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L) w‖ ^ w.mult

theorem continuous_archMod : Continuous (archMod L) := by
  unfold archMod
  refine continuous_finsetProd _ fun w _ => ?_
  refine Continuous.pow ?_ _
  refine continuous_norm.comp ?_
  have h1 : Continuous fun x : GL (Fin 2) (InfiniteAdeleRing L) =>
      ((x : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L))).det :=
    Units.continuous_val.matrix_det
  have h2 : Continuous fun a : InfiniteAdeleRing L => a w := continuous_apply w
  convert h2.comp h1 using 1
  rfl

theorem archMod_pos (x : GL (Fin 2) (InfiniteAdeleRing L)) : 0 < archMod L x := by
  unfold archMod
  refine Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 ?_) _
  intro h0
  have h := congrArg (archEval L w)
    ((Matrix.GeneralLinearGroup.det x).mul_inv : ((Matrix.GeneralLinearGroup.det x : (InfiniteAdeleRing L)ˣ) :
      InfiniteAdeleRing L) * _ = 1)
  rw [map_mul, map_one, archEval_apply, archEval_apply, h0, zero_mul] at h
  exact zero_ne_one h

end Arch

section SemiLocalMod

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K))

scoped instance instFintypeExtension : Fintype (v.Extension (𝓞 L)) :=
  HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v

abbrev bc : L ⊗[K] v.adicCompletion K ≃ₐ[L] Π w : v.Extension (𝓞 L), w.1.adicCompletion L :=
  HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v

theorem semiLocalHomeomorph_apply (y : L ⊗[K] v.adicCompletion K) :
    semiLocalHomeomorph K L v y = bc K L v y := rfl

def slMod (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : ℝ :=
  ∏ w : v.Extension (𝓞 L),
    ‖bc K L v ((Matrix.GeneralLinearGroup.det x : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) w‖

theorem slMod_mul (x y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    slMod K L v (x * y) = slMod K L v x * slMod K L v y := by
  unfold slMod
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [map_mul, Units.val_mul, map_mul, Pi.mul_apply, norm_mul]

theorem slMod_one : slMod K L v 1 = 1 := by
  unfold slMod
  simp

theorem slMod_nonneg (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : 0 ≤ slMod K L v x :=
  Finset.prod_nonneg fun _ _ => norm_nonneg _

theorem slMod_inv_mul_self (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    slMod K L v x⁻¹ * slMod K L v x = 1 := by
  rw [← slMod_mul, inv_mul_cancel, slMod_one]

theorem slMod_pos (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : 0 < slMod K L v x := by
  rcases (slMod_nonneg K L v x).lt_or_eq with h | h
  · exact h
  · have := slMod_inv_mul_self K L v x
    rw [← h, mul_zero] at this
    exact absurd this zero_ne_one

theorem continuous_slMod : Continuous (slMod K L v) := by
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  unfold slMod
  refine continuous_finsetProd _ fun w _ => ?_
  refine continuous_norm.comp ?_
  have h1 : Continuous fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
      ((x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))).det :=
    Units.continuous_val.matrix_det
  have h2 : Continuous fun y : L ⊗[K] v.adicCompletion K => bc K L v y w :=
    (continuous_apply w).comp (semiLocalHomeomorph K L v).continuous
  exact h2.comp h1

theorem norm_le_one_of_mem_integers (w : HeightOneSpectrum (𝓞 L)) {x : w.adicCompletion L}
    (hx : x ∈ w.adicCompletionIntegers L) : ‖x‖ ≤ 1 := by
  rw [FinitePlace.norm_def]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx
  have := (WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal w)).2 hx
  exact_mod_cast this

theorem det_mem_semiLocalIntegers {M : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hM : ∀ i j, M i j ∈ semiLocalIntegers K L v) : M.det ∈ semiLocalIntegers K L v := by
  rw [Matrix.det_fin_two]
  obtain ⟨a, ha⟩ := hM 0 0
  obtain ⟨b, hb⟩ := hM 0 1
  obtain ⟨c, hc⟩ := hM 1 0
  obtain ⟨d, hd⟩ := hM 1 1
  exact ⟨a * d - b * c, by rw [map_sub, map_mul, map_mul, ha, hb, hc, hd]⟩

theorem norm_bc_le_one_of_mem_semiLocalIntegers {y : L ⊗[K] v.adicCompletion K}
    (hy : y ∈ semiLocalIntegers K L v) (w : v.Extension (𝓞 L)) : ‖bc K L v y w‖ ≤ 1 := by
  rw [semiLocalIntegers_eq_preimage] at hy
  have hw := hy w (Set.mem_univ w)
  exact norm_le_one_of_mem_integers L w.1 hw

theorem norm_bc_det_eq_one_of_mem_semiLocalIntegralSet {x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hx : x ∈ semiLocalIntegralSet K L v) (w : v.Extension (𝓞 L)) :
    ‖bc K L v ((Matrix.GeneralLinearGroup.det x : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) w‖
      = 1 := by
  obtain ⟨h1, h2⟩ := hx
  have hle : ‖bc K L v ((Matrix.GeneralLinearGroup.det x : (L ⊗[K] v.adicCompletion K)ˣ) :
      L ⊗[K] v.adicCompletion K) w‖ ≤ 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact norm_bc_le_one_of_mem_semiLocalIntegers K L v (det_mem_semiLocalIntegers K L v h1) w
  have hle' : ‖bc K L v ((Matrix.GeneralLinearGroup.det x⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) :
      L ⊗[K] v.adicCompletion K) w‖ ≤ 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact norm_bc_le_one_of_mem_semiLocalIntegers K L v (det_mem_semiLocalIntegers K L v h2) w
  have hprod : ‖bc K L v ((Matrix.GeneralLinearGroup.det x : (L ⊗[K] v.adicCompletion K)ˣ) :
      L ⊗[K] v.adicCompletion K) w‖ *
      ‖bc K L v ((Matrix.GeneralLinearGroup.det x⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) :
      L ⊗[K] v.adicCompletion K) w‖ = 1 := by
    rw [← norm_mul, ← Pi.mul_apply, ← map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
      Units.val_one, map_one, Pi.one_apply, norm_one]
  refine le_antisymm hle ?_
  have hmul := mul_le_of_le_one_right (norm_nonneg (bc K L v ((Matrix.GeneralLinearGroup.det x :
    (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) w)) hle'
  rw [hprod] at hmul
  exact hmul

theorem slMod_eq_one_of_mem_semiLocalIntegralSet {x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hx : x ∈ semiLocalIntegralSet K L v) : slMod K L v x = 1 :=
  Finset.prod_eq_one fun w _ => norm_bc_det_eq_one_of_mem_semiLocalIntegralSet K L v hx w

theorem slMod_eq_of_inv_mul_mem {a x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (h : a⁻¹ * x ∈ semiLocalIntegralSet K L v) : slMod K L v x = slMod K L v a := by
  have := slMod_eq_one_of_mem_semiLocalIntegralSet K L v h
  rw [slMod_mul] at this
  have hx : x = a * (a⁻¹ * x) := by group
  rw [hx, slMod_mul, slMod_mul, this, mul_one]

end SemiLocalMod

section FinBridge

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K))

theorem bc_semiLocalEval (a : FiniteAdeleRing (𝓞 L) L) (w : v.Extension (𝓞 L)) :
    bc K L v (semiLocalEval K L v a) w = a w.1 := by
  unfold semiLocalEval
  simp only [RingHom.coe_comp, Function.comp_apply]
  erw [AlgEquiv.apply_symm_apply]
  rfl

theorem coe_det_semiLocalComponent (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    ((Matrix.GeneralLinearGroup.det (semiLocalComponent K L v h) : (L ⊗[K] v.adicCompletion K)ˣ) :
        L ⊗[K] v.adicCompletion K) =
      semiLocalEval K L v ((Matrix.GeneralLinearGroup.det h : (FiniteAdeleRing (𝓞 L) L)ˣ) :
        FiniteAdeleRing (𝓞 L) L) := by
  unfold semiLocalComponent
  rw [Matrix.GeneralLinearGroup.map_det, Units.coe_map]
  rfl

theorem slMod_semiLocalComponent (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    slMod K L v (semiLocalComponent K L v h) =
      ∏ w : v.Extension (𝓞 L), ‖((Matrix.GeneralLinearGroup.det h : (FiniteAdeleRing (𝓞 L) L)ˣ) :
        FiniteAdeleRing (𝓞 L) L) w.1‖ := by
  unfold slMod
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [coe_det_semiLocalComponent, bc_semiLocalEval]

theorem norm_det_apply_eq_one_of_mem_semiLocalIntegralSet (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))
    (hh : semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v) (w : v.Extension (𝓞 L)) :
    ‖((Matrix.GeneralLinearGroup.det h : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) w.1‖ = 1 := by
  rw [← bc_semiLocalEval K L v, ← coe_det_semiLocalComponent]
  exact norm_bc_det_eq_one_of_mem_semiLocalIntegralSet K L v hh w

omit [NumberField K] [Algebra K L] in
theorem coe_det_apply_eq_det_finComponent (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (u : HeightOneSpectrum (𝓞 L)) :
    ((Matrix.GeneralLinearGroup.det h : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) u =
      ((Matrix.GeneralLinearGroup.det (finComponent (𝓞 L) L u h) : (u.adicCompletion L)ˣ) : u.adicCompletion L) := by
  unfold finComponent
  rw [Matrix.GeneralLinearGroup.map_det, Units.coe_map]
  rfl

theorem slMod_semiLocalComponent_localEmbed (w₀ : v.Extension (𝓞 L)) (r : GL (Fin 2) (w₀.1.adicCompletion L)) :
    slMod K L v (semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w₀.1 r)) =
      ‖((Matrix.GeneralLinearGroup.det r : (w₀.1.adicCompletion L)ˣ) : w₀.1.adicCompletion L)‖ := by
  rw [slMod_semiLocalComponent, Finset.prod_eq_single w₀]
  · rw [coe_det_apply_eq_det_finComponent, AdelicDock.finComponent_localEmbed_self]
  · intro w _ hw
    have hw' : w.1 ≠ w₀.1 := fun h => hw (Subtype.ext h)
    rw [coe_det_apply_eq_det_finComponent, AdelicDock.finComponent_localEmbed_of_ne (𝓞 L) L w₀.1 r hw',
      map_one, Units.val_one, norm_one]
  · intro h; exact absurd (Finset.mem_univ w₀) h

end FinBridge

section Regroup

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

open scoped Classical in

def placesAbove (U : Finset (HeightOneSpectrum (𝓞 K))) : Finset (HeightOneSpectrum (𝓞 L)) :=
  U.biUnion fun v => (Finset.univ : Finset (v.Extension (𝓞 L))).map (Function.Embedding.subtype _)

open scoped Classical in
theorem mem_placesAbove {U : Finset (HeightOneSpectrum (𝓞 K))} {w : HeightOneSpectrum (𝓞 L)}
    (hw : HeightOneSpectrum.under (𝓞 K) w ∈ U) : w ∈ placesAbove K L U := by
  unfold placesAbove
  rw [Finset.mem_biUnion]
  refine ⟨HeightOneSpectrum.under (𝓞 K) w, hw, ?_⟩
  rw [Finset.mem_map]
  exact ⟨(⟨w, rfl⟩ : (HeightOneSpectrum.under (𝓞 K) w).Extension (𝓞 L)),
    Finset.mem_univ (α := (HeightOneSpectrum.under (𝓞 K) w).Extension (𝓞 L)) _, rfl⟩

open scoped Classical in
theorem prod_placesAbove (U : Finset (HeightOneSpectrum (𝓞 K))) (f : HeightOneSpectrum (𝓞 L) → ℝ) :
    ∏ w ∈ placesAbove K L U, f w = ∏ v ∈ U, ∏ w : v.Extension (𝓞 L), f w.1 := by
  unfold placesAbove
  rw [Finset.prod_biUnion]
  · refine Finset.prod_congr rfl fun v _ => ?_
    rw [Finset.prod_map]
    rfl
  · intro v₁ _ v₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro w h₁ h₂
    rw [Finset.mem_map] at h₁ h₂
    obtain ⟨w₁, -, rfl⟩ := h₁
    obtain ⟨w₂, -, h⟩ := h₂
    apply hne
    have e₁ := w₁.2
    have e₂ := w₂.2
    rw [← e₁, ← e₂]
    exact congrArg (HeightOneSpectrum.under (𝓞 K)) h.symm

theorem finprod_norm_det_eq_prod_slMod (U : Finset (HeightOneSpectrum (𝓞 K)))
    (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))
    (hint : ∀ v ∉ U, semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v) :
    ∏ᶠ w : HeightOneSpectrum (𝓞 L),
        ‖((Matrix.GeneralLinearGroup.det h : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) w‖ =
      ∏ v ∈ U, slMod K L v (semiLocalComponent K L v h) := by
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := placesAbove K L U)]
  · rw [prod_placesAbove]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [slMod_semiLocalComponent]
  · intro w hw
    rw [Function.mem_mulSupport] at hw
    refine mem_placesAbove K L ?_
    by_contra hU
    apply hw
    have := norm_det_apply_eq_one_of_mem_semiLocalIntegralSet K L (HeightOneSpectrum.under (𝓞 K) w) h
      (hint _ hU) ⟨w, rfl⟩
    exact this

end Regroup

section Bounds

theorem exists_pos_bounds_on_isCompact {X : Type*} [TopologicalSpace X] {C : Set X} (hC : IsCompact C)
    {f : X → ℝ} (hf : Continuous f) (hpos : ∀ x, 0 < f x) :
    ∃ a b : ℝ, 0 < a ∧ ∀ x ∈ C, a ≤ f x ∧ f x ≤ b := by
  by_cases hne : C.Nonempty
  · obtain ⟨x₀, hx₀, hmin⟩ := hC.exists_isMinOn hne hf.continuousOn
    obtain ⟨x₁, hx₁, hmax⟩ := hC.exists_isMaxOn hne hf.continuousOn
    exact ⟨f x₀, f x₁, hpos x₀, fun x hx => ⟨hmin hx, hmax hx⟩⟩
  · refine ⟨1, 1, one_pos, fun x hx => ?_⟩
    exact absurd ⟨x, hx⟩ hne

end Bounds

section IdeleNormDet

variable (L : Type) [Field L] [NumberField L]

theorem coe_det_glArch (g : GL (Fin 2) (AdeleRing (𝓞 L) L)) :
    ((Matrix.GeneralLinearGroup.det (glArch (𝓞 L) L g) : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L) =
      ((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).1 := by
  unfold glArch
  rw [Matrix.GeneralLinearGroup.map_det, Units.coe_map]
  rfl

theorem coe_det_glFin (g : GL (Fin 2) (AdeleRing (𝓞 L) L)) :
    ((Matrix.GeneralLinearGroup.det (glFin (𝓞 L) L g) : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) =
      ((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 := by
  unfold glFin
  rw [Matrix.GeneralLinearGroup.map_det, Units.coe_map]
  rfl

theorem ideleNorm_det_eq_archMod_mul_finprod (g : GL (Fin 2) (AdeleRing (𝓞 L) L)) :
    TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) =
      archMod L (glArch (𝓞 L) L g) *
        ∏ᶠ w : HeightOneSpectrum (𝓞 L),
          ‖((Matrix.GeneralLinearGroup.det (glFin (𝓞 L) L g) : (FiniteAdeleRing (𝓞 L) L)ˣ) :
            FiniteAdeleRing (𝓞 L) L) w‖ := by
  rw [show TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) =
      (MeasureTheory.distribHaarChar (AdeleRing (𝓞 L) L) (Matrix.GeneralLinearGroup.det g) : ℝ) from rfl,
    NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm L, archMod, coe_det_glArch,
    coe_det_glFin]

end IdeleNormDet

end R1SuppDet
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_mul_prod_le_ideleNorm_det_le_of_isSemiLocalFactorization_of_apply_ne_zero.R1SuppDet"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_mul_prod_le_ideleNorm_det_le_of_isSemiLocalFactorization_of_apply_ne_zero.R1SuppDet"

open R1SuppDet in
open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L)
    (hϖs : ∀ v ∈ T, Irreducible (ϖs v))
    (hϖs0 : ∀ v ∈ T,
      algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
    (ns : HeightOneSpectrum (𝓞 K) → ℕ)
    (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L))
    (hrTs : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      HeckeIntegralSeam.IsHeckeCosetSystem
        (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
        (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v))
    (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
    (hzs : ∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
      algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
        (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L))) :
    ∃ m M : ℝ, 0 < m ∧
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        AutomorphicForm.IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
        ∀ g : GL (Fin 2) (AdeleRing (𝓞 L) L), φ g ≠ 0 →
          m * ∏ v ∈ T, (((Ideal.absNorm (ws v).1.asIdeal : ℕ) : ℝ)⁻¹) ^ (ks v + 2 * js v) ≤
              NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∧
            NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ≤
              M * ∏ v ∈ T, (((Ideal.absNorm (ws v).1.asIdeal : ℕ) : ℝ)⁻¹) ^ (ks v + 2 * js v) := by

  have harch : ∃ a₁ a₂ : ℝ, 0 < a₁ ∧ (HasCompactSupport φa →
      ∀ x ∈ tsupport φa, a₁ ≤ archMod L x ∧ archMod L x ≤ a₂) := by
    by_cases hc : HasCompactSupport φa
    · obtain ⟨a₁, a₂, h₁, h₂⟩ := exists_pos_bounds_on_isCompact hc (continuous_archMod L) (archMod_pos L)
      exact ⟨a₁, a₂, h₁, fun _ => h₂⟩
    · exact ⟨1, 1, one_pos, fun h => absurd h hc⟩
  obtain ⟨a₁, a₂, ha₁, harch⟩ := harch

  have hloc : ∀ v : HeightOneSpectrum (𝓞 K), ∃ b₁ b₂ : ℝ, 0 < b₁ ∧ (HasCompactSupport (φS v) →
      ∀ x ∈ tsupport (φS v), b₁ ≤ slMod K L v x ∧ slMod K L v x ≤ b₂) := by
    intro v
    by_cases hc : HasCompactSupport (φS v)
    · obtain ⟨b₁, b₂, h₁, h₂⟩ :=
        exists_pos_bounds_on_isCompact hc (continuous_slMod K L v) (slMod_pos K L v)
      exact ⟨b₁, b₂, h₁, fun _ => h₂⟩
    · exact ⟨1, 1, one_pos, fun h => absurd h hc⟩
  choose b₁ b₂ hb₁ hloc using hloc
  refine ⟨a₁ * ∏ v ∈ S \ T, b₁ v, a₂ * ∏ v ∈ S \ T, b₂ v,
    mul_pos ha₁ (Finset.prod_pos fun v _ => hb₁ v), ?_⟩
  intro ks js φ φf hfact g hg

  set P : ℝ := ∏ v ∈ T, (((Ideal.absNorm (ws v).1.asIdeal : ℕ) : ℝ)⁻¹) ^ (ks v + 2 * js v) with hP
  have hPpos : 0 < P := by
    rw [hP]
    refine Finset.prod_pos fun v _ => pow_pos (inv_pos.2 ?_) _
    have h1 := NumberField.HeightOneSpectrum.one_lt_absNorm (v := (ws v).1)
    exact_mod_cast lt_trans zero_lt_one h1

  obtain ⟨hφa, -, htest, -, -, -⟩ := id hfact
  obtain ⟨hane, hint, hfacne⟩ := support_decomposition (S ∪ T) hfact g hg
  set gf := glFin (𝓞 L) L g with hgf

  have hT : ∀ v ∈ T, slMod K L v (semiLocalComponent K L v gf) =
      (((Ideal.absNorm (ws v).1.asIdeal : ℕ) : ℝ)⁻¹) ^ (ks v + 2 * js v) := by
    intro v hv
    have h := hfacne v (Finset.mem_union_right S hv)
    rw [if_pos hv] at h
    obtain ⟨ι, hι⟩ := exists_inv_mul_mem_of_sum_indicator_ne_zero v
      (fun ι : Fin (ks v) → Fin (ns v) => semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
        ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v))) _ h
    rw [slMod_eq_of_inv_mul_mem K L v hι, slMod_semiLocalComponent_localEmbed,
      norm_det_heckeWord L (ws v).1 (hϖs v hv) (hϖs0 v hv) (rTs v) (hrTs v hv) (hzs v hv) (ks v) (js v) ι]

  have hST : ∀ v ∈ S \ T, b₁ v ≤ slMod K L v (semiLocalComponent K L v gf) ∧
      slMod K L v (semiLocalComponent K L v gf) ≤ b₂ v := by
    intro v hv
    rw [Finset.mem_sdiff] at hv
    have h := hfacne v (Finset.mem_union_left T hv.1)
    have ht := htest v (Finset.mem_union_left T hv.1)
    beta_reduce at ht
    rw [if_neg hv.2] at h ht
    exact hloc v ht.2 _ (subset_tsupport _ (Function.mem_support.mpr h))

  have hA := harch hφa.2 _ (subset_tsupport _ (Function.mem_support.mpr hane))

  have hnorm : NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) =
      archMod L (glArch (𝓞 L) L g) * ((∏ v ∈ S \ T, slMod K L v (semiLocalComponent K L v gf)) * P) := by
    rw [ideleNorm_det_eq_archMod_mul_finprod, finprod_norm_det_eq_prod_slMod K L (S ∪ T) _ hint,
      ← Finset.sdiff_union_self_eq_union, Finset.prod_union Finset.sdiff_disjoint, hP,
      ← Finset.prod_congr rfl hT]

  have hA0 : 0 ≤ archMod L (glArch (𝓞 L) L g) := (archMod_pos L _).le
  have hF0 : 0 ≤ ∏ v ∈ S \ T, slMod K L v (semiLocalComponent K L v gf) :=
    Finset.prod_nonneg fun v _ => slMod_nonneg K L v _
  have hb0 : 0 ≤ ∏ v ∈ S \ T, b₁ v := Finset.prod_nonneg fun v _ => (hb₁ v).le
  have hlow : ∏ v ∈ S \ T, b₁ v ≤ ∏ v ∈ S \ T, slMod K L v (semiLocalComponent K L v gf) :=
    Finset.prod_le_prod (fun v _ => (hb₁ v).le) fun v hv => (hST v hv).1
  have hupp : ∏ v ∈ S \ T, slMod K L v (semiLocalComponent K L v gf) ≤ ∏ v ∈ S \ T, b₂ v :=
    Finset.prod_le_prod (fun v _ => slMod_nonneg K L v _) fun v hv => (hST v hv).2
  rw [hnorm]
  constructor
  · calc a₁ * (∏ v ∈ S \ T, b₁ v) * P
        = a₁ * ((∏ v ∈ S \ T, b₁ v) * P) := by ring
      _ ≤ archMod L (glArch (𝓞 L) L g) * ((∏ v ∈ S \ T, slMod K L v (semiLocalComponent K L v gf)) * P) := by
        apply mul_le_mul hA.1 (mul_le_mul_of_nonneg_right hlow hPpos.le) (mul_nonneg hb0 hPpos.le) hA0
  · calc archMod L (glArch (𝓞 L) L g) * ((∏ v ∈ S \ T, slMod K L v (semiLocalComponent K L v gf)) * P)
        ≤ a₂ * ((∏ v ∈ S \ T, b₂ v) * P) := by
          apply mul_le_mul hA.2 (mul_le_mul_of_nonneg_right hupp hPpos.le) (mul_nonneg hF0 hPpos.le)
          exact le_trans ha₁.le (le_trans hA.1 hA.2)
      _ = a₂ * (∏ v ∈ S \ T, b₂ v) * P := by ring

end S_AutomorphicForm_exists_pos_forall_mul_prod_le_ideleNorm_det_le_of_isSemiLocalFactorization_of_apply_ne_zero
end P2MW
export P2MW.S_AutomorphicForm_exists_pos_forall_mul_prod_le_ideleNorm_det_le_of_isSemiLocalFactorization_of_apply_ne_zero (solution)
