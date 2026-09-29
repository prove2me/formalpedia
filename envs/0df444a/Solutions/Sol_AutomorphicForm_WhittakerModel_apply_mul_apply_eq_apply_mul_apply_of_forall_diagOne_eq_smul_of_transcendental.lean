-- Prove2me | solution 1 for AutomorphicForm.WhittakerModel.apply_mul_apply_eq_apply_mul_apply_of_forall_diagOne_eq_smul_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/542c5440-a37a-5c6c-8d1e-18afedd669fb

import Mathlib
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_RatIdele_Normalizer
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_NumberField_StandardAddChar_psiLocal_rat_eq_psiV
import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_finset_span_mod_unipotentCoinvariants_of_irreducible_admissible
import Theorems.Thm_AutomorphicForm_WhittakerModel_eq_zero_of_forall_apply_diagOne_eq_zero_of_mem_span_of_localLevelOne
import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_mem_span_forall_diagOne_eq_of_shell_window_of_localLevelOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_WhittakerModel_apply_mul_apply_eq_apply_mul_apply_of_forall_diagOne_eq_smul_of_transcendental

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open IsDedekindDomain NumberField NumberField.AdelicLevel UnramifiedWhittaker Topology Filter
open Rat.HeightOneSpectrum
open scoped Classical Pointwise

namespace TorusMultOne

section Span

variable {G : Type*} [Group G]

abbrev cyc (W₀ : G → ℂ) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ (Set.range fun h : G => fun g : G => W₀ (g * h))

theorem translate_mem_cyc (W₀ : G → ℂ) {W : G → ℂ} (hW : W ∈ cyc W₀) (h : G) :
    (fun g => W (g * h)) ∈ cyc W₀ := by
  induction hW using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h', rfl⟩ := hx
    refine Submodule.subset_span ⟨h * h', ?_⟩
    funext g
    simp only [mul_assoc]
  | zero => exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
    have : (fun g => (x + y) (g * h)) = (fun g => x (g * h)) + fun g => y (g * h) := rfl
    rw [this]
    exact Submodule.add_mem _ ihx ihy
  | smul a x _ ihx =>
    have : (fun g => (a • x) (g * h)) = a • fun g => x (g * h) := rfl
    rw [this]
    exact Submodule.smul_mem _ a ihx

theorem self_translate_mem_cyc (W₀ : G → ℂ) (h : G) : (fun g => W₀ (g * h)) ∈ cyc W₀ :=
  Submodule.subset_span ⟨h, rfl⟩

theorem law_of_mem_cyc {X : Type*} (W₀ : G → ℂ) (n : X → G) (ψ : X → ℂ)
    (hlaw : ∀ (x : X) (g : G), W₀ (n x * g) = ψ x * W₀ g) :
    ∀ W ∈ cyc W₀, ∀ (x : X) (g : G), W (n x * g) = ψ x * W g := by
  intro W hW
  induction hW using Submodule.span_induction with
  | mem W' hW' =>
    obtain ⟨h, rfl⟩ := hW'
    intro x g
    show W₀ (n x * g * h) = ψ x * W₀ (g * h)
    rw [mul_assoc, hlaw]
  | zero => intro x g; simp
  | add W₁ W₂ _ _ ih₁ ih₂ =>
    intro x g
    simp only [Pi.add_apply]
    rw [ih₁, ih₂, mul_add]
  | smul a W' _ ih =>
    intro x g
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [ih]
    ring

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem smooth_of_mem_cyc (W₀ : G → ℂ) (K₀ : Subgroup G) (hK₀ : IsOpen (K₀ : Set G))
    (hfix : ∀ k ∈ K₀, ∀ g : G, W₀ (g * k) = W₀ g) :
    ∀ W ∈ cyc W₀, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, W (g * k) = W g := by
  intro W hW
  induction hW using Submodule.span_induction with
  | mem W' hW' =>
    obtain ⟨h, rfl⟩ := hW'
    refine ⟨K₀.comap (MulAut.conj h⁻¹).toMonoidHom, ?_, ?_⟩
    · rw [Subgroup.coe_comap]
      refine hK₀.preimage ?_
      show Continuous fun k : G => (MulAut.conj h⁻¹) k
      simp only [MulAut.conj_apply, inv_inv]
      fun_prop
    · intro k hk g
      rw [Subgroup.mem_comap] at hk
      have hk' : h⁻¹ * k * h ∈ K₀ := by
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hk
      show W₀ (g * k * h) = W₀ (g * h)
      calc W₀ (g * k * h) = W₀ (g * h * (h⁻¹ * k * h)) := by group
        _ = W₀ (g * h) := hfix _ hk' _
  | zero => exact ⟨⊤, isOpen_univ, fun _ _ _ => rfl⟩
  | add W₁ W₂ _ _ ih₁ ih₂ =>
    obtain ⟨U₁, hU₁, h₁⟩ := ih₁
    obtain ⟨U₂, hU₂, h₂⟩ := ih₂
    refine ⟨U₁ ⊓ U₂, hU₁.inter hU₂, fun k hk g => ?_⟩
    simp only [Pi.add_apply]
    rw [h₁ k hk.1 g, h₂ k hk.2 g]
  | smul a W' _ ih =>
    obtain ⟨U, hU, h⟩ := ih
    refine ⟨U, hU, fun k hk g => ?_⟩
    simp only [Pi.smul_apply]
    rw [h k hk g]

end Span

section GL2

variable {F : Type*} [Field F]

theorem unipotent_val (x : F) :
    ((unipotent x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, x; 0, 1] := rfl

theorem unipotent_add (x y : F) : unipotent (x + y) = unipotent x * unipotent y := by
  apply Units.ext
  simp only [Units.val_mul, unipotent_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] ; ring

theorem unipotent_zero : (unipotent (0 : F)) = 1 := by
  apply Units.ext
  simp only [unipotent_val, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem unipotent_inv (x : F) : (unipotent x)⁻¹ = unipotent (-x) := by
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [← unipotent_add, neg_add_cancel, unipotent_zero]

theorem diagOne_val (y : Fˣ) :
    ((diagOne y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Matrix.diagonal ![(y : F), 1] := rfl

theorem diagOne_mul_unipotent (y : Fˣ) (x : F) :
    diagOne y * unipotent x = unipotent ((y : F) * x) * diagOne y := by
  apply Units.ext
  simp only [Units.val_mul, unipotent_val, diagOne_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal]

variable [TopologicalSpace F] [IsTopologicalRing F]

theorem continuous_unipotent : Continuous (unipotent : F → GL (Fin 2) F) := by
  have hval : Continuous fun x : F => ((unipotent x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    refine continuous_matrix fun i j => ?_
    simp only [unipotent_val]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  have h : (fun x : F => ((unipotent x)⁻¹ : GL (Fin 2) F).val) =
      fun x : F => ((unipotent (-x) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    funext x; rw [unipotent_inv]
  show Continuous fun x : F => ((unipotent x)⁻¹ : GL (Fin 2) F).val
  rw [h]
  exact hval.comp continuous_neg

variable [ContinuousInv₀ F]

theorem continuous_diagOne : Continuous (diagOne : Fˣ → GL (Fin 2) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · change Continuous (fun t : Fˣ => Matrix.diagonal ![(t : F), 1])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;>
      first | exact continuous_const | exact Units.continuous_val
  · change Continuous (fun t : Fˣ => Matrix.diagonal ![((t⁻¹ : Fˣ) : F), 1])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;>
      first
        | exact continuous_const
        | exact (Units.continuous_val.inv₀ fun a => a.ne_zero)

end GL2

section Local

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ

def varpi : F := algebraMap ℚ F ((natGenerator p : ℕ) : ℚ)

theorem valued_varpi : Valued.v (varpi p) = WithZero.exp (-1 : ℤ) := by
  rw [varpi, RatIdele.valued_algebraMap_rat, RatIdele.valuation_natGenerator]

theorem varpi_ne_zero : varpi p ≠ 0 := by
  intro h
  have := valued_varpi p
  rw [h, Valuation.map_zero] at this
  exact WithZero.zero_ne_coe this

theorem valued_varpi_zpow (m : ℤ) : Valued.v (varpi p ^ m) = WithZero.exp (-m) := by
  rw [map_zpow₀, valued_varpi, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem valued_varpi_pow (n : ℕ) : Valued.v (varpi p ^ n) = WithZero.exp (-(n : ℤ)) := by
  rw [← zpow_natCast, valued_varpi_zpow]

theorem natCast_natGenerator : ((natGenerator p : ℕ) : F) = varpi p := by
  rw [varpi, map_natCast]

theorem primesEquiv_val : ((primesEquiv p : Nat.Primes) : ℕ) = natGenerator p := rfl

theorem psiLocal_eq_one_iff (s : F) :
    NumberField.StandardAddChar.psiLocal ℚ p s = 1 ↔ Valued.v s ≤ 1 := by
  haveI : Fact (primesEquiv p : Nat.Primes).1.Prime := ⟨(primesEquiv p).2⟩
  rw [NumberField.StandardAddChar.psiLocal_rat_eq_psiV, NumberField.StandardAddChar.psiV_apply]
  constructor
  · intro h
    obtain ⟨a, k, ha⟩ := NumberField.StandardAddChar.exists_pPow_approx (adicCompletion.padicEquiv p s)
    rw [NumberField.StandardAddChar.psiPadic_apply, NumberField.StandardAddChar.psiPadicFun_eq ha,
      Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    have hqprime : ((primesEquiv p : Nat.Primes) : ℕ).Prime := (primesEquiv p).2
    have hqC : (((primesEquiv p : Nat.Primes) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hqprime.ne_zero

    have h1 : (a : ℂ) / (((primesEquiv p : Nat.Primes) : ℕ) : ℂ) ^ k = -(n : ℂ) := by
      have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have h3 : (2 * (Real.pi : ℂ) * Complex.I) * ((a : ℂ) / (((primesEquiv p : Nat.Primes) : ℕ) : ℂ) ^ k) =
          (2 * (Real.pi : ℂ) * Complex.I) * (-(n : ℂ)) := by
        linear_combination -hn
      exact mul_left_cancel₀ h2 h3
    have hval : (a : ℂ) = -(n : ℂ) * (((primesEquiv p : Nat.Primes) : ℕ) : ℂ) ^ k := by
      rw [div_eq_iff (pow_ne_zero _ hqC)] at h1; exact h1
    have hZ : a = -n * (((primesEquiv p : Nat.Primes) : ℕ) : ℤ) ^ k := by exact_mod_cast hval
    have hint : ((a : ℚ_[primesEquiv p]) / (((primesEquiv p : Nat.Primes) : ℕ) : ℚ_[primesEquiv p]) ^ k) =
        ((-n : ℤ) : ℚ_[primesEquiv p]) := by
      have hqQ : ((((primesEquiv p : Nat.Primes) : ℕ) : ℚ_[primesEquiv p])) ≠ 0 :=
        Nat.cast_ne_zero.mpr hqprime.ne_zero
      rw [hZ]; push_cast; field_simp
    have hnorm : ‖adicCompletion.padicEquiv p s‖ ≤ 1 := by
      have h1 : ‖((a : ℚ_[primesEquiv p]) / (((primesEquiv p : Nat.Primes) : ℕ) : ℚ_[primesEquiv p]) ^ k)‖ ≤ 1 := by
        rw [hint]; exact Padic.norm_int_le_one _
      calc ‖adicCompletion.padicEquiv p s‖
          = ‖(adicCompletion.padicEquiv p s -
              (a : ℚ_[primesEquiv p]) / (((primesEquiv p : Nat.Primes) : ℕ) : ℚ_[primesEquiv p]) ^ k) +
            (a : ℚ_[primesEquiv p]) / (((primesEquiv p : Nat.Primes) : ℕ) : ℚ_[primesEquiv p]) ^ k‖ := by
            rw [sub_add_cancel]
        _ ≤ max ‖adicCompletion.padicEquiv p s -
              (a : ℚ_[primesEquiv p]) / (((primesEquiv p : Nat.Primes) : ℕ) : ℚ_[primesEquiv p]) ^ k‖
            ‖(a : ℚ_[primesEquiv p]) / (((primesEquiv p : Nat.Primes) : ℕ) : ℚ_[primesEquiv p]) ^ k‖ :=
            Padic.nonarchimedean _ _
        _ ≤ 1 := max_le ha h1

    obtain ⟨s', hs', hs'x⟩ := (adicCompletion.padicEquiv_bijOn p).surjOn hnorm
    have hss' : s = s' := (adicCompletion.padicEquiv p).injective hs'x.symm
    rw [hss']
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).mp hs'
  · intro h
    exact NumberField.StandardAddChar.psiV_eq_one_of_mem_integers p
      ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).mpr h)

theorem exists_ball_subset_of_mem_nhds {x₀ : F} {s : Set F} (hs : s ∈ 𝓝 x₀) :
    ∃ n : ℕ, ∀ y : F, Valued.v (y - x₀) ≤ WithZero.exp (-(n : ℤ)) → y ∈ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hs
  have key : ∀ y : F,
      Valued.v.restrict (y - x₀) < γ.1 ↔ Valued.v (y - x₀) < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 :=
    fun y => Valuation.restrict_lt_iff_lt_embedding _
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ (0 : WithZero (Multiplicative ℤ)) :=
    (map_ne_zero MonoidWithZeroHom.ValueGroup₀.embedding).mpr γ.ne_zero
  obtain ⟨m, hm⟩ : ∃ m : ℤ, MonoidWithZeroHom.ValueGroup₀.embedding γ.1 =
      (WithZero.exp m : WithZero (Multiplicative ℤ)) :=
    ⟨_, (WithZero.exp_log hne).symm⟩
  refine ⟨(-m).toNat + 1, fun y hy => hγ ?_⟩
  show Valued.v.restrict (y - x₀) < γ.1
  rw [key, hm]
  refine lt_of_le_of_lt hy ?_
  rw [WithZero.exp_lt_exp]
  have : -m ≤ ((-m).toNat : ℤ) := Int.self_le_toNat (-m)
  push_cast
  omega

theorem exists_ball_subset_of_mem_nhds_units {s : Set Fˣ} (hs : s ∈ 𝓝 (1 : Fˣ)) :
    ∃ n : ℕ, ∀ u : Fˣ, Valued.v ((u : F) - 1) ≤ WithZero.exp (-(n : ℤ)) → u ∈ s := by
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap] at hs
  obtain ⟨t, ht, hts⟩ := hs
  rw [Units.val_one] at ht
  obtain ⟨n, hn⟩ := exists_ball_subset_of_mem_nhds p ht
  exact ⟨n, fun u hu => hts (hn u hu)⟩

theorem valued_eq_one_of_valued_sub_one_lt {x : F} (hx : Valued.v (x - 1) < 1) : Valued.v x = 1 := by
  have := Valuation.map_one_add_of_lt Valued.v hx
  rwa [show (1 : F) + (x - 1) = x by ring] at this

theorem exp_neg_natCast_lt_one {n : ℕ} (hn : 1 ≤ n) : (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) < 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega

theorem exp_neg_natCast_le_one (n : ℕ) : (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) ≤ 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega

def congr1 (n : ℕ) (hn : 1 ≤ n) : Subgroup Fˣ where
  carrier := {u | Valued.v ((u : F) - 1) ≤ WithZero.exp (-(n : ℤ))}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul] at ha hb ⊢
    have ha1 : Valued.v (a : F) = 1 :=
      valued_eq_one_of_valued_sub_one_lt p (lt_of_le_of_lt ha (exp_neg_natCast_lt_one hn))
    have : (a : F) * b - 1 = (a : F) * (b - 1) + (a - 1) := by ring
    rw [this]
    refine (Valuation.map_add Valued.v _ _).trans (max_le ?_ ha)
    rw [Valuation.map_mul, ha1, one_mul]; exact hb
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have ha1 : Valued.v (a : F) = 1 :=
      valued_eq_one_of_valued_sub_one_lt p (lt_of_le_of_lt ha (exp_neg_natCast_lt_one hn))
    have : ((a⁻¹ : Fˣ) : F) - 1 = ((a⁻¹ : Fˣ) : F) * (1 - a) := by
      rw [mul_sub, mul_one, Units.inv_mul]
    rw [this, Valuation.map_mul, Valuation.map_sub_swap]
    have hinv : Valued.v ((a⁻¹ : Fˣ) : F) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, ha1, inv_one]
    rw [hinv, one_mul]; exact ha

theorem mem_congr1 {n : ℕ} {hn : 1 ≤ n} {u : Fˣ} :
    u ∈ congr1 p n hn ↔ Valued.v ((u : F) - 1) ≤ WithZero.exp (-(n : ℤ)) := Iff.rfl

theorem valued_eq_one_of_mem_congr1 {n : ℕ} {hn : 1 ≤ n} {u : Fˣ} (hu : u ∈ congr1 p n hn) :
    Valued.v (u : F) = 1 :=
  valued_eq_one_of_valued_sub_one_lt p (lt_of_le_of_lt hu (exp_neg_natCast_lt_one hn))

theorem isOpen_ball (m : ℤ) : IsOpen {x : F | Valued.v x ≤ WithZero.exp m} := by
  have h := isOpen_setOf_valued_le p (varpi p ^ (-m)) (zpow_ne_zero _ (varpi_ne_zero p))
  rw [valued_varpi_zpow, neg_neg] at h
  exact h

theorem isClosed_ball (m : ℤ) : IsClosed {x : F | Valued.v x ≤ WithZero.exp m} := by
  have h := isClosed_setOf_valued_le p (varpi p ^ (-m)) (zpow_ne_zero _ (varpi_ne_zero p))
  rw [valued_varpi_zpow, neg_neg] at h
  exact h

theorem isCompact_ball (m : ℤ) : IsCompact {x : F | Valued.v x ≤ WithZero.exp m} := by
  have hint : IsCompact {x : F | Valued.v x ≤ (1 : WithZero (Multiplicative ℤ))} := by
    have h1 : IsCompact ((p.adicCompletionIntegers ℚ : Set F)) :=
      isCompact_iff_compactSpace.mpr (show CompactSpace (p.adicCompletionIntegers ℚ) from inferInstance)
    have h2 : ((p.adicCompletionIntegers ℚ : Set F)) = {x : F | Valued.v x ≤ (1 : WithZero (Multiplicative ℤ))} := by
      ext x; exact HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p
    rw [← h2]; exact h1
  have heq : {x : F | Valued.v x ≤ WithZero.exp m} = (fun x => varpi p ^ (-m) * x) '' {x : F | Valued.v x ≤ 1} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro hx
      refine ⟨(varpi p ^ (-m))⁻¹ * x, ?_,
        by rw [← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ (varpi_ne_zero p)), one_mul]⟩
      rw [Valuation.map_mul, map_inv₀, valued_varpi_zpow, neg_neg]
      calc (WithZero.exp m)⁻¹ * Valued.v x ≤ (WithZero.exp m)⁻¹ * WithZero.exp m :=
            mul_le_mul_right hx _
        _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
    · rintro ⟨z, hz, rfl⟩
      rw [Valuation.map_mul, valued_varpi_zpow, neg_neg]
      calc WithZero.exp m * Valued.v z ≤ WithZero.exp m * 1 := mul_le_mul_right hz _
        _ = WithZero.exp m := mul_one _
  rw [heq]
  exact hint.image (continuous_const.mul continuous_id)

theorem isOpen_congr1 (n : ℕ) (hn : 1 ≤ n) : IsOpen (congr1 p n hn : Set Fˣ) := by
  have hc : Continuous fun u : Fˣ => (u : F) - 1 := Units.continuous_val.sub continuous_const
  exact (isOpen_ball p (-(n : ℤ))).preimage hc

theorem mem_smul_congr1_iff {n : ℕ} {hn : 1 ≤ n} (t y : Fˣ) :
    y ∈ t • (congr1 p n hn : Set Fˣ) ↔ Valued.v (((y * t⁻¹ : Fˣ) : F) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  rw [mem_leftCoset_iff, SetLike.mem_coe, mem_congr1, mul_comm]

theorem smul_congr1_eq_of_mem {n : ℕ} {hn : 1 ≤ n} {t t' y : Fˣ}
    (hy : y ∈ t • (congr1 p n hn : Set Fˣ)) (hy' : y ∈ t' • (congr1 p n hn : Set Fˣ)) :
    t • (congr1 p n hn : Set Fˣ) = t' • (congr1 p n hn : Set Fˣ) := by
  rw [mem_leftCoset_iff] at hy hy'
  have h1 : t • (congr1 p n hn : Set Fˣ) = y • (congr1 p n hn : Set Fˣ) := by
    rw [eq_comm, leftCoset_eq_iff]; simpa using (congr1 p n hn).inv_mem hy
  have h2 : t' • (congr1 p n hn : Set Fˣ) = y • (congr1 p n hn : Set Fˣ) := by
    rw [eq_comm, leftCoset_eq_iff]; simpa using (congr1 p n hn).inv_mem hy'
  rw [h1, h2]

def window (n₁ n₀ : ℤ) : Set Fˣ :=
  {y | WithZero.exp (-n₀) ≤ Valued.v (y : F) ∧ Valued.v (y : F) ≤ WithZero.exp (-n₁)}

theorem isCompact_window (n₁ n₀ : ℤ) : IsCompact (window p n₁ n₀) := by
  have himg : Units.val '' window p n₁ n₀ =
      {x : F | WithZero.exp (-n₀) ≤ Valued.v x ∧ Valued.v x ≤ WithZero.exp (-n₁)} := by
    ext x
    simp only [Set.mem_image, window, Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · intro hx
      have hx0 : x ≠ 0 := by
        intro h0
        rw [h0, Valuation.map_zero] at hx
        exact WithZero.exp_ne_zero (le_antisymm hx.1 zero_le')
      exact ⟨Units.mk0 x hx0, hx, rfl⟩
  rw [Units.isEmbedding_val₀.isCompact_iff, himg]
  refine (isCompact_ball p (-n₁)).of_isClosed_subset ?_ (fun x hx => hx.2)
  have h1 : IsClosed {x : F | WithZero.exp (-n₀) ≤ Valued.v x} := by
    have : {x : F | WithZero.exp (-n₀) ≤ Valued.v x} = {x : F | Valued.v x ≤ WithZero.exp (-n₀ - 1)}ᶜ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
      constructor
      · intro h
        refine lt_of_lt_of_le ?_ h
        rw [WithZero.exp_lt_exp]; omega
      · intro h
        by_cases hx : Valued.v x = 0
        · rw [hx] at h; exact absurd h (not_lt.mpr zero_le')
        · obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v x = WithZero.exp m := ⟨_, (WithZero.exp_log hx).symm⟩
          rw [hm] at h ⊢
          rw [WithZero.exp_lt_exp] at h
          rw [WithZero.exp_le_exp]; omega
    rw [this, isClosed_compl_iff]
    exact isOpen_ball p _
  simpa [Set.setOf_and] using h1.inter (isClosed_ball p (-n₁))

theorem smul_congr1_subset_window {n : ℕ} {hn : 1 ≤ n} {n₁ n₀ : ℤ} {t : Fˣ} (ht : t ∈ window p n₁ n₀) :
    t • (congr1 p n hn : Set Fˣ) ⊆ window p n₁ n₀ := by
  intro y hy
  rw [mem_leftCoset_iff] at hy
  have h1 := valued_eq_one_of_mem_congr1 p hy
  rw [Units.val_mul, Units.val_inv_eq_inv_val, Valuation.map_mul, map_inv₀] at h1
  have ht0 : Valued.v (t : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr t.ne_zero
  have hy' : Valued.v (y : F) = Valued.v (t : F) := by
    have := congrArg (fun z => Valued.v (t : F) * z) h1
    simp only [mul_one] at this
    rwa [← mul_assoc, mul_inv_cancel₀ ht0, one_mul] at this
  simp only [window, Set.mem_setOf_eq] at ht ⊢
  rw [hy']; exact ht

end Local

section Decompose

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ

theorem exists_finset_eq_sum_indicator (f : Fˣ → ℂ) (n₁ n₀ : ℤ) (M : ℕ) (hM : 1 ≤ M)
    (hf₀ : ∀ y : Fˣ, WithZero.exp (-n₁) < Valued.v (y : F) ∨ Valued.v (y : F) < WithZero.exp (-n₀) → f y = 0)
    (hf₁ : ∀ y u : Fˣ, u ∈ congr1 p M hM → f (y * u) = f y) :
    ∃ (S : Finset (Set Fˣ)) (r : Set Fˣ → Fˣ),
      (∀ s ∈ S, r s • (congr1 p M hM : Set Fˣ) = s) ∧
      ∀ y : Fˣ, f y = ∑ s ∈ S, f (r s) * (if y ∈ r s • (congr1 p M hM : Set Fˣ) then 1 else 0) := by
  set H : Subgroup Fˣ := congr1 p M hM with hH
  set W : Set Fˣ := window p n₁ n₀ with hW
  have hWc : IsCompact W := isCompact_window p n₁ n₀

  have hcover : W ⊆ ⋃ i : W, ((i : Fˣ) • (H : Set Fˣ)) := by
    intro t ht
    refine Set.mem_iUnion.mpr ⟨⟨t, ht⟩, ?_⟩
    exact mem_leftCoset_iff _ |>.mpr (by simpa using H.one_mem)
  have hopen : ∀ i : W, IsOpen ((i : Fˣ) • (H : Set Fˣ)) := fun i =>
    (isOpen_congr1 p M hM).leftCoset _
  obtain ⟨T, hT⟩ := hWc.elim_finite_subcover _ hopen hcover

  let S : Finset (Set Fˣ) := T.image fun i : W => ((i : Fˣ) • (H : Set Fˣ))
  let r : Set Fˣ → Fˣ := fun s => if h : ∃ i ∈ T, (((i : W) : Fˣ) • (H : Set Fˣ)) = s then ((h.choose : W) : Fˣ) else 1
  have hr : ∀ s ∈ S, r s ∈ W ∧ r s • (H : Set Fˣ) = s := by
    intro s hs
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
    have h : ∃ j ∈ T, (((j : W) : Fˣ) • (H : Set Fˣ)) = (i : Fˣ) • (H : Set Fˣ) := ⟨i, hi, rfl⟩
    simp only [r, dif_pos h]
    exact ⟨h.choose.2, h.choose_spec.2⟩
  refine ⟨S, r, fun s hs => (hr s hs).2, fun y => ?_⟩
  by_cases hyW : y ∈ W
  ·
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hT hyW)
    obtain ⟨hiT, hyi⟩ := Set.mem_iUnion.mp hi
    set s₀ : Set Fˣ := (i : Fˣ) • (H : Set Fˣ) with hs₀
    have hs₀S : s₀ ∈ S := Finset.mem_image.mpr ⟨i, hiT, rfl⟩
    rw [Finset.sum_eq_single_of_mem s₀ hs₀S]
    · rw [(hr s₀ hs₀S).2, if_pos hyi, mul_one]

      have hy' : y ∈ r s₀ • (H : Set Fˣ) := by rw [(hr s₀ hs₀S).2]; exact hyi
      rw [mem_leftCoset_iff] at hy'
      have := hf₁ (r s₀) ((r s₀)⁻¹ * y) hy'
      rwa [mul_inv_cancel_left] at this
    · intro s hs hne
      rw [(hr s hs).2]
      have hys : y ∉ s := by
        intro hys
        apply hne
        rw [← (hr s hs).2] at hys ⊢
        exact smul_congr1_eq_of_mem p hys hyi
      rw [if_neg hys, mul_zero]
  ·
    have hfy : f y = 0 := by
      apply hf₀
      simp only [hW, window, Set.mem_setOf_eq, not_and_or, not_le] at hyW
      rcases hyW with h | h
      · exact Or.inr h
      · exact Or.inl h
    rw [hfy, eq_comm]
    refine Finset.sum_eq_zero fun s hs => ?_
    have hys : y ∉ r s • (H : Set Fˣ) := fun h =>
      hyW (smul_congr1_subset_window p (hr s hs).1 h)
    rw [if_neg hys, mul_zero]

end Decompose

section KirillovF

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ
local notation "G₂" => GL (Fin 2) (p.adicCompletion ℚ)
local notation "ψ" => NumberField.StandardAddChar.psiLocal ℚ p

def NearZero (w : G₂ → ℂ) : Prop :=
  ∃ n₀ : ℤ, ∀ y : Fˣ, Valued.v (y : F) < WithZero.exp n₀ → w (diagOne y) = 0

theorem NearZero.zero : NearZero p (0 : G₂ → ℂ) := ⟨0, fun _ _ => rfl⟩

theorem NearZero.add {w w' : G₂ → ℂ} (hw : NearZero p w) (hw' : NearZero p w') : NearZero p (w + w') := by
  obtain ⟨n, hn⟩ := hw
  obtain ⟨m, hm⟩ := hw'
  refine ⟨min n m, fun y hy => ?_⟩
  simp only [Pi.add_apply]
  rw [hn y (lt_of_lt_of_le hy (WithZero.exp_le_exp.mpr (min_le_left _ _))),
    hm y (lt_of_lt_of_le hy (WithZero.exp_le_exp.mpr (min_le_right _ _))), add_zero]

theorem NearZero.smul {w : G₂ → ℂ} (a : ℂ) (hw : NearZero p w) : NearZero p (a • w) := by
  obtain ⟨n, hn⟩ := hw
  exact ⟨n, fun y hy => by simp [Pi.smul_apply, hn y hy]⟩

theorem NearZero.sub {w w' : G₂ → ℂ} (hw : NearZero p w) (hw' : NearZero p w') : NearZero p (w - w') := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ w']
  exact NearZero.add p hw (NearZero.smul p _ hw')

theorem NearZero.translate {w : G₂ → ℂ} (hw : NearZero p w) (a : Fˣ) :
    NearZero p (fun g => w (g * diagOne a)) := by
  obtain ⟨n, hn⟩ := hw
  have ha0 : Valued.v (a : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr a.ne_zero
  obtain ⟨e, he⟩ : ∃ e : ℤ, Valued.v (a : F) = WithZero.exp e := ⟨_, (WithZero.exp_log ha0).symm⟩
  refine ⟨n - e, fun y hy => ?_⟩
  show w (diagOne y * diagOne a) = 0
  rw [← map_mul]
  apply hn
  rw [Units.val_mul, Valuation.map_mul, he]
  have hy0 : Valued.v (y : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  obtain ⟨d, hd⟩ : ∃ d : ℤ, Valued.v (y : F) = WithZero.exp d := ⟨_, (WithZero.exp_log hy0).symm⟩
  rw [hd, WithZero.exp_lt_exp] at hy
  rw [hd, ← WithZero.exp_add, WithZero.exp_lt_exp]
  omega

variable (w₀ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
  (hlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
    w₀ (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₀ g)

include hlaw in

theorem nearZero_of_mem_span_unipotent_sub {f : G₂ → ℂ}
    (hf : f ∈ Submodule.span ℂ {f : G₂ → ℂ | ∃ W' ∈ cyc w₀, ∃ t : F, f = fun g => W' (g * unipotent t) - W' g}) :
    NearZero p f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨W', hW', t, rfl⟩ := hf
    by_cases ht : t = 0
    · refine ⟨0, fun y _ => ?_⟩
      simp [ht, unipotent_zero]
    · obtain ⟨e, he⟩ : ∃ e : ℤ, Valued.v t = WithZero.exp e :=
        ⟨_, (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr ht)).symm⟩
      refine ⟨-e, fun y hy => ?_⟩
      show W' (diagOne y * unipotent t) - W' (diagOne y) = 0
      rw [diagOne_mul_unipotent, law_of_mem_cyc w₀ unipotent ψ hlaw W' hW']
      have h1 : ψ ((y : F) * t) = 1 := by
        rw [psiLocal_eq_one_iff, Valuation.map_mul, he]
        have hy0 : Valued.v (y : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
        obtain ⟨d, hd⟩ : ∃ d : ℤ, Valued.v (y : F) = WithZero.exp d := ⟨_, (WithZero.exp_log hy0).symm⟩
        rw [hd, WithZero.exp_lt_exp] at hy
        rw [hd, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
        omega
      rw [h1, one_mul, sub_self]
  | zero => exact NearZero.zero p
  | add f g _ _ hf hg => exact NearZero.add p hf hg
  | smul a f _ hf => exact NearZero.smul p a hf

include hlaw in

theorem apply_diagOne_eq_zero_of_le {w : G₂ → ℂ} (hw : w ∈ cyc w₀)
    {k : ℕ} (hk : ∀ x : F, Valued.v x ≤ WithZero.exp (-(k : ℤ)) → ∀ g : G₂, w (g * unipotent x) = w g)
    (y : Fˣ) (hy : WithZero.exp ((k : ℤ) + 1) ≤ Valued.v (y : F)) : w (diagOne y) = 0 := by
  have hy0 : Valued.v (y : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  obtain ⟨e, he⟩ : ∃ e : ℤ, Valued.v (y : F) = WithZero.exp e := ⟨_, (WithZero.exp_log hy0).symm⟩
  set x : F := ((y : F))⁻¹ * (varpi p)⁻¹ with hxdef
  have hx : Valued.v x ≤ WithZero.exp (-(k : ℤ)) := by
    rw [he, WithZero.exp_le_exp] at hy
    rw [hxdef, Valuation.map_mul, map_inv₀, map_inv₀, valued_varpi, he, ← WithZero.exp_neg, ← WithZero.exp_neg,
      ← WithZero.exp_add, WithZero.exp_le_exp]
    omega
  have h1 := hk x hx (diagOne y)
  rw [diagOne_mul_unipotent, law_of_mem_cyc w₀ unipotent ψ hlaw w hw] at h1
  have hyx : (y : F) * x = (varpi p)⁻¹ := by
    rw [hxdef, ← mul_assoc, mul_inv_cancel₀ y.ne_zero, one_mul]
  rw [hyx] at h1
  have hne : ψ (varpi p)⁻¹ ≠ 1 := by
    rw [Ne, psiLocal_eq_one_iff, map_inv₀, valued_varpi, ← WithZero.exp_neg, ← WithZero.exp_zero,
      WithZero.exp_le_exp]
    omega
  have h2 : (ψ (varpi p)⁻¹ - 1) * w (diagOne y) = 0 := by rw [sub_mul, one_mul, h1, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)

theorem exists_stabilizers (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (hK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : G₂, w₀ (g * k) = w₀ g)
    {w : G₂ → ℂ} (hw : w ∈ cyc w₀) :
    (∃ k : ℕ, ∀ x : F, Valued.v x ≤ WithZero.exp (-(k : ℤ)) → ∀ g : G₂, w (g * unipotent x) = w g) ∧
    (∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∀ u : Fˣ, Valued.v ((u : F) - 1) ≤ WithZero.exp (-(m₁ : ℤ)) →
      ∀ g : G₂, w (g * diagOne u) = w g) := by
  obtain ⟨-, hKopen⟩ := AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN
  obtain ⟨U, hUopen, hU⟩ := smooth_of_mem_cyc w₀ (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N) hKopen hK w hw
  constructor
  · have hmem : (unipotent : F → _) ⁻¹' (U : Set G₂) ∈ 𝓝 (0 : F) := by
      refine (hUopen.preimage continuous_unipotent).mem_nhds ?_
      show unipotent (0 : F) ∈ U
      rw [unipotent_zero]; exact U.one_mem
    obtain ⟨k, hk⟩ := exists_ball_subset_of_mem_nhds p hmem
    exact ⟨k, fun x hx g => hU _ (hk x (by simpa using hx)) g⟩
  · have hmem : (diagOne : Fˣ → _) ⁻¹' (U : Set G₂) ∈ 𝓝 (1 : Fˣ) := by
      refine (hUopen.preimage continuous_diagOne).mem_nhds ?_
      show diagOne (1 : Fˣ) ∈ U
      rw [map_one]; exact U.one_mem
    obtain ⟨m₁, hm₁⟩ := exists_ball_subset_of_mem_nhds_units p hmem
    refine ⟨max m₁ 1, le_max_right _ _, fun u hu g => hU _ (hm₁ u ?_) g⟩
    exact hu.trans (by rw [WithZero.exp_le_exp]; omega)

def bumpFn (M : ℕ) (hM : 1 ≤ M) (y : Fˣ) : ℂ := if y ∈ (congr1 p M hM : Set Fˣ) then 1 else 0

theorem bumpFn_window (M : ℕ) (hM : 1 ≤ M) (y : Fˣ)
    (hy : WithZero.exp (-(0 : ℤ)) < Valued.v (y : F) ∨ Valued.v (y : F) < WithZero.exp (-(0 : ℤ))) :
    bumpFn p M hM y = 0 := by
  have hne : Valued.v (y : F) ≠ 1 := by
    rw [neg_zero, WithZero.exp_zero] at hy
    rcases hy with h | h
    · exact ne_of_gt h
    · exact ne_of_lt h
  simp only [bumpFn]
  rw [if_neg]
  intro hmem
  exact hne (valued_eq_one_of_mem_congr1 p hmem)

theorem bumpFn_mul (M : ℕ) (hM : 1 ≤ M) (y u : Fˣ) (hu1 : Valued.v (u : F) = 1)
    (hu : Valued.v ((u : F) - 1) ≤ WithZero.exp (-(M : ℤ))) : bumpFn p M hM (y * u) = bumpFn p M hM y := by
  have huH : u ∈ congr1 p M hM := hu
  simp only [bumpFn, SetLike.mem_coe]
  rw [Subgroup.mul_mem_cancel_right _ huH]

include hlaw in

theorem eq_sum_smul_translate_bump
    (hinj : ∀ w ∈ cyc w₀, (∀ y : Fˣ, w (diagOne y) = 0) → w = 0)
    {w : G₂ → ℂ} (hw : w ∈ cyc w₀) (hw0 : NearZero p w)
    {k : ℕ} (hk : ∀ x : F, Valued.v x ≤ WithZero.exp (-(k : ℤ)) → ∀ g : G₂, w (g * unipotent x) = w g)
    {M : ℕ} (hM : 1 ≤ M) (hMw : ∀ u ∈ congr1 p M hM, ∀ g : G₂, w (g * diagOne u) = w g)
    {b : G₂ → ℂ} (hb : b ∈ cyc w₀) (hbK : ∀ y : Fˣ, b (diagOne y) = bumpFn p M hM y) :
    ∃ (S : Finset (Set Fˣ)) (r : Set Fˣ → Fˣ),
      w = ∑ s ∈ S, w (diagOne (r s)) • fun g => b (g * diagOne (r s)⁻¹) := by
  obtain ⟨n₀, hn₀⟩ := hw0
  have hf₀ : ∀ y : Fˣ, WithZero.exp (-(-((k : ℤ) + 1))) < Valued.v (y : F) ∨
      Valued.v (y : F) < WithZero.exp (-(-n₀)) → w (diagOne y) = 0 := by
    intro y hy
    rcases hy with h | h
    · exact apply_diagOne_eq_zero_of_le p w₀ hlaw hw hk y (by rw [neg_neg] at h; exact h.le)
    · exact hn₀ y (by rw [neg_neg] at h; exact h)
  have hf₁ : ∀ y u : Fˣ, u ∈ congr1 p M hM → w (diagOne (y * u)) = w (diagOne y) := by
    intro y u hu
    rw [map_mul]
    exact hMw u hu (diagOne y)
  obtain ⟨S, r, hr, hsum⟩ :=
    exists_finset_eq_sum_indicator p (fun y => w (diagOne y)) (-((k : ℤ) + 1)) (-n₀) M hM hf₀ hf₁
  refine ⟨S, r, ?_⟩
  have hmem : (∑ s ∈ S, w (diagOne (r s)) • fun g => b (g * diagOne (r s)⁻¹)) ∈ cyc w₀ :=
    Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (translate_mem_cyc w₀ hb _)
  have hdiff : w - (∑ s ∈ S, w (diagOne (r s)) • fun g => b (g * diagOne (r s)⁻¹)) = 0 := by
    refine hinj _ (Submodule.sub_mem _ hw hmem) fun y => ?_
    rw [Pi.sub_apply, Finset.sum_apply, sub_eq_zero, hsum y]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    congr 1
    show (if y ∈ r s • (congr1 p M hM : Set Fˣ) then (1 : ℂ) else 0) = b (diagOne y * diagOne (r s)⁻¹)
    rw [← map_mul, hbK]
    simp only [bumpFn, SetLike.mem_coe]
    have hiff : y ∈ r s • (congr1 p M hM : Set Fˣ) ↔ y * (r s)⁻¹ ∈ congr1 p M hM := by
      rw [mem_smul_congr1_iff]; exact Iff.rfl
    by_cases h : y * (r s)⁻¹ ∈ congr1 p M hM
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
  exact (sub_eq_zero.mp hdiff)

end KirillovF

section Key

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {𝕂 : Type*} [Field 𝕂] [Algebra ℂ 𝕂]

theorem apply_eq_zero_of_transcendental
    (V Vc : Submodule ℂ E)
    (T : E →ₗ[ℂ] E) (hTV : ∀ v ∈ V, T v ∈ V) (hTVc : ∀ v ∈ Vc, T v ∈ Vc)
    (B : Finset E) (hBV : (B : Set E) ⊆ V)
    (hB : ∀ v ∈ V, ∃ b ∈ Submodule.span ℂ (B : Set E), v - b ∈ Vc)
    (c₀ : 𝕂) (hc : Transcendental ℂ c₀)
    (Φ : E →ₗ[ℂ] 𝕂) (hΦT : ∀ v ∈ V, Φ (T v) = c₀ * Φ v) (hΦ0 : ∀ v ∈ Vc, Φ v = 0) :
    ∀ v ∈ V, Φ v = 0 := by
  classical

  let Vc' : Submodule ℂ V := Vc.comap V.subtype
  let T' : V →ₗ[ℂ] V := T.restrict (p := V) (q := V) (fun x hx => hTV x hx)
  have hT'coe : ∀ x : V, ((T' x : V) : E) = T (x : E) := fun x => rfl
  have hT'Vc : Vc' ≤ Vc'.comap T' := by
    intro x hx
    simp only [Vc', Submodule.mem_comap, Submodule.subtype_apply] at hx ⊢
    rw [hT'coe]
    exact hTVc _ hx
  let Tq : (V ⧸ Vc') →ₗ[ℂ] (V ⧸ Vc') := Vc'.mapQ Vc' T' hT'Vc
  let Φ' : V →ₗ[ℂ] 𝕂 := Φ.comp V.subtype
  have hker : Vc' ≤ LinearMap.ker Φ' := by
    intro x hx
    simp only [Vc', Submodule.mem_comap, Submodule.subtype_apply] at hx
    simp only [LinearMap.mem_ker, Φ', LinearMap.comp_apply, Submodule.subtype_apply]
    exact hΦ0 _ hx
  let Φq : (V ⧸ Vc') →ₗ[ℂ] 𝕂 := Vc'.liftQ Φ' hker
  have hΦq_mk : ∀ x : V, Φq (Submodule.Quotient.mk x) = Φ (x : E) := fun x => rfl
  have hTq_mk : ∀ x : V, Tq (Submodule.Quotient.mk x) = Submodule.Quotient.mk (T' x) := fun x => rfl

  have hΦqT : ∀ q : V ⧸ Vc', Φq (Tq q) = c₀ * Φq q := by
    intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective Vc' q
    rw [hTq_mk, hΦq_mk, hΦq_mk, hT'coe]
    exact hΦT x x.2

  haveI : Module.Finite ℂ (V ⧸ Vc') := by
    let ι : B → V ⧸ Vc' := fun b => Submodule.Quotient.mk ⟨(b : E), hBV b.2⟩
    have hspan : Submodule.span ℂ (Set.range ι) = ⊤ := by
      rw [eq_top_iff]
      rintro q -
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective Vc' q
      obtain ⟨b, hb, hxb⟩ := hB x x.2
      have hBV' : Submodule.span ℂ (B : Set E) ≤ V := Submodule.span_le.mpr hBV
      have hbV : b ∈ V := hBV' hb
      have hq : (Submodule.Quotient.mk x : V ⧸ Vc') = Submodule.Quotient.mk ⟨b, hbV⟩ := by
        rw [Submodule.Quotient.eq]
        simp only [Vc', Submodule.mem_comap, map_sub, Submodule.subtype_apply]
        exact hxb
      rw [hq]

      have hlift : (⟨b, hbV⟩ : V) ∈ Submodule.span ℂ (Set.range fun b' : B => (⟨(b' : E), hBV b'.2⟩ : V)) := by
        have hinj : Function.Injective (V.subtype) := Submodule.injective_subtype V
        rw [← Submodule.apply_mem_span_image_iff_mem_span hinj]
        have himg : (V.subtype) '' (Set.range fun b' : B => (⟨(b' : E), hBV b'.2⟩ : V)) = (B : Set E) := by
          ext e
          simp only [Set.mem_image, Set.mem_range, Submodule.subtype_apply]
          constructor
          · rintro ⟨y, ⟨b', rfl⟩, rfl⟩
            exact b'.2
          · intro he
            exact ⟨⟨e, hBV he⟩, ⟨⟨e, he⟩, rfl⟩, rfl⟩
        rw [himg]
        exact hb
      have himage := Submodule.apply_mem_span_image_of_mem_span (Vc'.mkQ) hlift
      have hrange : (Vc'.mkQ) '' (Set.range fun b' : B => (⟨(b' : E), hBV b'.2⟩ : V)) = Set.range ι := by
        rw [← Set.range_comp]
        rfl
      rw [hrange] at himage
      exact himage
    exact Module.finite_def.mpr (Submodule.fg_def.mpr ⟨Set.range ι, Set.finite_range ι, hspan⟩)

  have hCH : Polynomial.aeval Tq Tq.charpoly = 0 := LinearMap.aeval_self_charpoly Tq
  have hmonic : Tq.charpoly.Monic := LinearMap.charpoly_monic Tq
  have hpow : ∀ (n : ℕ) (q : V ⧸ Vc'), Φq ((Tq ^ n) q) = c₀ ^ n * Φq q := by
    intro n
    induction n with
    | zero => intro q; simp
    | succ n ih => intro q; rw [pow_succ', Module.End.mul_apply, hΦqT, ih, pow_succ', mul_assoc]
  have hpoly : ∀ (P : Polynomial ℂ) (q : V ⧸ Vc'),
      Φq (Polynomial.aeval Tq P q) = Polynomial.aeval c₀ P * Φq q := by
    intro P q
    rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, map_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply, map_smul, hpow, Algebra.smul_def, Algebra.smul_def, mul_assoc]
  have hne : Polynomial.aeval c₀ Tq.charpoly ≠ 0 := fun h0 => hc ⟨Tq.charpoly, hmonic.ne_zero, h0⟩
  have hΦq0 : ∀ q : V ⧸ Vc', Φq q = 0 := by
    intro q
    have h := hpoly Tq.charpoly q
    rw [hCH, LinearMap.zero_apply, map_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hne
  intro v hv
  have h := hΦq0 (Submodule.Quotient.mk ⟨v, hv⟩)
  rwa [hΦq_mk] at h

end Key

section Apply

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ
local notation "G₂" => GL (Fin 2) (p.adicCompletion ℚ)

theorem apply_sum_smul_translate {𝕂 : Type*} [Field 𝕂] [Algebra ℂ 𝕂]
    (V : Submodule ℂ (G₂ → ℂ)) (c : Fˣ → 𝕂) (L : (G₂ → ℂ) →ₗ[ℂ] 𝕂)
    (hL : ∀ (a : Fˣ), ∀ w ∈ V, L (fun g : G₂ => w (g * diagOne a)) = c a • L w)
    {b : G₂ → ℂ} (hb : b ∈ V) (S : Finset (Set Fˣ)) (a : Set Fˣ → ℂ) (t : Set Fˣ → Fˣ) :
    L (∑ s ∈ S, a s • fun g => b (g * diagOne (t s))) = (∑ s ∈ S, a s • c (t s)) * L b := by
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [LinearMap.map_smul, hL (t s) b hb, smul_eq_mul, smul_mul_assoc]

end Apply

end TorusMultOne

end

open IsDedekindDomain NumberField NumberField.AdelicLevel UnramifiedWhittaker Topology Filter
open MeasureTheory LanglandsTunnell.TateLocal

open TorusMultOne in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))

    (𝕂 : Type) [Field 𝕂] [Algebra ℂ 𝕂]
    (c : (p.adicCompletion ℚ)ˣ → 𝕂) (hc : Transcendental ℂ (c (uniformizerUnit ℚ p)))

    (L L' : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] 𝕂)
    (hL : ∀ (a : (p.adicCompletion ℚ)ˣ), ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      L (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * diagOne a)) = c a • L w)
    (hL' : ∀ (a : (p.adicCompletion ℚ)ˣ), ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      L' (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * diagOne a)) = c a • L' w) :
    ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        L w * L' w' = L w' * L' w := by
  classical

  change ∀ w ∈ cyc w₂base, ∀ w' ∈ cyc w₂base, L w * L' w' = L w' * L' w
  have hLc : ∀ (a : (p.adicCompletion ℚ)ˣ), ∀ w ∈ cyc w₂base,
      L (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * diagOne a)) = c a • L w := hL
  have hL'c : ∀ (a : (p.adicCompletion ℚ)ˣ), ∀ w ∈ cyc w₂base,
      L' (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * diagOne a)) = c a • L' w := hL'

  have hstab : ∀ W ∈ cyc w₂base, ∀ h : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * h)) ∈ cyc w₂base :=
    fun W hW h => translate_mem_cyc w₂base hW h
  obtain ⟨-, hKopen⟩ := AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN
  have hsmV := smooth_of_mem_cyc w₂base (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N) hKopen hw₂K
  have hirrV : ∀ W₀ ∈ cyc w₂base, W₀ ≠ 0 → ∀ W ∈ cyc w₂base,
      W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
        fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h)) := by
    intro W₀ hW₀ hne W hW
    have hbase : w₂base ∈ cyc W₀ := hw₂irr W₀ hW₀ hne
    have hle : cyc w₂base ≤ cyc W₀ := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨h, rfl⟩
      exact translate_mem_cyc W₀ hbase h
    exact hle hW

  have hinj : ∀ W ∈ cyc w₂base, (∀ y : (p.adicCompletion ℚ)ˣ, W (diagOne y) = 0) → W = 0 :=
    AutomorphicForm.WhittakerModel.eq_zero_of_forall_apply_diagOne_eq_zero_of_mem_span_of_localLevelOne
      p N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm
  have hbump : ∀ (M : ℕ) (hM : 1 ≤ M), ∃ b ∈ cyc w₂base,
      ∀ y : (p.adicCompletion ℚ)ˣ, b (diagOne y) = bumpFn p M hM y := fun M hM =>
    AutomorphicForm.WhittakerModel.exists_mem_span_forall_diagOne_eq_of_shell_window_of_localLevelOne
      p N hN w₂base hw₂law hw₂K hw₂ne hw₂irr (bumpFn p M hM) 0 0 M (bumpFn_window p M hM) (bumpFn_mul p M hM)
  obtain ⟨S, hSV, hS⟩ :=
    AutomorphicForm.WhittakerModel.exists_finset_span_mod_unipotentCoinvariants_of_irreducible_admissible
      p (cyc w₂base) hstab hsmV hw₂adm hirrV

  let Vc : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) :=
    { carrier := {v | v ∈ cyc w₂base ∧ NearZero p v}
      add_mem' := fun {a b} ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, NearZero.add p ha.2 hb.2⟩
      zero_mem' := ⟨Submodule.zero_mem _, NearZero.zero p⟩
      smul_mem' := fun r {a} ha => ⟨Submodule.smul_mem _ r ha.1, NearZero.smul p r ha.2⟩ }
  have hVc_mem : ∀ v, v ∈ Vc ↔ v ∈ cyc w₂base ∧ NearZero p v := fun v => Iff.rfl

  have hB : ∀ v ∈ cyc w₂base, ∃ b ∈ Submodule.span ℂ (S : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)), v - b ∈ Vc := by
    intro v hv
    obtain ⟨coef, hcoef⟩ := hS v hv
    refine ⟨∑ s ∈ S, coef s • s, Submodule.sum_mem _ fun s hs => Submodule.smul_mem _ _ (Submodule.subset_span hs), ?_⟩
    refine (hVc_mem _).mpr ⟨?_, nearZero_of_mem_span_unipotent_sub p w₂base hw₂law hcoef⟩
    exact Submodule.sub_mem _ hv (Submodule.sum_mem _ fun s hs => Submodule.smul_mem _ _ (hSV hs))

  let ϖ : (p.adicCompletion ℚ)ˣ := uniformizerUnit ℚ p
  let T : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => g * diagOne ϖ)
  have hT_apply : ∀ v, T v = fun g => v (g * diagOne ϖ) := fun v => rfl
  have hTV : ∀ v ∈ cyc w₂base, T v ∈ cyc w₂base := fun v hv => by rw [hT_apply]; exact hstab v hv _
  have hTVc : ∀ v ∈ Vc, T v ∈ Vc := fun v hv => by
    rw [hT_apply]
    exact (hVc_mem _).mpr ⟨hstab v hv.1 _, NearZero.translate p hv.2 ϖ⟩

  have hcross : ∀ v ∈ Vc, ∀ v' ∈ Vc, L v * L' v' = L v' * L' v := by
    intro v hv v' hv'
    obtain ⟨⟨k, hk⟩, ⟨m, hm1, hm⟩⟩ := exists_stabilizers p w₂base N hN hw₂K hv.1
    obtain ⟨⟨k', hk'⟩, ⟨m', hm1', hm'⟩⟩ := exists_stabilizers p w₂base N hN hw₂K hv'.1
    have hM : 1 ≤ max m m' := le_max_of_le_left hm1
    have hMv : ∀ u ∈ congr1 p (max m m') hM, ∀ g, v (g * diagOne u) = v g := fun u hu g =>
      hm u ((mem_congr1 p).mp hu |>.trans (by rw [WithZero.exp_le_exp]; omega)) g
    have hMv' : ∀ u ∈ congr1 p (max m m') hM, ∀ g, v' (g * diagOne u) = v' g := fun u hu g =>
      hm' u ((mem_congr1 p).mp hu |>.trans (by rw [WithZero.exp_le_exp]; omega)) g
    obtain ⟨b, hb, hbK⟩ := hbump (max m m') hM
    obtain ⟨S₁, r₁, h₁⟩ := eq_sum_smul_translate_bump p w₂base hw₂law hinj hv.1 hv.2 hk hM hMv hb hbK
    obtain ⟨S₂, r₂, h₂⟩ := eq_sum_smul_translate_bump p w₂base hw₂law hinj hv'.1 hv'.2 hk' hM hMv' hb hbK
    have e1 := apply_sum_smul_translate p (cyc w₂base) c L hLc hb S₁ (fun s => v (diagOne (r₁ s))) (fun s => (r₁ s)⁻¹)
    have e2 := apply_sum_smul_translate p (cyc w₂base) c L' hL'c hb S₁ (fun s => v (diagOne (r₁ s))) (fun s => (r₁ s)⁻¹)
    have e3 := apply_sum_smul_translate p (cyc w₂base) c L hLc hb S₂ (fun s => v' (diagOne (r₂ s))) (fun s => (r₂ s)⁻¹)
    have e4 := apply_sum_smul_translate p (cyc w₂base) c L' hL'c hb S₂ (fun s => v' (diagOne (r₂ s))) (fun s => (r₂ s)⁻¹)
    rw [← h₁] at e1 e2
    rw [← h₂] at e3 e4
    rw [e1, e2, e3, e4]
    ring

  have hstep2 : ∀ w' ∈ Vc, ∀ v ∈ cyc w₂base, L' w' * L v - L w' * L' v = 0 := by
    intro w' hw'
    let Φ : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] 𝕂 := (L' w') • L - (L w') • L'
    have hΦ_apply : ∀ v, Φ v = L' w' * L v - L w' * L' v := fun v => by
      simp only [Φ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    have hΦT : ∀ v ∈ cyc w₂base, Φ (T v) = c ϖ * Φ v := by
      intro v hv
      rw [hΦ_apply, hΦ_apply, hT_apply, hLc ϖ v hv, hL'c ϖ v hv, smul_eq_mul, smul_eq_mul]
      ring
    have hΦ0 : ∀ v ∈ Vc, Φ v = 0 := by
      intro v hv
      rw [hΦ_apply, sub_eq_zero, mul_comm (L' w') (L v), hcross v hv w' hw', mul_comm]
    intro v hv
    rw [← hΦ_apply]
    exact apply_eq_zero_of_transcendental (cyc w₂base) Vc T hTV hTVc S hSV hB (c ϖ) hc Φ hΦT hΦ0 v hv

  intro w hw w' hw'
  let Ψ : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] 𝕂 := (L w) • L' - (L' w) • L
  have hΨ_apply : ∀ u, Ψ u = L w * L' u - L' w * L u := fun u => by
    simp only [Ψ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  have hΨT : ∀ u ∈ cyc w₂base, Ψ (T u) = c ϖ * Ψ u := by
    intro u hu
    rw [hΨ_apply, hΨ_apply, hT_apply, hLc ϖ u hu, hL'c ϖ u hu, smul_eq_mul, smul_eq_mul]
    ring
  have hΨ0 : ∀ u ∈ Vc, Ψ u = 0 := by
    intro u hu
    rw [hΨ_apply, sub_eq_zero]
    have := hstep2 u hu w hw
    rw [sub_eq_zero] at this

    calc L w * L' u = L' u * L w := mul_comm _ _
      _ = L u * L' w := this
      _ = L' w * L u := mul_comm _ _
  have hfin := apply_eq_zero_of_transcendental (cyc w₂base) Vc T hTV hTVc S hSV hB (c ϖ) hc Ψ hΨT hΨ0 w' hw'
  rw [hΨ_apply, sub_eq_zero] at hfin

  rw [hfin, mul_comm]

end S_AutomorphicForm_WhittakerModel_apply_mul_apply_eq_apply_mul_apply_of_forall_diagOne_eq_smul_of_transcendental
end P2MW
export P2MW.S_AutomorphicForm_WhittakerModel_apply_mul_apply_eq_apply_mul_apply_of_forall_diagOne_eq_smul_of_transcendental (solution)
