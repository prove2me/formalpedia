-- Prove2me | solution 1 for AutomorphicForm.WhittakerModel.exists_finset_span_mod_unipotentCoinvariants_of_irreducible_admissible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/0492568b-eda3-5091-82c5-c4a4f77138f9

import Mathlib
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_WhittakerModel_exists_finset_span_mod_unipotentCoinvariants_of_irreducible_admissible

set_option autoImplicit false

open IsDedekindDomain NumberField UnramifiedWhittaker
open scoped Matrix

noncomputable section

namespace KirillovJ

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ
local notation "G" => GL (Fin 2) (p.adicCompletion ℚ)
local notation "𝕧" => (Valued.v : p.adicCompletion ℚ → WithZero (Multiplicative ℤ))

def lowerUni (c : F) : G :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; c, 1] (by simp [Matrix.det_fin_two_of])

def diagU (a d : (p.adicCompletion ℚ)ˣ) : G where
  val := Matrix.diagonal ![(a : F), d]
  inv := Matrix.diagonal ![((a⁻¹ : (p.adicCompletion ℚ)ˣ) : F), ((d⁻¹ : (p.adicCompletion ℚ)ˣ) : F)]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp

def weyl : G :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by simp [Matrix.det_fin_two_of])

theorem unipotent_coe (t : F) : ((unipotent t : G) : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := rfl
theorem lowerUni_coe (c : F) : ((lowerUni p c : G) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; c, 1] := rfl
theorem diagU_coe (a d : (p.adicCompletion ℚ)ˣ) :
    ((diagU p a d : G) : Matrix (Fin 2) (Fin 2) F) = Matrix.diagonal ![(a : F), d] := rfl
theorem weyl_coe : ((weyl p : G) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := rfl

theorem unipotent_add (s t : F) : (unipotent s : G) * unipotent t = unipotent (s + t) := by
  exact Matrix.GeneralLinearGroup.ext fun i j => by
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, unipotent_coe, add_comm]

theorem unipotent_zero : (unipotent (0 : F) : G) = 1 := by
  exact Matrix.GeneralLinearGroup.ext fun i j => by
    fin_cases i <;> fin_cases j <;> simp [unipotent_coe]

theorem lowerUni_add (s t : F) : lowerUni p s * lowerUni p t = lowerUni p (s + t) := by
  exact Matrix.GeneralLinearGroup.ext fun i j => by
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, lowerUni_coe]

theorem diagU_mul (a d a' d' : (p.adicCompletion ℚ)ˣ) :
    diagU p a d * diagU p a' d' = diagU p (a * a') (d * d') := by
  exact Matrix.GeneralLinearGroup.ext fun i j => by
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, diagU_coe, Matrix.diagonal]

theorem diagU_one : diagU p 1 1 = 1 := by
  exact Matrix.GeneralLinearGroup.ext fun i j => by
    fin_cases i <;> fin_cases j <;> simp [diagU_coe, Matrix.diagonal]

theorem diagU_mul_unipotent (a d : (p.adicCompletion ℚ)ˣ) (t : F) :
    diagU p a d * unipotent t = unipotent ((a : F) * t * ((d⁻¹ : (p.adicCompletion ℚ)ˣ) : F)) * diagU p a d := by
  exact Matrix.GeneralLinearGroup.ext fun i j => by
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, unipotent_coe, diagU_coe, Matrix.diagonal]

theorem lowerUni_mul_diagU (a d : (p.adicCompletion ℚ)ˣ) (c : F) :
    lowerUni p c * diagU p a d = diagU p a d * lowerUni p (c * (a : F) * ((d⁻¹ : (p.adicCompletion ℚ)ˣ) : F)) := by
  exact Matrix.GeneralLinearGroup.ext fun i j => by
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, lowerUni_coe, diagU_coe, Matrix.diagonal]
    field_simp

theorem v_one_apply_le (i j : Fin 2) : 𝕧 ((1 : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1 := by
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem exp_neg_nat_le_one (n : ℕ) : WithZero.exp (-(n : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega

theorem v_mul_apply_le {A B : Matrix (Fin 2) (Fin 2) F} {a b : WithZero (Multiplicative ℤ)}
    (hA : ∀ i j, 𝕧 (A i j) ≤ a) (hB : ∀ i j, 𝕧 (B i j) ≤ b) (i j : Fin 2) : 𝕧 ((A * B) i j) ≤ a * b := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ (fun k _ => ?_)
  rw [Valuation.map_mul]
  exact mul_le_mul' (hA i k) (hB k j)

theorem mul_sub_one_eq (M N : Matrix (Fin 2) (Fin 2) F) : M * N - 1 = (M - 1) * (N - 1) + (M - 1) + (N - 1) := by
  noncomm_ring

def congMonoid (n : ℕ) : Submonoid (Matrix (Fin 2) (Fin 2) F) where
  carrier := {M | ∀ i j, 𝕧 ((M - 1) i j) ≤ WithZero.exp (-(n : ℤ))}
  one_mem' := by
    intro i j; simp
  mul_mem' := by
    intro M N hM hN i j
    simp only [Set.mem_setOf_eq] at hM hN ⊢
    rw [mul_sub_one_eq]
    refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ (hM i j)) (hN i j)
    calc 𝕧 (((M - 1) * (N - 1)) i j) ≤ WithZero.exp (-(n : ℤ)) * WithZero.exp (-(n : ℤ)) :=
          v_mul_apply_le p hM hN i j
      _ ≤ WithZero.exp (-(n : ℤ)) * 1 := mul_le_mul_right (exp_neg_nat_le_one n) _
      _ = _ := mul_one _

def Kc (n : ℕ) : Subgroup G := (congMonoid p n).units

theorem mem_Kc_iff (n : ℕ) (g : G) : g ∈ Kc p n ↔
    (∀ i j, 𝕧 (((g : Matrix (Fin 2) (Fin 2) F) - 1) i j) ≤ WithZero.exp (-(n : ℤ))) ∧
    (∀ i j, 𝕧 ((((g⁻¹ : G) : Matrix (Fin 2) (Fin 2) F) - 1) i j) ≤ WithZero.exp (-(n : ℤ))) :=
  Submonoid.mem_units_iff _ _

theorem mem_Kc_zero_iff (g : G) : g ∈ Kc p 0 ↔
    (∀ i j, 𝕧 ((g : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1) ∧
    (∀ i j, 𝕧 (((g⁻¹ : G) : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1) := by
  have key : ∀ M : Matrix (Fin 2) (Fin 2) F,
      (∀ i j, 𝕧 ((M - 1) i j) ≤ WithZero.exp (-((0 : ℕ) : ℤ))) ↔ ∀ i j, 𝕧 (M i j) ≤ 1 := by
    intro M
    simp only [Nat.cast_zero, neg_zero, WithZero.exp_zero, Matrix.sub_apply]
    constructor
    · intro h i j
      have := Valuation.map_add_le _ (h i j) (v_one_apply_le p i j)
      simpa using this
    · intro h i j
      exact Valuation.map_sub_le _ (h i j) (v_one_apply_le p i j)
  rw [mem_Kc_iff, key, key]

theorem isLocalLevelOne_top_iff (m : Matrix (Fin 2) (Fin 2) F) :
    AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ m ↔ ∀ i j, 𝕧 (m i j) ≤ 1 := by
  constructor
  · intro h i j
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 ℚ) (K := ℚ) (v := p)).mp (h.integral i j)
  · intro h
    refine ⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 ℚ) (K := ℚ) (v := p)).mpr (h i j), ?_, ?_⟩
    · rw [AdelicLevel.idealBound_top]; exact h 1 0
    · rw [AdelicLevel.idealBound_top]; exact Valuation.map_sub_le _ (h 1 1) (by simp)

theorem localLevelOne_top_eq_Kc_zero : AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ = Kc p 0 := by
  ext g
  rw [AdelicDock.mem_localLevelOne_iff, isLocalLevelOne_top_iff, isLocalLevelOne_top_iff, mem_Kc_zero_iff]

theorem Kc_antitone {m n : ℕ} (h : n ≤ m) : Kc p m ≤ Kc p n := by
  intro g hg
  rw [mem_Kc_iff] at hg ⊢
  have hle : WithZero.exp (-(m : ℤ)) ≤ WithZero.exp (-(n : ℤ)) := by
    rw [WithZero.exp_le_exp]; omega
  exact ⟨fun i j => (hg.1 i j).trans hle, fun i j => (hg.2 i j).trans hle⟩

private theorem C_exists_val_eq (γ : WithZero (Multiplicative ℤ)) : ∃ x : F, 𝕧 x = γ := by
  obtain ⟨k, hk⟩ := p.valuation_surjective ℚ γ
  exact ⟨_, (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := p) k).trans hk⟩

private theorem C_isClopen_le {γ : WithZero (Multiplicative ℤ)} (hγ : γ ≠ 0) :
    IsClopen {x : F | 𝕧 x ≤ γ} := by
  obtain ⟨x₀, hx₀⟩ := C_exists_val_eq p γ
  have h0 : (Valued.v : Valuation F (WithZero (Multiplicative ℤ))).restrict x₀ ≠ 0 := by
    rw [ne_eq, Valuation.restrict_eq_zero_iff, hx₀]; exact hγ
  have : {x : F | 𝕧 x ≤ γ} = {x : F | Valued.v.restrict x ≤ Valued.v.restrict x₀} := by
    ext x; simp only [Set.mem_setOf_eq, Valuation.restrict_le_iff, hx₀]
  rw [this]
  exact Valued.isClopen_closedBall F h0

private theorem C_coe_congMonoid (n : ℕ) : (congMonoid p n : Set (Matrix (Fin 2) (Fin 2) F)) =
    ⋂ i, ⋂ j, (fun M : Matrix (Fin 2) (Fin 2) F => (M - 1) i j) ⁻¹'
      {x : F | 𝕧 x ≤ WithZero.exp (-(n : ℤ))} := by
  ext M
  simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
  rfl

private theorem C_continuous_entry (i j : Fin 2) :
    Continuous (fun M : Matrix (Fin 2) (Fin 2) F => (M - 1) i j) :=
  (continuous_id.sub continuous_const).matrix_elem i j

private theorem C_isOpen_congMonoid (n : ℕ) :
    IsOpen (congMonoid p n : Set (Matrix (Fin 2) (Fin 2) F)) := by
  rw [C_coe_congMonoid]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (C_isClopen_le p WithZero.exp_ne_zero).isOpen.preimage (C_continuous_entry p i j)

private theorem C_isClosed_congMonoid (n : ℕ) :
    IsClosed (congMonoid p n : Set (Matrix (Fin 2) (Fin 2) F)) := by
  rw [C_coe_congMonoid]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    (C_isClopen_le p WithZero.exp_ne_zero).isClosed.preimage (C_continuous_entry p i j)

private theorem C_isCompact_integralMatrices :
    IsCompact {M : Matrix (Fin 2) (Fin 2) F | ∀ i j, 𝕧 (M i j) ≤ 1} := by
  have hO : IsCompact {x : F | 𝕧 x ≤ 1} := by
    have : IsCompact (p.adicCompletionIntegers ℚ : Set F) :=
      isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (p.adicCompletionIntegers ℚ)))
    convert this using 1
    rfl
  have : {M : Matrix (Fin 2) (Fin 2) F | ∀ i j, 𝕧 (M i j) ≤ 1} =
      Set.pi Set.univ (fun _ : Fin 2 => Set.pi Set.univ (fun _ : Fin 2 => {x : F | 𝕧 x ≤ 1})) := by
    ext M
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hO

private theorem C_isCompact_congMonoid (n : ℕ) :
    IsCompact (congMonoid p n : Set (Matrix (Fin 2) (Fin 2) F)) := by
  refine (C_isCompact_integralMatrices p).of_isClosed_subset (C_isClosed_congMonoid p n) ?_
  intro M hM i j
  have hM' : 𝕧 ((M - 1) i j) ≤ WithZero.exp (-(n : ℤ)) := hM i j
  have h1 : 𝕧 ((M - 1) i j) ≤ 1 :=
    hM'.trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  have h2 : 𝕧 ((1 : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1 := by
    rw [Matrix.one_apply]; split_ifs <;> simp
  have : M i j = (M - 1) i j + (1 : Matrix (Fin 2) (Fin 2) F) i j := by simp [Matrix.sub_apply]
  show 𝕧 (M i j) ≤ 1
  rw [this]
  exact Valuation.map_add_le _ h1 h2

private theorem C_coe_Kc (n : ℕ) : (Kc p n : Set G) =
    (Units.val ⁻¹' (congMonoid p n : Set (Matrix (Fin 2) (Fin 2) F))) ∩
    ((fun g : G => ((g⁻¹ : G) : Matrix (Fin 2) (Fin 2) F)) ⁻¹' (congMonoid p n)) := by
  ext g
  simp only [Kc, SetLike.mem_coe, Submonoid.mem_units_iff, Set.mem_inter_iff, Set.mem_preimage]

theorem isOpen_Kc (n : ℕ) : IsOpen (Kc p n : Set G) := by
  rw [C_coe_Kc]
  exact ((C_isOpen_congMonoid p n).preimage Units.continuous_val).inter
    ((C_isOpen_congMonoid p n).preimage Units.continuous_coe_inv)

theorem isCompact_Kc (n : ℕ) : IsCompact (Kc p n : Set G) := by
  exact Submonoid.units_isCompact (C_isCompact_congMonoid p n)

private theorem C_eq_zero_of_forall_le {γ : WithZero (Multiplicative ℤ)}
    (h : ∀ n : ℕ, γ ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ))) : γ = 0 := by
  by_contra hγ
  have := h (WithZero.log γ).natAbs
  rw [← WithZero.exp_log hγ, WithZero.exp_le_exp, WithZero.log_exp] at this
  omega

theorem exists_Kc_le_of_isOpen (U : Subgroup G) (hU : IsOpen (U : Set G)) : ∃ n : ℕ, 1 ≤ n ∧ Kc p n ≤ U := by
  have hdir : Directed (· ⊇ ·) (fun n : ℕ => (Kc p (n + 1) : Set G)) := fun a b =>
    ⟨max a b, SetLike.coe_subset_coe.mpr (Kc_antitone p (by omega)),
      SetLike.coe_subset_coe.mpr (Kc_antitone p (by omega))⟩
  have hint : ∀ x ∈ ⋂ n : ℕ, (Kc p (n + 1) : Set G), (U : Set G) ∈ nhds x := by
    intro x hx
    have hmem : ∀ n : ℕ, (x : Matrix (Fin 2) (Fin 2) F) ∈ congMonoid p (n + 1) := fun n =>
      ((Submonoid.mem_units_iff _ _).mp (Set.mem_iInter.mp hx n)).1
    have hent : ∀ i j, ((x : Matrix (Fin 2) (Fin 2) F) - 1) i j = 0 := fun i j =>
      (Valuation.zero_iff _).mp (C_eq_zero_of_forall_le (fun n => hmem n i j))
    have hx1 : (x : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← sub_eq_zero]; ext i j; exact hent i j
    rw [Units.val_eq_one.mp hx1]
    exact hU.mem_nhds U.one_mem
  obtain ⟨n, hn⟩ := exists_subset_nhds_of_isCompact hdir (fun n => isCompact_Kc p (n + 1)) hint
  exact ⟨n + 1, by omega, fun g hg => hn hg⟩

theorem conj_mem_Kc {n : ℕ} {k g : G} (hk : k ∈ Kc p 0) (hg : g ∈ Kc p n) : k * g * k⁻¹ ∈ Kc p n := by
  rw [mem_Kc_zero_iff] at hk
  rw [mem_Kc_iff] at hg ⊢

  have key : ∀ X : Matrix (Fin 2) (Fin 2) F, (∀ i j, 𝕧 ((X - 1) i j) ≤ WithZero.exp (-(n : ℤ))) →
      ∀ i j, 𝕧 (((k : Matrix (Fin 2) (Fin 2) F) * X * ((k⁻¹ : G) : Matrix (Fin 2) (Fin 2) F) - 1) i j) ≤
        WithZero.exp (-(n : ℤ)) := by
    intro X hX i j
    have hkk : (k : Matrix (Fin 2) (Fin 2) F) * ((k⁻¹ : G) : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
    have : (k : Matrix (Fin 2) (Fin 2) F) * X * ((k⁻¹ : G) : Matrix (Fin 2) (Fin 2) F) - 1 =
        (k : Matrix (Fin 2) (Fin 2) F) * (X - 1) * ((k⁻¹ : G) : Matrix (Fin 2) (Fin 2) F) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hkk]
    rw [this]
    have h1 := v_mul_apply_le p hk.1 hX
    have h2 := v_mul_apply_le p h1 hk.2 i j
    simpa using h2
  constructor
  · simpa [Matrix.GeneralLinearGroup.coe_mul] using key _ hg.1
  · have : (k * g * k⁻¹)⁻¹ = k * g⁻¹ * k⁻¹ := by group
    rw [this]
    simpa [Matrix.GeneralLinearGroup.coe_mul] using key _ hg.2

theorem finite_quotient_Kc {n m : ℕ} (h : n ≤ m) :
    Finite (Kc p n ⧸ (Kc p m).subgroupOf (Kc p n)) := by
  haveI : CompactSpace (Kc p n) := isCompact_iff_compactSpace.mp (isCompact_Kc p n)
  exact Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen (Kc p n) (Kc p m) (isOpen_Kc p m))

theorem unipotent_inv (t : F) : (unipotent t : G)⁻¹ = unipotent (-t) :=
  inv_eq_of_mul_eq_one_right (by rw [unipotent_add, add_neg_cancel, unipotent_zero])

theorem lowerUni_zero : lowerUni p 0 = 1 :=
  Units.ext (by simp [lowerUni_coe, Matrix.one_fin_two])

theorem lowerUni_inv (c : F) : (lowerUni p c)⁻¹ = lowerUni p (-c) :=
  inv_eq_of_mul_eq_one_right (by rw [lowerUni_add, add_neg_cancel, lowerUni_zero])

theorem diagU_inv_coe (a d : (p.adicCompletion ℚ)ˣ) :
    (((diagU p a d)⁻¹ : G) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.diagonal ![((a⁻¹ : (p.adicCompletion ℚ)ˣ) : F), ((d⁻¹ : (p.adicCompletion ℚ)ˣ) : F)] := rfl

theorem weyl_mul_weyl : weyl p * weyl p = 1 :=
  Units.ext (by simp [weyl_coe, Matrix.one_fin_two, Matrix.mul_fin_two])

theorem weyl_inv : (weyl p)⁻¹ = weyl p := inv_eq_of_mul_eq_one_right (weyl_mul_weyl p)

theorem unipotent_mem_Kc {n : ℕ} {t : F} (ht : 𝕧 t ≤ WithZero.exp (-(n : ℤ))) : (unipotent t : G) ∈ Kc p n := by
  rw [mem_Kc_iff, unipotent_inv, unipotent_coe, unipotent_coe]
  refine ⟨?_, ?_⟩ <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    first | (simp [Matrix.one_fin_two]; done) | simpa [Matrix.one_fin_two] using ht

theorem lowerUni_mem_Kc {n : ℕ} {c : F} (hc : 𝕧 c ≤ WithZero.exp (-(n : ℤ))) : lowerUni p c ∈ Kc p n := by
  rw [mem_Kc_iff, lowerUni_inv, lowerUni_coe, lowerUni_coe]
  refine ⟨?_, ?_⟩ <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    first | (simp [Matrix.one_fin_two]; done) | simpa [Matrix.one_fin_two] using hc

theorem diagU_mem_Kc {n : ℕ} (hn : 1 ≤ n) {a d : (p.adicCompletion ℚ)ˣ} (ha : 𝕧 ((a : F) - 1) ≤ WithZero.exp (-(n : ℤ)))
    (hd : 𝕧 ((d : F) - 1) ≤ WithZero.exp (-(n : ℤ))) : diagU p a d ∈ Kc p n := by
  have he1 : WithZero.exp (-(n : ℤ)) < 1 := by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega

  have hinv : ∀ x : (p.adicCompletion ℚ)ˣ, 𝕧 ((x : F) - 1) ≤ WithZero.exp (-(n : ℤ)) →
      𝕧 (((x⁻¹ : (p.adicCompletion ℚ)ˣ) : F) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
    intro x hx
    have hx1 : 𝕧 (x : F) = 1 := by
      have := Valuation.map_one_add_of_lt Valued.v (lt_of_le_of_lt hx he1)
      simpa using this
    have : ((x⁻¹ : (p.adicCompletion ℚ)ˣ) : F) - 1 = -((x : F)⁻¹ * ((x : F) - 1)) := by
      rw [Units.val_inv_eq_inv_val]; field_simp; ring
    rw [this, Valuation.map_neg, Valuation.map_mul, map_inv₀, hx1, inv_one, one_mul]
    exact hx
  have ha' := hinv a ha
  have hd' := hinv d hd
  rw [mem_Kc_iff, diagU_coe, diagU_inv_coe]
  refine ⟨?_, ?_⟩ <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    first
    | (simp [Matrix.one_fin_two, Matrix.diagonal]; done)
    | simpa [Matrix.one_fin_two, Matrix.diagonal] using ha
    | simpa [Matrix.one_fin_two, Matrix.diagonal] using hd
    | simpa [Matrix.one_fin_two, Matrix.diagonal] using ha'
    | simpa [Matrix.one_fin_two, Matrix.diagonal] using hd'

theorem diagU_mem_Kc_zero {a d : (p.adicCompletion ℚ)ˣ} (ha : 𝕧 (a : F) = 1) (hd : 𝕧 (d : F) = 1) :
    diagU p a d ∈ Kc p 0 := by
  rw [mem_Kc_zero_iff, diagU_coe, diagU_inv_coe]
  refine ⟨?_, ?_⟩ <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Units.val_inv_eq_inv_val, map_inv₀, ha, hd]

theorem weyl_mem_Kc_zero : weyl p ∈ Kc p 0 := by
  rw [mem_Kc_zero_iff, weyl_inv, weyl_coe]
  refine ⟨?_, ?_⟩ <;> intro i j <;> fin_cases i <;> fin_cases j <;> simp

theorem coe_unipotent_mul_diagU_mul_lowerUni (t c : F) (a d : (p.adicCompletion ℚ)ˣ) :
    ((unipotent t * diagU p a d * lowerUni p c : G) : Matrix (Fin 2) (Fin 2) F) =
      !![(a : F) + t * d * c, t * d; (d : F) * c, d] := by
  simp only [Units.val_mul, unipotent_coe, diagU_coe, lowerUni_coe]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp

theorem iwahori {n : ℕ} (hn : 1 ≤ n) {k : G} (hk : k ∈ Kc p n) :
    ∃ (β c : F) (a d : (p.adicCompletion ℚ)ˣ),
      𝕧 β ≤ WithZero.exp (-(n : ℤ)) ∧ 𝕧 c ≤ WithZero.exp (-(n : ℤ)) ∧
      𝕧 ((a : F) - 1) ≤ WithZero.exp (-(n : ℤ)) ∧ 𝕧 ((d : F) - 1) ≤ WithZero.exp (-(n : ℤ)) ∧
      k = unipotent β * diagU p a d * lowerUni p c := by
  have he1 : WithZero.exp (-(n : ℤ)) < 1 := by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  rw [mem_Kc_iff] at hk
  obtain ⟨hk1, -⟩ := hk
  set m : Matrix (Fin 2) (Fin 2) F := (k : Matrix (Fin 2) (Fin 2) F) with hm
  have h00 : 𝕧 (m 0 0 - 1) ≤ WithZero.exp (-(n : ℤ)) := by simpa [Matrix.one_fin_two] using hk1 0 0
  have h01 : 𝕧 (m 0 1) ≤ WithZero.exp (-(n : ℤ)) := by simpa [Matrix.one_fin_two] using hk1 0 1
  have h10 : 𝕧 (m 1 0) ≤ WithZero.exp (-(n : ℤ)) := by simpa [Matrix.one_fin_two] using hk1 1 0
  have h11 : 𝕧 (m 1 1 - 1) ≤ WithZero.exp (-(n : ℤ)) := by simpa [Matrix.one_fin_two] using hk1 1 1
  have hv11 : 𝕧 (m 1 1) = 1 := by
    have := Valuation.map_one_add_of_lt Valued.v (lt_of_le_of_lt h11 he1)
    simpa using this
  have hd0 : m 1 1 ≠ 0 := by
    intro h; rw [h, map_zero] at hv11; exact zero_ne_one hv11
  have hdet : m.det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero k
  have ha0 : m.det / m 1 1 ≠ 0 := div_ne_zero hdet hd0
  refine ⟨m 0 1 / m 1 1, m 1 0 / m 1 1, Units.mk0 _ ha0, Units.mk0 _ hd0, ?_, ?_, ?_, ?_, ?_⟩
  · rw [map_div₀, hv11, div_one]; exact h01
  · rw [map_div₀, hv11, div_one]; exact h10
  · have : m.det / m 1 1 - 1 = (m 0 0 - 1) - m 0 1 * (m 1 0 / m 1 1) := by
      rw [Matrix.det_fin_two]; field_simp; ring
    rw [Units.val_mk0, this]
    refine Valuation.map_sub_le _ h00 ?_
    rw [Valuation.map_mul, map_div₀, hv11, div_one]
    calc 𝕧 (m 0 1) * 𝕧 (m 1 0) ≤ WithZero.exp (-(n : ℤ)) * WithZero.exp (-(n : ℤ)) := mul_le_mul' h01 h10
      _ ≤ WithZero.exp (-(n : ℤ)) * 1 := mul_le_mul_right he1.le _
      _ = _ := mul_one _
  · rw [Units.val_mk0]; exact h11
  · apply Units.ext
    change m = _
    rw [coe_unipotent_mul_diagU_mul_lowerUni, Units.val_mk0, Units.val_mk0]
    have hdet2 : m.det = m 0 0 * m 1 1 - m 0 1 * m 1 0 := Matrix.det_fin_two m
    ext i j
    fin_cases i <;> fin_cases j
    · simp [hd0]
      field_simp
      linear_combination -hdet2
    · simp [hd0]
    · rw [mul_div_cancel₀ _ hd0]; simp
    · simp

private theorem iwasawa_of_le (g : G)
    (h : 𝕧 ((g : Matrix (Fin 2) (Fin 2) F) 1 0) ≤ 𝕧 ((g : Matrix (Fin 2) (Fin 2) F) 1 1)) :
    ∃ (t : F) (a d : (p.adicCompletion ℚ)ˣ) (k : G), k ∈ Kc p 0 ∧ g = unipotent t * diagU p a d * k := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 - (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
    rw [← Matrix.det_fin_two]
    exact Matrix.GeneralLinearGroup.det_ne_zero g
  have hδ : (g : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    intro h0
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at h
    apply hdet
    rw [h0, h]
    ring
  refine ⟨(g : Matrix (Fin 2) (Fin 2) F) 0 1 / (g : Matrix (Fin 2) (Fin 2) F) 1 1, Units.mk0 _ (div_ne_zero hdet hδ), Units.mk0 _ hδ,
    lowerUni p ((g : Matrix (Fin 2) (Fin 2) F) 1 0 / (g : Matrix (Fin 2) (Fin 2) F) 1 1), ?_, ?_⟩
  · apply lowerUni_mem_Kc
    rw [map_div₀, Nat.cast_zero, neg_zero, WithZero.exp_zero]
    exact div_le_one_of_le₀ h zero_le'
  · refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [coe_unipotent_mul_diagU_mul_lowerUni, Units.val_mk0, Units.val_mk0]
    fin_cases i <;> fin_cases j <;> simp <;> field_simp
    ring

theorem iwasawa (g : G) :
    ∃ (t : F) (a d : (p.adicCompletion ℚ)ˣ) (k : G), k ∈ Kc p 0 ∧ g = unipotent t * diagU p a d * k := by
  rcases le_total (𝕧 ((g : Matrix (Fin 2) (Fin 2) F) 1 0)) (𝕧 ((g : Matrix (Fin 2) (Fin 2) F) 1 1)) with h | h
  · exact iwasawa_of_le p g h
  ·
    have h' : 𝕧 (((g * weyl p : G) : Matrix (Fin 2) (Fin 2) F) 1 0) ≤
        𝕧 (((g * weyl p : G) : Matrix (Fin 2) (Fin 2) F) 1 1) := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, weyl_coe] using h
    obtain ⟨t, a, d, k, hk, hgw⟩ := iwasawa_of_le p (g * weyl p) h'
    refine ⟨t, a, d, k * (weyl p)⁻¹, (Kc p 0).mul_mem hk ((Kc p 0).inv_mem (weyl_mem_Kc_zero p)), ?_⟩
    rw [← mul_assoc, ← hgw, mul_inv_cancel_right]

theorem exists_uniformizer : ∃ ϖ : (p.adicCompletion ℚ)ˣ, 𝕧 (ϖ : F) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨x, hx⟩ := C_exists_val_eq p (WithZero.exp (-1 : ℤ))
  have hx0 : x ≠ 0 := by
    intro h; rw [h, map_zero] at hx; exact WithZero.exp_ne_zero hx.symm
  exact ⟨Units.mk0 x hx0, hx⟩

theorem exists_eq_unit_mul_zpow {ϖ : (p.adicCompletion ℚ)ˣ} (hϖ : 𝕧 (ϖ : F) = WithZero.exp (-1 : ℤ))
    (y : (p.adicCompletion ℚ)ˣ) : ∃ (u : (p.adicCompletion ℚ)ˣ) (j : ℤ), 𝕧 (u : F) = 1 ∧ y = u * ϖ ^ j := by
  have hy : 𝕧 (y : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  set k : ℤ := WithZero.log (𝕧 (y : F)) with hk
  have hyk : 𝕧 (y : F) = WithZero.exp k := (WithZero.exp_log hy).symm
  refine ⟨y * ϖ ^ k, -k, ?_, ?_⟩
  · rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hϖ, hyk, ← WithZero.exp_zsmul,
      ← WithZero.exp_add, WithZero.exp_eq_one]
    simp
  · rw [mul_assoc, ← zpow_add]; simp

theorem diagU_inv (a d : (p.adicCompletion ℚ)ˣ) : (diagU p a d)⁻¹ = diagU p a⁻¹ d⁻¹ :=
  Units.ext rfl

theorem diagU_inv_mul_lowerUni_mul_diagU (ϖ : (p.adicCompletion ℚ)ˣ) (c : F) :
    (diagU p ϖ 1)⁻¹ * lowerUni p c * diagU p ϖ 1 = lowerUni p (c * (ϖ : F)) := by
  rw [diagU_inv]
  exact Matrix.GeneralLinearGroup.ext fun i j => by
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, lowerUni_coe, diagU_coe, Matrix.diagonal]

theorem diagU_mul_unipotent_mul_diagU_inv (ϖ : (p.adicCompletion ℚ)ˣ) (t : F) :
    diagU p ϖ 1 * unipotent t * (diagU p ϖ 1)⁻¹ = unipotent ((ϖ : F) * t) := by
  rw [diagU_inv]
  exact Matrix.GeneralLinearGroup.ext fun i j => by
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, unipotent_coe, diagU_coe, Matrix.diagonal]

end KirillovJ

end

set_option autoImplicit false

open IsDedekindDomain NumberField UnramifiedWhittaker
open scoped Matrix

noncomputable section

namespace KirillovJ

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ
local notation "G" => GL (Fin 2) (p.adicCompletion ℚ)

def rt (h : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun W := fun g => W (g * h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem rt_apply (h : G) (W : G → ℂ) (g : G) : rt p h W g = W (g * h) := rfl

theorem rt_mul (h₁ h₂ : G) (W : G → ℂ) : rt p h₁ (rt p h₂ W) = rt p (h₁ * h₂) W := by
  ext g; simp [mul_assoc]

@[scoped simp] theorem rt_one (W : G → ℂ) : rt p 1 W = W := by
  ext g; simp

def VN (V : Submodule ℂ (G → ℂ)) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ {f : G → ℂ | ∃ W' ∈ V, ∃ t : F, f = fun g => W' (g * unipotent t) - W' g}

def fixedIn (V : Submodule ℂ (G → ℂ)) (U : Subgroup G) : Submodule ℂ (G → ℂ) where
  carrier := {W | W ∈ V ∧ ∀ k ∈ U, rt p k W = W}
  zero_mem' := ⟨V.zero_mem, fun k _ => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨V.add_mem ha hb, fun k hk => by rw [map_add, ha' k hk, hb' k hk]⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    exact ⟨V.smul_mem c ha, fun k hk => by rw [map_smul, ha' k hk]⟩

theorem mem_fixedIn_iff (V : Submodule ℂ (G → ℂ)) (U : Subgroup G) (W : G → ℂ) :
    W ∈ fixedIn p V U ↔ W ∈ V ∧ ∀ k ∈ U, rt p k W = W := Iff.rfl

theorem fixedIn_le (V : Submodule ℂ (G → ℂ)) (U : Subgroup G) : fixedIn p V U ≤ V := fun _ h => h.1

theorem rt_mem (V : Submodule ℂ (G → ℂ)) (hstab : ∀ W ∈ V, ∀ h : G, (fun g => W (g * h)) ∈ V)
    (h : G) {W : G → ℂ} (hW : W ∈ V) : rt p h W ∈ V := hstab W hW h

theorem VN_le (V : Submodule ℂ (G → ℂ)) (hstab : ∀ W ∈ V, ∀ h : G, (fun g => W (g * h)) ∈ V) :
    VN p V ≤ V := by
  refine Submodule.span_le.mpr ?_
  rintro f ⟨W', hW', t, rfl⟩
  exact V.sub_mem (hstab W' hW' _) hW'

theorem rt_unipotent_sub_mem_VN (V : Submodule ℂ (G → ℂ)) (t : F) {W : G → ℂ} (hW : W ∈ V) :
    rt p (unipotent t) W - W ∈ VN p V :=
  Submodule.subset_span ⟨W, hW, t, rfl⟩

theorem rt_VN_le_of_conj (V : Submodule ℂ (G → ℂ)) (hstab : ∀ W ∈ V, ∀ h : G, (fun g => W (g * h)) ∈ V)
    (h : G) (φ : F → F) (hφ : ∀ t : F, h * unipotent t * h⁻¹ = unipotent (φ t)) :
    (VN p V).map (rt p h) ≤ VN p V := by
  rw [Submodule.map_le_iff_le_comap, VN, Submodule.span_le]
  rintro f ⟨W', hW', t, rfl⟩
  simp only [Set.mem_preimage, SetLike.mem_coe, Submodule.mem_comap]
  have hmul : h * unipotent t = unipotent (φ t) * h := by
    rw [← hφ t]; group
  have : rt p h ((fun g => W' (g * unipotent t)) - W') = (fun g => (rt p h W') (g * unipotent (φ t))) - rt p h W' := by
    ext g
    simp only [rt_apply, Pi.sub_apply, mul_assoc, hmul]
  rw [show (fun g => W' (g * unipotent t) - W' g) = (fun g => W' (g * unipotent t)) - W' from rfl, this]
  exact Submodule.subset_span ⟨rt p h W', hstab W' hW' h, φ t, rfl⟩

theorem exists_average {Kn Km : Subgroup G} (hle : Km ≤ Kn) [Finite (Kn ⧸ Km.subgroupOf Kn)]
    (V : Submodule ℂ (G → ℂ)) (hstab : ∀ W ∈ V, ∀ h : G, (fun g => W (g * h)) ∈ V)
    {u : G → ℂ} (hu : u ∈ V) (hfix : ∀ k ∈ Km, rt p k u = u) :
    ∃ (Pu : G → ℂ) (R : Finset G), (↑R : Set G) ⊆ Kn ∧ R.card = Nat.card (Kn ⧸ Km.subgroupOf Kn) ∧
      Pu = ∑ k ∈ R, rt p k u ∧ Pu ∈ V ∧ ∀ k ∈ Kn, rt p k Pu = Pu := by
  classical
  haveI : Fintype (Kn ⧸ Km.subgroupOf Kn) := Fintype.ofFinite _

  let s : Kn ⧸ Km.subgroupOf Kn → Kn := fun q => Quotient.out q
  have hs : ∀ q : Kn ⧸ Km.subgroupOf Kn, (QuotientGroup.mk (s q) : Kn ⧸ Km.subgroupOf Kn) = q :=
    fun q => Quotient.out_eq q

  let φ : Kn → (G → ℂ) := fun k => rt p (k : G) u
  have hφ : ∀ a b : Kn, (QuotientGroup.mk a : Kn ⧸ Km.subgroupOf Kn) = QuotientGroup.mk b → φ a = φ b := by
    intro a b hab
    rw [QuotientGroup.eq] at hab
    have hmem : ((a : G)⁻¹ * b) ∈ Km := by simpa [Subgroup.mem_subgroupOf] using hab
    have : (b : G) = a * ((a : G)⁻¹ * b) := by group
    simp only [φ]
    rw [this, ← rt_mul, hfix _ hmem]
  let ψ : Kn ⧸ Km.subgroupOf Kn → (G → ℂ) := Quotient.lift φ (fun a b hab => hφ a b (Quotient.sound hab))
  have hψ : ∀ k : Kn, ψ (QuotientGroup.mk k) = φ k := fun k => rfl
  have hsinj : Function.Injective s := fun a b h => by rw [← hs a, ← hs b, h]
  have hinj : Function.Injective (fun q : Kn ⧸ Km.subgroupOf Kn => ((s q : Kn) : G)) :=
    fun a b h => hsinj (Subtype.val_injective h)
  refine ⟨∑ q : Kn ⧸ Km.subgroupOf Kn, ψ q, Finset.univ.image (fun q => ((s q : Kn) : G)), ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨q, rfl⟩ := hx
    exact (s q).2
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Nat.card_eq_fintype_card]
  · rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    conv_lhs => rw [← hs q]
    rfl
  · exact Submodule.sum_mem _ (fun q _ => by
      induction q using Quotient.inductionOn with
      | h k => exact hstab u hu _)
  · intro k hk
    rw [map_sum]
    let kk : Kn := ⟨k, hk⟩
    let σ : Equiv.Perm (Kn ⧸ Km.subgroupOf Kn) := MulAction.toPerm kk
    have hσ : ∀ q : Kn ⧸ Km.subgroupOf Kn, rt p k (ψ q) = ψ (σ q) := by
      intro q
      induction q using Quotient.inductionOn with
      | h a =>
        change rt p k (φ a) = ψ (QuotientGroup.mk (kk * a))
        rw [hψ]
        simp only [φ, Subgroup.coe_mul, rt_mul]
        rfl
    simp_rw [hσ]
    exact Fintype.sum_equiv σ _ _ (fun q => rfl)

end KirillovJ
p2m_reactivate "P2MW.S_AutomorphicForm_WhittakerModel_exists_finset_span_mod_unipotentCoinvariants_of_irreducible_admissible.KirillovJ"

end
p2m_reactivate "P2MW.S_AutomorphicForm_WhittakerModel_exists_finset_span_mod_unipotentCoinvariants_of_irreducible_admissible.KirillovJ"

set_option autoImplicit false

open IsDedekindDomain NumberField UnramifiedWhittaker
open scoped Matrix

noncomputable section

namespace KirillovJ

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ
local notation "G" => GL (Fin 2) (p.adicCompletion ℚ)
local notation "𝕧" => (Valued.v : p.adicCompletion ℚ → WithZero (Multiplicative ℤ))

theorem diagU_central (z : (p.adicCompletion ℚ)ˣ) (g : G) : diagU p z z * g = g * diagU p z z := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Units.val_mul, diagU_coe, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem diagU_comm (a d a' d' : (p.adicCompletion ℚ)ˣ) : diagU p a d * diagU p a' d' = diagU p a' d' * diagU p a d := by
  rw [diagU_mul, diagU_mul, mul_comm a, mul_comm d]

theorem diagU_conj_unipotent (a d : (p.adicCompletion ℚ)ˣ) (t : F) :
    diagU p a d * unipotent t * (diagU p a d)⁻¹ = unipotent ((a : F) * t * ((d⁻¹ : (p.adicCompletion ℚ)ˣ) : F)) := by
  rw [diagU_mul_unipotent, mul_inv_cancel_right]

theorem unipotent_conj_unipotent (s t : F) :
    (unipotent s : G) * unipotent t * (unipotent s)⁻¹ = unipotent t := by
  rw [unipotent_add, add_comm, ← unipotent_add, mul_inv_cancel_right]

theorem lowerUni_mul_diagU_unif (ϖ : (p.adicCompletion ℚ)ˣ) (c : F) :
    lowerUni p c * diagU p ϖ 1 = diagU p ϖ 1 * lowerUni p (c * (ϖ : F)) := by
  simpa using lowerUni_mul_diagU p ϖ 1 c

theorem v_mul_unif_le {ϖ : (p.adicCompletion ℚ)ˣ} (hϖ : 𝕧 (ϖ : F) = WithZero.exp (-1 : ℤ)) {n : ℕ} {c : F}
    (hc : 𝕧 c ≤ WithZero.exp (-(n : ℤ))) : 𝕧 (c * (ϖ : F)) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := by
  rw [map_mul, hϖ, Nat.cast_add, Nat.cast_one, neg_add, WithZero.exp_add]
  exact mul_le_mul' hc le_rfl

def diagUHom : (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ →* G where
  toFun x := diagU p x.1 x.2
  map_one' := by
    exact diagU_one p
  map_mul' := by
    intro x y
    exact (diagU_mul p x.1 x.2 y.1 y.2).symm

@[scoped simp] theorem diagUHom_apply (a d : (p.adicCompletion ℚ)ˣ) : diagUHom p (a, d) = diagU p a d := rfl

theorem diagU_decomp {ϖ : (p.adicCompletion ℚ)ˣ} (hϖ : 𝕧 (ϖ : F) = WithZero.exp (-1 : ℤ))
    (a d : (p.adicCompletion ℚ)ˣ) :
    ∃ (u₁ u₂ : (p.adicCompletion ℚ)ˣ) (i j : ℤ), 𝕧 (u₁ : F) = 1 ∧ 𝕧 (u₂ : F) = 1 ∧
      diagU p a d = diagU p u₁ u₂ * (diagU p ϖ ϖ) ^ j * (diagU p ϖ 1) ^ (i - j) := by
  obtain ⟨u₁, i, hu₁, ha⟩ := exists_eq_unit_mul_zpow p hϖ a
  obtain ⟨u₂, j, hu₂, hd⟩ := exists_eq_unit_mul_zpow p hϖ d
  refine ⟨u₁, u₂, i, j, hu₁, hu₂, ?_⟩

  simp only [← diagUHom_apply, ← map_zpow, ← map_mul]
  congr 1
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_mul, Prod.pow_fst]
    rw [ha, mul_assoc, ← zpow_add, add_sub_cancel]
  · simp only [Prod.snd_mul, Prod.pow_snd, one_zpow, mul_one]
    exact hd

end KirillovJ
p2m_reactivate "P2MW.S_AutomorphicForm_WhittakerModel_exists_finset_span_mod_unipotentCoinvariants_of_irreducible_admissible.KirillovJ"

end
p2m_reactivate "P2MW.S_AutomorphicForm_WhittakerModel_exists_finset_span_mod_unipotentCoinvariants_of_irreducible_admissible.KirillovJ"

set_option autoImplicit false

namespace KirillovJ

theorem exists_finset_span_eq_of_le_span {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (N : Submodule K V) (B : Finset V) (h : N ≤ Submodule.span K (B : Set V)) :
    ∃ S : Finset V, (↑S : Set V) ⊆ N ∧ Submodule.span K (S : Set V) = N := by
  haveI : FiniteDimensional K N := Submodule.finiteDimensional_of_le h
  obtain ⟨S, hS⟩ := (Submodule.FG.of_finite : N.FG)
  refine ⟨S, ?_, hS⟩
  rw [← hS]
  exact Submodule.subset_span

theorem finiteDimensional_of_le_span_finset {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (N : Submodule K V) (B : Finset V) (h : N ≤ Submodule.span K (B : Set V)) :
    FiniteDimensional K N := by
  exact Submodule.finiteDimensional_of_le h

theorem le_map_of_map_le_of_injective {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : V →ₗ[K] V) (hf : Function.Injective f) (L : Submodule K V) [FiniteDimensional K L]
    (h : L.map f ≤ L) : L ≤ L.map f := by
  intro y hy
  let g : L →ₗ[K] L := (f.domRestrict L).codRestrict L (fun x => h (Submodule.mem_map_of_mem x.2))
  have hg : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    apply hf
    simpa [g] using congrArg Subtype.val hab
  obtain ⟨x, hx⟩ := LinearMap.surjective_of_injective hg ⟨y, hy⟩
  exact Submodule.mem_map.mpr ⟨x, x.2, by simpa [g] using congrArg Subtype.val hx⟩

theorem exists_sub_sum_smul_of_mem_sup_span {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (S : Finset V) (P : Submodule K V) {x : V} (hx : x ∈ Submodule.span K (S : Set V) ⊔ P) :
    ∃ c : V → K, (x - ∑ s ∈ S, c s • s) ∈ P := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp hy
  refine ⟨c, ?_⟩
  rw [hc, add_sub_cancel_left]
  exact hz

end KirillovJ
p2m_reactivate "P2MW.S_AutomorphicForm_WhittakerModel_exists_finset_span_mod_unipotentCoinvariants_of_irreducible_admissible.KirillovJ"

set_option autoImplicit false

open IsDedekindDomain NumberField UnramifiedWhittaker
open scoped Matrix

noncomputable section

namespace KirillovJ

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ
local notation "G" => GL (Fin 2) (p.adicCompletion ℚ)
local notation "𝕧" => (Valued.v : p.adicCompletion ℚ → WithZero (Multiplicative ℤ))

def Mn (V : Submodule ℂ (G → ℂ)) (n : ℕ) : Submodule ℂ (G → ℂ) := fixedIn p V (Kc p n) ⊔ VN p V

theorem fixedIn_le_Mn (V : Submodule ℂ (G → ℂ)) (n : ℕ) : fixedIn p V (Kc p n) ≤ Mn p V n := le_sup_left
theorem VN_le_Mn (V : Submodule ℂ (G → ℂ)) (n : ℕ) : VN p V ≤ Mn p V n := le_sup_right

theorem Mn_le (V : Submodule ℂ (G → ℂ)) (hstab : ∀ W ∈ V, ∀ h : G, (fun g => W (g * h)) ∈ V) (n : ℕ) :
    Mn p V n ≤ V :=
  sup_le (fixedIn_le p V _) (VN_le p V hstab)

theorem rt_unipotent_mem_Mn (V : Submodule ℂ (G → ℂ)) (hstab : ∀ W ∈ V, ∀ h : G, (fun g => W (g * h)) ∈ V)
    (n : ℕ) (s : F) {x : G → ℂ} (hx : x ∈ Mn p V n) : rt p (unipotent s) x ∈ Mn p V n := by
  have hxV : x ∈ V := Mn_le p V hstab n hx
  have : rt p (unipotent s) x = x + (rt p (unipotent s) x - x) := by abel
  rw [this]
  exact (Mn p V n).add_mem hx (VN_le_Mn p V n (rt_unipotent_sub_mem_VN p V s hxV))

theorem rt_mem_fixedIn_of_conj (V : Submodule ℂ (G → ℂ)) (hstab : ∀ W ∈ V, ∀ h : G, (fun g => W (g * h)) ∈ V)
    (n : ℕ) {h : G} (hK : ∀ k ∈ Kc p n, h⁻¹ * k * h ∈ Kc p n) {y : G → ℂ} (hy : y ∈ fixedIn p V (Kc p n)) :
    rt p h y ∈ fixedIn p V (Kc p n) := by
  refine ⟨hstab y hy.1 h, fun k hk => ?_⟩
  have : k * h = h * (h⁻¹ * k * h) := by group
  rw [rt_mul, this, ← rt_mul, hy.2 _ (hK k hk)]

theorem rt_mem_fixedIn_of_mem_Kc_zero (V : Submodule ℂ (G → ℂ))
    (hstab : ∀ W ∈ V, ∀ h : G, (fun g => W (g * h)) ∈ V)
    (n : ℕ) {k : G} (hk : k ∈ Kc p 0) {y : G → ℂ} (hy : y ∈ fixedIn p V (Kc p n)) :
    rt p k y ∈ fixedIn p V (Kc p n) := by
  refine rt_mem_fixedIn_of_conj p V hstab n (fun k' hk' => ?_) hy
  have := conj_mem_Kc p ((Kc p 0).inv_mem hk) hk'
  simpa using this

theorem rt_mem_Mn_of_conj (V : Submodule ℂ (G → ℂ)) (hstab : ∀ W ∈ V, ∀ h : G, (fun g => W (g * h)) ∈ V)
    (n : ℕ) {h : G} (hK : ∀ k ∈ Kc p n, h⁻¹ * k * h ∈ Kc p n)
    (φ : F → F) (hφ : ∀ t : F, h * unipotent t * h⁻¹ = unipotent (φ t))
    {x : G → ℂ} (hx : x ∈ Mn p V n) : rt p h x ∈ Mn p V n := by
  rw [Mn, Submodule.mem_sup] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  rw [map_add]
  refine (Mn p V n).add_mem (fixedIn_le_Mn p V n (rt_mem_fixedIn_of_conj p V hstab n hK hy))
    (VN_le_Mn p V n ?_)
  exact rt_VN_le_of_conj p V hstab h φ hφ (Submodule.mem_map_of_mem hz)

theorem rt_diagU_unit_mem_Mn (V : Submodule ℂ (G → ℂ)) (hstab : ∀ W ∈ V, ∀ h : G, (fun g => W (g * h)) ∈ V)
    (n : ℕ) {u₁ u₂ : (p.adicCompletion ℚ)ˣ} (h1 : 𝕧 (u₁ : F) = 1) (h2 : 𝕧 (u₂ : F) = 1)
    {x : G → ℂ} (hx : x ∈ Mn p V n) : rt p (diagU p u₁ u₂) x ∈ Mn p V n := by
  refine rt_mem_Mn_of_conj p V hstab n (fun k hk => ?_) _ (diagU_conj_unipotent p u₁ u₂) hx
  have hmem : (diagU p u₁ u₂)⁻¹ ∈ Kc p 0 := (Kc p 0).inv_mem (diagU_mem_Kc_zero p h1 h2)
  have := conj_mem_Kc p hmem hk
  simpa using this

theorem rt_diagU_central_mem_Mn (V : Submodule ℂ (G → ℂ)) (hstab : ∀ W ∈ V, ∀ h : G, (fun g => W (g * h)) ∈ V)
    (n : ℕ) (z : (p.adicCompletion ℚ)ˣ) {x : G → ℂ} (hx : x ∈ Mn p V n) : rt p (diagU p z z) x ∈ Mn p V n := by
  refine rt_mem_Mn_of_conj p V hstab n (fun k hk => ?_) id (fun t => ?_) hx
  · have : (diagU p z z)⁻¹ * k * diagU p z z = k := by
      rw [mul_assoc, ← diagU_central p z k, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]; exact hk
  · rw [diagU_central p z (unipotent t), mul_assoc, mul_inv_cancel, mul_one]; rfl

theorem rt_A_mem_Mn_of_mem_fixedIn (V : Submodule ℂ (G → ℂ))
    (hstab : ∀ W ∈ V, ∀ h : G, (fun g => W (g * h)) ∈ V)
    (hsm : ∀ W ∈ V, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, W (g * k) = W g)
    {n : ℕ} (hn : 1 ≤ n) {ϖ : (p.adicCompletion ℚ)ˣ} (hϖ : 𝕧 (ϖ : F) = WithZero.exp (-1 : ℤ))
    {y : G → ℂ} (hy : y ∈ fixedIn p V (Kc p n)) : rt p (diagU p ϖ 1) y ∈ Mn p V n := by
  classical
  set A : G := diagU p ϖ 1 with hA
  set u := rt p A y with hu
  have huV : u ∈ V := hstab y hy.1 A
  obtain ⟨U, hUo, hU⟩ := hsm u huV
  obtain ⟨m', -, hm'⟩ := exists_Kc_le_of_isOpen p U hUo
  set m := max m' n with hm
  have hnm : n ≤ m := le_max_right _ _
  have hfix : ∀ k ∈ Kc p m, rt p k u = u := fun k hk =>
    funext fun g => hU k (hm' (Kc_antitone p (le_max_left m' n) hk)) g
  haveI := finite_quotient_Kc p hnm
  obtain ⟨Pu, R, hR, hcard, hPu, hPuV, hPufix⟩ := exists_average p (Kc_antitone p hnm) V hstab huV hfix

  have hkey : ∀ k ∈ Kc p n, rt p k u - u ∈ VN p V := by
    intro k hk
    obtain ⟨β, c, a, d, hβ, hc, ha, hd, rfl⟩ := iwahori p hn hk
    have h1 : unipotent β * diagU p a d * lowerUni p c * A =
        unipotent β * A * (diagU p a d * lowerUni p (c * (ϖ : F))) := by
      rw [hA, mul_assoc (unipotent β * diagU p a d), lowerUni_mul_diagU_unif, ← mul_assoc, ← mul_assoc,
        mul_assoc (unipotent β), diagU_comm p a d ϖ 1, ← mul_assoc, mul_assoc]
    have hL : lowerUni p (c * (ϖ : F)) ∈ Kc p n :=
      Kc_antitone p (Nat.le_succ n) (lowerUni_mem_Kc p (v_mul_unif_le p hϖ hc))
    have hD : diagU p a d ∈ Kc p n := diagU_mem_Kc p hn ha hd
    have : rt p (unipotent β * diagU p a d * lowerUni p c) u = rt p (unipotent β) u := by
      rw [hu, rt_mul, h1, ← rt_mul, ← rt_mul, ← rt_mul (p := p) (diagU p a d), hy.2 _ hL, hy.2 _ hD]
    rw [this]
    exact rt_unipotent_sub_mem_VN p V β huV

  have hdiff : Pu - (R.card : ℂ) • u ∈ VN p V := by
    have : Pu - (R.card : ℂ) • u = ∑ k ∈ R, (rt p k u - u) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, hPu]
    rw [this]
    exact Submodule.sum_mem _ (fun k hk => hkey k (hR hk))
  have hcard0 : (R.card : ℂ) ≠ 0 := by
    rw [hcard, Nat.cast_ne_zero]
    exact (Nat.card_pos (α := ↥(Kc p n) ⧸ (Kc p m).subgroupOf (Kc p n))).ne'
  have hPuM : Pu ∈ Mn p V n := fixedIn_le_Mn p V n ⟨hPuV, hPufix⟩
  have : u = (R.card : ℂ)⁻¹ • (Pu - (Pu - (R.card : ℂ) • u)) := by
    rw [sub_sub_cancel, smul_smul, inv_mul_cancel₀ hcard0, one_smul]
  rw [this]
  exact (Mn p V n).smul_mem _ ((Mn p V n).sub_mem hPuM (VN_le_Mn p V n hdiff))

theorem VN_le_comap_rt_diagU (V : Submodule ℂ (G → ℂ)) (hstab : ∀ W ∈ V, ∀ h : G, (fun g => W (g * h)) ∈ V)
    (a d : (p.adicCompletion ℚ)ˣ) : VN p V ≤ (VN p V).comap (rt p (diagU p a d)) := by
  rw [← Submodule.map_le_iff_le_comap]
  exact rt_VN_le_of_conj p V hstab _ _ (diagU_conj_unipotent p a d)

theorem mem_Mn_iff_mkQ_mem (V : Submodule ℂ (G → ℂ)) (n : ℕ) (x : G → ℂ) :
    x ∈ Mn p V n ↔ (VN p V).mkQ x ∈ (fixedIn p V (Kc p n)).map (VN p V).mkQ := by
  constructor
  · intro hx
    rw [Mn, Submodule.mem_sup] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    refine ⟨y, hy, ?_⟩
    have hz0 : (VN p V).mkQ z = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hz
    rw [map_add, hz0, add_zero]
  · rintro ⟨y, hy, hyx⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hyx
    have : x = y + -(y - x) := by abel
    rw [this]
    exact (Mn p V n).add_mem (fixedIn_le_Mn p V n hy) (VN_le_Mn p V n ((VN p V).neg_mem hyx))

theorem rt_Ainv_mem_Mn_of_mem_fixedIn (V : Submodule ℂ (G → ℂ))
    (hstab : ∀ W ∈ V, ∀ h : G, (fun g => W (g * h)) ∈ V)
    (hsm : ∀ W ∈ V, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, W (g * k) = W g)
    (hadm : ∀ U : Subgroup G, IsOpen (U : Set G) →
      ∃ B : Finset (G → ℂ), ∀ W ∈ V, (∀ k ∈ U, ∀ g : G, W (g * k) = W g) →
        W ∈ Submodule.span ℂ (B : Set (G → ℂ)))
    {n : ℕ} (hn : 1 ≤ n) {ϖ : (p.adicCompletion ℚ)ˣ} (hϖ : 𝕧 (ϖ : F) = WithZero.exp (-1 : ℤ))
    {y : G → ℂ} (hy : y ∈ fixedIn p V (Kc p n)) : rt p (diagU p ϖ 1)⁻¹ y ∈ Mn p V n := by
  classical
  set A : G := diagU p ϖ 1 with hA
  set Fix := fixedIn p V (Kc p n) with hFix
  set mk := (VN p V).mkQ with hmk
  set L : Submodule ℂ ((G → ℂ) ⧸ VN p V) := Fix.map mk with hL

  obtain ⟨B, hB⟩ := hadm (Kc p n) (isOpen_Kc p n)
  have hFixle : Fix ≤ Submodule.span ℂ (B : Set (G → ℂ)) :=
    fun W hW => hB W hW.1 (fun k hk g => congrFun (hW.2 k hk) g)
  haveI : FiniteDimensional ℂ Fix := finiteDimensional_of_le_span_finset _ B hFixle
  haveI : FiniteDimensional ℂ L := inferInstance

  have hAco := VN_le_comap_rt_diagU p V hstab ϖ 1
  set barA : ((G → ℂ) ⧸ VN p V) →ₗ[ℂ] ((G → ℂ) ⧸ VN p V) := (VN p V).mapQ (VN p V) (rt p A) hAco with hbarA
  have hbarA_mk : ∀ x, barA (mk x) = mk (rt p A x) := fun x => rfl

  have hAinvVN : ∀ z ∈ VN p V, rt p A⁻¹ z ∈ VN p V := by
    intro z hz
    have := VN_le_comap_rt_diagU p V hstab ϖ⁻¹ 1⁻¹ hz
    rw [Submodule.mem_comap] at this
    rwa [hA, diagU_inv]

  have hinj : Function.Injective barA := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro q hq
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (VN p V) q
    rw [LinearMap.mem_ker, ← hmk, hbarA_mk, hmk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hq
    rw [← hmk] at *
    rw [hmk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have := hAinvVN _ hq
    rwa [rt_mul, inv_mul_cancel, rt_one] at this

  have hmap : L.map barA ≤ L := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hq
    change barA (mk x) ∈ L
    rw [hbarA_mk]
    exact (mem_Mn_iff_mkQ_mem p V n _).mp (rt_A_mem_Mn_of_mem_fixedIn p V hstab hsm hn hϖ hx)
  have hle : L ≤ L.map barA := le_map_of_map_le_of_injective barA hinj L hmap

  obtain ⟨q, hq, hqy⟩ := hle (Submodule.mem_map_of_mem (f := mk) hy : mk y ∈ L)
  obtain ⟨x, hxM⟩ : ∃ x, x ∈ Mn p V n ∧ mk x = q := by
    obtain ⟨x', hx', rfl⟩ := hq
    exact ⟨x', fixedIn_le_Mn p V n hx', rfl⟩
  obtain ⟨hxM, rfl⟩ := hxM
  rw [hbarA_mk, hmk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hqy

  have h2 := hAinvVN _ hqy
  rw [map_sub, rt_mul, inv_mul_cancel, rt_one] at h2
  have : rt p A⁻¹ y = x - (x - rt p A⁻¹ y) := by abel
  rw [this]
  exact (Mn p V n).sub_mem hxM (VN_le_Mn p V n h2)

end KirillovJ
p2m_reactivate "P2MW.S_AutomorphicForm_WhittakerModel_exists_finset_span_mod_unipotentCoinvariants_of_irreducible_admissible.KirillovJ"

end
p2m_reactivate "P2MW.S_AutomorphicForm_WhittakerModel_exists_finset_span_mod_unipotentCoinvariants_of_irreducible_admissible.KirillovJ"

set_option autoImplicit false

open IsDedekindDomain NumberField UnramifiedWhittaker
open scoped Matrix

noncomputable section

namespace KirillovJ

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ
local notation "G" => GL (Fin 2) (p.adicCompletion ℚ)
local notation "𝕧" => (Valued.v : p.adicCompletion ℚ → WithZero (Multiplicative ℤ))

def Stab (V : Submodule ℂ (G → ℂ)) (n : ℕ) : Subgroup G where
  carrier := {h | ∀ x ∈ Mn p V n, rt p h x ∈ Mn p V n ∧ rt p h⁻¹ x ∈ Mn p V n}
  one_mem' := by
    intro x hx
    simp only [inv_one, rt_one]
    exact ⟨hx, hx⟩
  mul_mem' := by
    intro a b ha hb x hx
    refine ⟨?_, ?_⟩
    · rw [← rt_mul]; exact (ha _ (hb x hx).1).1
    · rw [mul_inv_rev, ← rt_mul]; exact (hb _ (ha x hx).2).2
  inv_mem' := by
    intro a ha x hx
    rw [inv_inv]
    exact ⟨(ha x hx).2, (ha x hx).1⟩

theorem mem_Stab_iff (V : Submodule ℂ (G → ℂ)) (n : ℕ) (h : G) :
    h ∈ Stab p V n ↔ ∀ x ∈ Mn p V n, rt p h x ∈ Mn p V n ∧ rt p h⁻¹ x ∈ Mn p V n := Iff.rfl

theorem unipotent_mem_Stab (V : Submodule ℂ (G → ℂ)) (hstab : ∀ W ∈ V, ∀ h : G, (fun g => W (g * h)) ∈ V)
    (n : ℕ) (s : F) : (unipotent s : G) ∈ Stab p V n := fun x hx =>
  ⟨rt_unipotent_mem_Mn p V hstab n s hx, by rw [unipotent_inv]; exact rt_unipotent_mem_Mn p V hstab n (-s) hx⟩

theorem diagU_unit_mem_Stab (V : Submodule ℂ (G → ℂ)) (hstab : ∀ W ∈ V, ∀ h : G, (fun g => W (g * h)) ∈ V)
    (n : ℕ) {u₁ u₂ : (p.adicCompletion ℚ)ˣ} (h1 : 𝕧 (u₁ : F) = 1) (h2 : 𝕧 (u₂ : F) = 1) :
    diagU p u₁ u₂ ∈ Stab p V n := fun x hx =>
  ⟨rt_diagU_unit_mem_Mn p V hstab n h1 h2 hx, by
    rw [diagU_inv]
    refine rt_diagU_unit_mem_Mn p V hstab n ?_ ?_ hx <;>
      simp [Units.val_inv_eq_inv_val, map_inv₀, h1, h2]⟩

theorem diagU_central_mem_Stab (V : Submodule ℂ (G → ℂ)) (hstab : ∀ W ∈ V, ∀ h : G, (fun g => W (g * h)) ∈ V)
    (n : ℕ) (z : (p.adicCompletion ℚ)ˣ) : diagU p z z ∈ Stab p V n := fun x hx =>
  ⟨rt_diagU_central_mem_Mn p V hstab n z hx, by
    rw [diagU_inv]; exact rt_diagU_central_mem_Mn p V hstab n z⁻¹ hx⟩

theorem diagU_unif_mem_Stab (V : Submodule ℂ (G → ℂ))
    (hstab : ∀ W ∈ V, ∀ h : G, (fun g => W (g * h)) ∈ V)
    (hsm : ∀ W ∈ V, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, W (g * k) = W g)
    (hadm : ∀ U : Subgroup G, IsOpen (U : Set G) →
      ∃ B : Finset (G → ℂ), ∀ W ∈ V, (∀ k ∈ U, ∀ g : G, W (g * k) = W g) →
        W ∈ Submodule.span ℂ (B : Set (G → ℂ)))
    {n : ℕ} (hn : 1 ≤ n) {ϖ : (p.adicCompletion ℚ)ˣ} (hϖ : 𝕧 (ϖ : F) = WithZero.exp (-1 : ℤ)) :
    diagU p ϖ 1 ∈ Stab p V n := by
  intro x hx
  rw [Mn, Submodule.mem_sup] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  have hzA : rt p (diagU p ϖ 1) z ∈ VN p V := by
    have := VN_le_comap_rt_diagU p V hstab ϖ 1 hz
    rwa [Submodule.mem_comap] at this
  have hzAinv : rt p (diagU p ϖ 1)⁻¹ z ∈ VN p V := by
    have := VN_le_comap_rt_diagU p V hstab ϖ⁻¹ 1⁻¹ hz
    rw [Submodule.mem_comap] at this
    rwa [diagU_inv]
  refine ⟨?_, ?_⟩ <;> rw [map_add]
  · exact (Mn p V n).add_mem (rt_A_mem_Mn_of_mem_fixedIn p V hstab hsm hn hϖ hy) (VN_le_Mn p V n hzA)
  · exact (Mn p V n).add_mem (rt_Ainv_mem_Mn_of_mem_fixedIn p V hstab hsm hadm hn hϖ hy)
      (VN_le_Mn p V n hzAinv)

theorem diagU_mem_Stab (V : Submodule ℂ (G → ℂ))
    (hstab : ∀ W ∈ V, ∀ h : G, (fun g => W (g * h)) ∈ V)
    (hsm : ∀ W ∈ V, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, W (g * k) = W g)
    (hadm : ∀ U : Subgroup G, IsOpen (U : Set G) →
      ∃ B : Finset (G → ℂ), ∀ W ∈ V, (∀ k ∈ U, ∀ g : G, W (g * k) = W g) →
        W ∈ Submodule.span ℂ (B : Set (G → ℂ)))
    {n : ℕ} (hn : 1 ≤ n) {ϖ : (p.adicCompletion ℚ)ˣ} (hϖ : 𝕧 (ϖ : F) = WithZero.exp (-1 : ℤ))
    (a d : (p.adicCompletion ℚ)ˣ) : diagU p a d ∈ Stab p V n := by
  obtain ⟨u₁, u₂, i, j, hu₁, hu₂, h⟩ := diagU_decomp p hϖ a d
  rw [h]
  refine (Stab p V n).mul_mem ((Stab p V n).mul_mem ?_ ?_) ?_
  · exact diagU_unit_mem_Stab p V hstab n hu₁ hu₂
  · exact (Stab p V n).zpow_mem (diagU_central_mem_Stab p V hstab n ϖ) j
  · exact (Stab p V n).zpow_mem (diagU_unif_mem_Stab p V hstab hsm hadm hn hϖ) (i - j)

theorem main (V : Submodule ℂ (G → ℂ))
    (hstab : ∀ W ∈ V, ∀ h : G, (fun g => W (g * h)) ∈ V)
    (hsm : ∀ W ∈ V, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, W (g * k) = W g)
    (hadm : ∀ U : Subgroup G, IsOpen (U : Set G) →
      ∃ B : Finset (G → ℂ), ∀ W ∈ V, (∀ k ∈ U, ∀ g : G, W (g * k) = W g) →
        W ∈ Submodule.span ℂ (B : Set (G → ℂ)))
    (hirr : ∀ W₀ ∈ V, W₀ ≠ 0 → ∀ W ∈ V,
      W ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => W₀ (g * h))) :
    ∃ S : Finset (G → ℂ), (↑S : Set (G → ℂ)) ⊆ V ∧
      ∀ W ∈ V, ∃ c : (G → ℂ) → ℂ,
        (W - ∑ s ∈ S, c s • s) ∈ Submodule.span ℂ {f : G → ℂ | ∃ W' ∈ V, ∃ t : F, f = fun g => W' (g * unipotent t) - W' g} := by
  classical
  by_cases hV0 : ∀ W ∈ V, W = 0
  · refine ⟨∅, by simp, fun W hW => ⟨0, ?_⟩⟩
    simp [hV0 W hW]
  push_neg at hV0
  obtain ⟨W₀, hW₀, hne⟩ := hV0
  obtain ⟨U, hUo, hU⟩ := hsm W₀ hW₀
  obtain ⟨n, hn1, hnU⟩ := exists_Kc_le_of_isOpen p U hUo
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer p
  have hW₀fix : W₀ ∈ fixedIn p V (Kc p n) := ⟨hW₀, fun k hk => funext fun g => hU k (hnU hk) g⟩
  obtain ⟨B, hB⟩ := hadm (Kc p n) (isOpen_Kc p n)
  have hFixle : fixedIn p V (Kc p n) ≤ Submodule.span ℂ (B : Set (G → ℂ)) :=
    fun W hW => hB W hW.1 (fun k hk g => congrFun (hW.2 k hk) g)
  obtain ⟨S, hSsub, hSspan⟩ := exists_finset_span_eq_of_le_span _ B hFixle
  refine ⟨S, hSsub.trans (fixedIn_le p V _), fun W hW => ?_⟩
  have hWM : W ∈ Mn p V n := by
    refine (Submodule.span_le.mpr ?_) (hirr W₀ hW₀ hne W hW)
    rintro _ ⟨h, rfl⟩
    obtain ⟨t, a, d, k, hk, rfl⟩ := iwasawa p h
    change rt p (unipotent t * diagU p a d * k) W₀ ∈ Mn p V n
    rw [← rt_mul, ← rt_mul]
    refine ((unipotent_mem_Stab p V hstab n t) _ ?_).1
    refine ((diagU_mem_Stab p V hstab hsm hadm hn1 hϖ a d) _ ?_).1
    exact fixedIn_le_Mn p V n (rt_mem_fixedIn_of_mem_Kc_zero p V hstab n hk hW₀fix)
  rw [Mn, ← hSspan] at hWM
  exact exists_sub_sum_smul_of_mem_sup_span S (VN p V) hWM

end KirillovJ
p2m_reactivate "P2MW.S_AutomorphicForm_WhittakerModel_exists_finset_span_mod_unipotentCoinvariants_of_irreducible_admissible.KirillovJ"

end
p2m_reactivate "P2MW.S_AutomorphicForm_WhittakerModel_exists_finset_span_mod_unipotentCoinvariants_of_irreducible_admissible.KirillovJ"

open IsDedekindDomain NumberField UnramifiedWhittaker in

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (V : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))
    (hstab : ∀ W ∈ V, ∀ h : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * h)) ∈ V)
    (hsm : ∀ W ∈ V, ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g)
    (hadm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), ∀ W ∈ V, (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) →
        W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hirr : ∀ W₀ ∈ V, W₀ ≠ 0 → ∀ W ∈ V,
      W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h))) :
    ∃ S : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), (↑S : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)) ⊆ V ∧
      ∀ W ∈ V, ∃ c : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) → ℂ,
        (W - ∑ s ∈ S, c s • s) ∈ Submodule.span ℂ {f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ | ∃ W' ∈ V, ∃ t : p.adicCompletion ℚ, f = fun g => W' (g * unipotent t) - W' g} :=
  KirillovJ.main p V hstab hsm hadm hirr

end S_AutomorphicForm_WhittakerModel_exists_finset_span_mod_unipotentCoinvariants_of_irreducible_admissible
end P2MW
export P2MW.S_AutomorphicForm_WhittakerModel_exists_finset_span_mod_unipotentCoinvariants_of_irreducible_admissible (solution)
