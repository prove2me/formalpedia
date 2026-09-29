-- Prove2me | solution 1 for AutomorphicForm.LocalFunctionSpace.eq_zero_of_forall_apply_diagOne_eq_zero_of_irreducible_of_admissible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ee0bdaae-f5e4-50b3-8893-df15ed63cfdc

import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_RatIdele_Normalizer
import Theorems.Thm_AutomorphicForm_LocalFunctionSpace_mem_span_sub_of_apply_one_eq_zero_of_irreducible_of_admissible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_LocalFunctionSpace_eq_zero_of_forall_apply_diagOne_eq_zero_of_irreducible_of_admissible

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.longFile 0

noncomputable section

open IsDedekindDomain NumberField
open scoped WithZero Pointwise

namespace KirillovInjectivity

variable {p : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => HeightOneSpectrum.adicCompletion ℚ p
local notation "Mat" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)
local notation "ψ" => NumberField.StandardAddChar.psiV p

variable (p) in

def unif : HeightOneSpectrum.adicCompletion ℚ p :=
  algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ p) ((Rat.HeightOneSpectrum.natGenerator p : ℕ) : ℚ)

theorem v_unif : Valued.v (unif p) = WithZero.exp (-1 : ℤ) := by
  rw [unif, RatIdele.valued_algebraMap_rat, RatIdele.valuation_natGenerator]

theorem unif_ne_zero : unif p ≠ 0 := by
  intro h
  have h1 := v_unif (p := p)
  rw [h, Valuation.map_zero] at h1
  exact WithZero.exp_ne_zero h1.symm

theorem v_unif_zpow (j : ℤ) : Valued.v (unif p ^ j) = WithZero.exp (-j) := by
  rw [map_zpow₀, v_unif, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem v_unif_pow (n : ℕ) : Valued.v (unif p ^ n) = WithZero.exp (-(n : ℤ)) := by
  rw [← zpow_natCast, v_unif_zpow]

theorem psi_unif_inv_ne_one : ψ (unif p)⁻¹ ≠ 1 := by
  rw [unif, ← map_inv₀]
  exact NumberField.StandardAddChar.psiV_algebraMap_inv_ne_one p

theorem psi_eq_one_of_v_le_one {x : F} (hx : Valued.v x ≤ 1) : ψ x = 1 :=
  NumberField.StandardAddChar.psiV_eq_one_of_mem_integers p
    ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hx)

theorem psi_neg_mul_psi (x : F) : ψ (-x) * ψ x = 1 := by
  rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

theorem psi_ne_zero (x : F) : ψ x ≠ 0 := by
  intro h
  have := psi_neg_mul_psi x
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem psi_neg_ne_one {x : F} (hx : ψ x ≠ 1) : ψ (-x) ≠ 1 := by
  intro h
  have := psi_neg_mul_psi x
  rw [h, one_mul] at this
  exact hx this

theorem v_add_le {x y : F} {γ : ℤᵐ⁰} (hx : Valued.v x ≤ γ) (hy : Valued.v y ≤ γ) :
    Valued.v (x + y) ≤ γ :=
  (Valuation.map_add _ x y).trans (max_le hx hy)

theorem v_mul_le {x y : F} {a b : ℤ} (hx : Valued.v x ≤ WithZero.exp a)
    (hy : Valued.v y ≤ WithZero.exp b) : Valued.v (x * y) ≤ WithZero.exp (a + b) := by
  rw [Valuation.map_mul, WithZero.exp_add]
  exact mul_le_mul' hx hy

theorem v_ne_zero {x : F} (hx : x ≠ 0) : Valued.v x ≠ 0 := by
  rwa [ne_eq, Valuation.zero_iff]

theorem exp_succ_le_of_exp_lt {y : F} {i : ℤ} (h : WithZero.exp i < Valued.v y) :
    WithZero.exp (i + 1) ≤ Valued.v y := by
  have hy : Valued.v y ≠ 0 := (lt_of_le_of_lt zero_le' h).ne'
  rw [← WithZero.exp_log hy] at h ⊢
  rw [WithZero.exp_lt_exp] at h
  rw [WithZero.exp_le_exp]
  omega

theorem exists_v_le_exp (x : F) : ∃ j : ℤ, 0 ≤ j ∧ Valued.v x ≤ WithZero.exp j := by
  by_cases hx : Valued.v x = 0
  · exact ⟨0, le_rfl, by rw [hx]; exact zero_le'⟩
  · refine ⟨max 0 (WithZero.log (Valued.v x)), le_max_left _ _, ?_⟩
    conv_lhs => rw [← WithZero.exp_log hx]
    rw [WithZero.exp_le_exp]
    exact le_max_right _ _

theorem exists_freq {y : F} {i : ℤ} (h : ¬ Valued.v y ≤ WithZero.exp i) :
    ∃ a : F, Valued.v a ≤ WithZero.exp (-i) ∧ ψ (a * y) ≠ 1 := by
  have hlt : WithZero.exp i < Valued.v y := lt_of_not_ge h
  have hy0 : y ≠ 0 := by
    intro h0; apply h; rw [h0, Valuation.map_zero]; exact zero_le'
  have hy' : Valued.v y ≠ 0 := v_ne_zero hy0
  refine ⟨y⁻¹ * (unif p)⁻¹, ?_, ?_⟩
  · have h1 := exp_succ_le_of_exp_lt hlt
    rw [Valuation.map_mul, map_inv₀, map_inv₀, v_unif, ← WithZero.exp_neg, neg_neg]
    rw [← WithZero.exp_log hy'] at h1 ⊢
    rw [WithZero.exp_le_exp] at h1
    rw [← WithZero.exp_neg, ← WithZero.exp_add, WithZero.exp_le_exp]
    omega
  · have : y⁻¹ * (unif p)⁻¹ * y = (unif p)⁻¹ := by
      field_simp [unif_ne_zero (p := p)]
    rw [this]
    exact psi_unif_inv_ne_one

variable (p) in

def ball (j : ℤ) : AddSubgroup (HeightOneSpectrum.adicCompletion ℚ p) where
  carrier := {x | Valued.v x ≤ WithZero.exp j}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => v_add_le ha hb
  neg_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq, Valuation.map_neg] at ha ⊢
    exact ha

theorem mem_ball {j : ℤ} {x : F} : x ∈ ball p j ↔ Valued.v x ≤ WithZero.exp j := Iff.rfl

theorem ball_mono {i j : ℤ} (h : i ≤ j) : ball p i ≤ ball p j :=
  fun _ hx => hx.trans (WithZero.exp_le_exp.mpr h)

theorem zero_mem_ball (j : ℤ) : (0 : F) ∈ ball p j := (ball p j).zero_mem

theorem mul_mem_ball {i j : ℤ} {x y : F} (hx : x ∈ ball p i) (hy : y ∈ ball p j) :
    x * y ∈ ball p (i + j) :=
  v_mul_le hx hy

theorem psi_eq_one_of_mem_ball_zero {x : F} (hx : x ∈ ball p 0) : ψ x = 1 :=
  psi_eq_one_of_v_le_one (by simpa [mem_ball] using hx)

theorem psi_mul_eq_one {i j : ℤ} {x y : F} (hx : x ∈ ball p i) (hy : y ∈ ball p j) (h : i + j ≤ 0) :
    ψ (x * y) = 1 :=
  psi_eq_one_of_mem_ball_zero (ball_mono h (mul_mem_ball hx hy))

theorem isOpen_ball (j : ℤ) : IsOpen (ball p j : Set F) := by
  have hϖ0 : unif p ≠ 0 := unif_ne_zero
  have hset : (ball p j : Set F) =
      (fun x => unif p ^ j * x) ⁻¹' (p.adicCompletionIntegers ℚ : Set F) := by
    ext x
    simp only [SetLike.mem_coe, mem_ball, Set.mem_preimage,
      HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, v_unif_zpow, WithZero.exp_neg]
    constructor
    · intro h
      calc (WithZero.exp j)⁻¹ * Valued.v x ≤ (WithZero.exp j)⁻¹ * WithZero.exp j :=
            mul_le_mul_right h _
        _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
    · intro h
      calc Valued.v x = WithZero.exp j * ((WithZero.exp j)⁻¹ * Valued.v x) := by
            rw [← mul_assoc, mul_inv_cancel₀ WithZero.exp_ne_zero, one_mul]
        _ ≤ WithZero.exp j * 1 := mul_le_mul_right h _
        _ = WithZero.exp j := mul_one _
  rw [hset]
  exact (Valued.isOpen_valuationSubring _).preimage (continuous_const_mul _)

theorem isClosed_ball (j : ℤ) : IsClosed (ball p j : Set F) :=
  AddSubgroup.isClosed_of_isOpen _ (isOpen_ball j)

theorem isCompact_ball (j : ℤ) : IsCompact (ball p j : Set F) := by
  have hO : IsCompact (p.adicCompletionIntegers ℚ : Set F) :=
    isCompact_iff_compactSpace.2 (NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 ℚ) ℚ p)
  have hϖ0 : unif p ≠ 0 := unif_ne_zero
  have himg : (ball p j : Set F) = (fun x => unif p ^ (-j) * x) '' (p.adicCompletionIntegers ℚ : Set F) := by
    ext x
    simp only [SetLike.mem_coe, mem_ball, Set.mem_image, HeightOneSpectrum.mem_adicCompletionIntegers]
    constructor
    · intro hx
      refine ⟨unif p ^ j * x, ?_, ?_⟩
      · rw [Valuation.map_mul, v_unif_zpow]
        calc WithZero.exp (-j) * Valued.v x ≤ WithZero.exp (-j) * WithZero.exp j := mul_le_mul_right hx _
          _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
      · rw [← mul_assoc, ← zpow_add₀ hϖ0, neg_add_cancel, zpow_zero, one_mul]
    · rintro ⟨y, hy, rfl⟩
      rw [Valuation.map_mul, v_unif_zpow, neg_neg]
      calc WithZero.exp j * Valued.v y ≤ WithZero.exp j * 1 := mul_le_mul_right hy _
        _ = WithZero.exp j := mul_one _
  rw [himg]
  exact hO.image (continuous_const_mul _)

theorem eq_zero_of_forall_mem_ball {x : F} (h : ∀ n : ℕ, x ∈ ball p (-(n : ℤ))) : x = 0 := by
  by_contra hx
  have hx' : Valued.v x ≠ 0 := v_ne_zero hx
  set L := WithZero.log (Valued.v x)
  have hxL : Valued.v x = WithZero.exp L := (WithZero.exp_log hx').symm
  have := h ((-L).toNat + 1)
  rw [mem_ball, hxL, WithZero.exp_le_exp] at this
  omega

theorem exists_ball_subset {U : Set F} (hU : IsOpen U) (h0 : (0 : F) ∈ U) :
    ∃ n : ℕ, (ball p (-(n : ℤ)) : Set F) ⊆ U := by
  have hdir : Directed (fun x1 x2 : Set F => x1 ⊇ x2) fun n : ℕ => (ball p (-(n : ℤ)) : Set F) := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · exact fun x hx => ball_mono (by simp) hx
    · exact fun x hx => ball_mono (by simp) hx
  refine exists_subset_nhds_of_isCompact' hdir (fun n => isCompact_ball _) (fun n => isClosed_ball _) ?_
  intro x hx
  rw [Set.mem_iInter] at hx
  have : x = 0 := eq_zero_of_forall_mem_ball hx
  subst this
  exact hU.mem_nhds h0

theorem exists_ne_zero_mem_ball (j : ℤ) : ∃ y : F, y ≠ 0 ∧ y ∈ ball p j := by
  refine ⟨unif p ^ (-j).toNat, pow_ne_zero _ unif_ne_zero, ?_⟩
  rw [mem_ball, v_unif_pow, WithZero.exp_le_exp]
  omega

abbrev nU (x : HeightOneSpectrum.adicCompletion ℚ p) : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) :=
  AutomorphicForm.unipotentGL2 x

def gl2 (a b c d : F) (h : a * d - b * c ≠ 0) : G :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; c, d] (by rwa [Matrix.det_fin_two_of])

@[scoped simp] theorem gl2_coe (a b c d : F) (h : a * d - b * c ≠ 0) :
    ((gl2 a b c d h : G) : Mat) = !![a, b; c, d] := rfl

theorem nU_coe (x : F) : ((nU x : G) : Mat) = !![1, x; 0, 1] := rfl

theorem diagOne_coe (a : Fˣ) :
    ((AdelicLevel.diagOne a : G) : Mat) = !![(a : F), 0; 0, 1] := by
  ext i j
  rw [AdelicLevel.diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem gl_eq_of_entries {g h : G}
    (h00 : (g : Mat) 0 0 = (h : Mat) 0 0) (h01 : (g : Mat) 0 1 = (h : Mat) 0 1)
    (h10 : (g : Mat) 1 0 = (h : Mat) 1 0) (h11 : (g : Mat) 1 1 = (h : Mat) 1 1) : g = h := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem mul_coe_apply (g h : G) (i j : Fin 2) :
    ((g * h : G) : Mat) i j = (g : Mat) i 0 * (h : Mat) 0 j + (g : Mat) i 1 * (h : Mat) 1 j := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem nU_add (x y : F) : (nU (x + y) : G) = nU x * nU y := AutomorphicForm.unipotentGL2_add x y

theorem nU_zero : (nU (0 : F) : G) = 1 := AutomorphicForm.unipotentGL2_zero

theorem diagOne_mul_nU (a : Fˣ) (x : F) :
    (AdelicLevel.diagOne a : G) * nU x = nU ((a : F) * x) * AdelicLevel.diagOne a := by
  apply gl_eq_of_entries <;> simp [mul_coe_apply, nU_coe, diagOne_coe]

theorem nU_mul_diagOne (a : Fˣ) (x : F) :
    (nU x : G) * AdelicLevel.diagOne a = AdelicLevel.diagOne a * nU ((a : F)⁻¹ * x) := by
  rw [diagOne_mul_nU, ← mul_assoc, mul_inv_cancel₀ a.ne_zero, one_mul]

def lowU (y : F) : G := gl2 1 0 y 1 (by simp)

@[scoped simp] theorem lowU_coe (y : F) : ((lowU y : G) : Mat) = !![1, 0; y, 1] := rfl

theorem diag_mul_nU (t₁ t₂ : F) (h : t₁ * t₂ - 0 * 0 ≠ 0) (x : F) :
    gl2 t₁ 0 0 t₂ h * nU x = nU (t₁ * x * t₂⁻¹) * gl2 t₁ 0 0 t₂ h := by
  have ht₂ : t₂ ≠ 0 := by intro h'; apply h; simp [h']
  apply gl_eq_of_entries <;> simp [mul_coe_apply, nU_coe] ; field_simp

theorem continuous_nU : Continuous fun x : F => (nU x : G) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    all_goals simp only [Function.comp_apply, nU_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
    all_goals fun_prop
  · have : (fun x : F => (((nU x : G)⁻¹ : G) : Mat)) = fun x => !![1, -x; 0, 1] := by
      funext x
      rw [show ((nU x : G)⁻¹ : G) = nU (-x) from by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← nU_add, neg_add_cancel, nU_zero]]
      rfl
    rw [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    all_goals simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
    all_goals fun_prop

theorem lowU_add (x y : F) : (lowU (x + y) : G) = lowU x * lowU y := by
  apply gl_eq_of_entries <;> simp [mul_coe_apply, lowU_coe] <;> ring

theorem lowU_zero : (lowU (0 : F) : G) = 1 := by
  apply gl_eq_of_entries <;> simp [lowU_coe]

theorem lowU_inv (y : F) : ((lowU y : G)⁻¹ : G) = lowU (-y) := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← lowU_add, neg_add_cancel, lowU_zero]

theorem continuous_lowU : Continuous fun y : F => (lowU y : G) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    all_goals simp only [Function.comp_apply, lowU_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
    all_goals fun_prop
  · have : (fun y : F => (((lowU y : G)⁻¹ : G) : Mat)) = fun y => !![1, 0; -y, 1] := by
      funext y; rw [lowU_inv, lowU_coe]
    rw [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    all_goals simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
    all_goals fun_prop

theorem exists_nU_mem {K : Subgroup G} (hK : IsOpen (K : Set G)) :
    ∃ n : ℕ, ∀ x ∈ ball p (-(n : ℤ)), (nU x : G) ∈ K := by
  obtain ⟨n, hn⟩ := exists_ball_subset (hK.preimage continuous_nU) (by
    show (nU (0 : F) : G) ∈ (K : Set G)
    rw [nU_zero]; exact K.one_mem)
  exact ⟨n, fun x hx => hn hx⟩

theorem exists_lowU_mem {K : Subgroup G} (hK : IsOpen (K : Set G)) :
    ∃ n : ℕ, ∀ y ∈ ball p (-(n : ℤ)), (lowU y : G) ∈ K := by
  obtain ⟨n, hn⟩ := exists_ball_subset (hK.preimage continuous_lowU) (by
    show (lowU (0 : F) : G) ∈ (K : Set G)
    rw [lowU_zero]; exact K.one_mem)
  exact ⟨n, fun x hx => hn hx⟩

def stab (W : G → ℂ) : Subgroup G where
  carrier := {h | ∀ g, W (g * h) = W g}
  one_mem' := fun g => by rw [mul_one]
  mul_mem' := by
    intro a b ha hb g
    rw [← mul_assoc, hb, ha]
  inv_mem' := by
    intro a ha g
    have := ha (g * a⁻¹)
    rw [inv_mul_cancel_right] at this
    exact this.symm

theorem mem_stab {W : G → ℂ} {h : G} : h ∈ stab W ↔ ∀ g, W (g * h) = W g := Iff.rfl

variable (p) in

abbrev Q (j i : ℤ) : Type := ↥(ball p j) ⧸ (ball p i).addSubgroupOf (ball p j)

scoped instance instFiniteQ (j i : ℤ) : Finite (Q p j i) := by
  classical
  obtain ⟨T, hT⟩ := (isCompact_ball (p := p) j).elim_finite_subcover
    (fun x : ball p j => ((x : F) +ᵥ (ball p i : Set F) : Set F)) (fun x => (isOpen_ball i).left_addCoset _)
    (by
      intro x hx
      rw [Set.mem_iUnion]
      refine ⟨⟨x, hx⟩, ?_⟩
      rw [mem_leftAddCoset_iff, neg_add_cancel]
      exact zero_mem_ball i)
  let f : ↥T → Q p j i := fun t => QuotientAddGroup.mk (t.1 : ball p j)
  refine Finite.of_surjective f ?_
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H x =>
    have hx := hT x.2
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨t, htT, hxt⟩ := hx
    refine ⟨⟨t, htT⟩, ?_⟩
    show QuotientAddGroup.mk t = QuotientAddGroup.mk x
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    rw [mem_leftAddCoset_iff] at hxt
    exact hxt

scoped instance instFintypeQ (j i : ℤ) : Fintype (Q p j i) := Fintype.ofFinite _

def qsum (j i : ℤ) (f : F → ℂ) : ℂ :=
  ∑ q : Q p j i, f ((q.out : ball p j) : F)

def IsPer (i : ℤ) (f : F → ℂ) : Prop := ∀ (x c : F), c ∈ ball p i → f (x + c) = f x

theorem IsPer.mono {i i' : ℤ} {f : F → ℂ} (hf : IsPer i f) (h : i' ≤ i) : IsPer i' f :=
  fun x c hc => hf x c (ball_mono h hc)

theorem IsPer.mul {i : ℤ} {f g : F → ℂ} (hf : IsPer i f) (hg : IsPer i g) : IsPer i (fun x => f x * g x) :=
  fun x c hc => by simp only [hf x c hc, hg x c hc]

theorem qsum_add (j i : ℤ) (f g : F → ℂ) : qsum j i (fun x => f x + g x) = qsum j i f + qsum j i g := by
  unfold qsum; rw [← Finset.sum_add_distrib]

theorem qsum_sub (j i : ℤ) (f g : F → ℂ) : qsum j i (fun x => f x - g x) = qsum j i f - qsum j i g := by
  unfold qsum; rw [← Finset.sum_sub_distrib]

theorem qsum_const_mul (j i : ℤ) (c : ℂ) (f : F → ℂ) : qsum j i (fun x => c * f x) = c * qsum j i f := by
  unfold qsum; rw [Finset.mul_sum]

theorem qsum_zero (j i : ℤ) : qsum j i (fun _ : F => (0 : ℂ)) = 0 := by
  unfold qsum; exact Finset.sum_const_zero

theorem qsum_congr {j i : ℤ} {f g : F → ℂ} (h : ∀ x ∈ ball p j, f x = g x) : qsum j i f = qsum j i g := by
  unfold qsum
  exact Finset.sum_congr rfl fun q _ => h _ (q.out).2

theorem out_mk_spec {j i : ℤ} (x : ball p j) :
    ∃ c : F, c ∈ ball p i ∧ (((QuotientAddGroup.mk x : Q p j i).out : ball p j) : F) = (x : F) + c := by
  obtain ⟨h, H⟩ := QuotientAddGroup.mk_out_eq_mul ((ball p i).addSubgroupOf (ball p j)) x
  refine ⟨((h : ball p j) : F), ?_, ?_⟩
  · exact AddSubgroup.mem_addSubgroupOf.mp h.2
  · rw [H]; rfl

theorem IsPer.apply_out_mk {j i : ℤ} {f : F → ℂ} (hf : IsPer i f) (x : ball p j) :
    f (((QuotientAddGroup.mk x : Q p j i).out : ball p j) : F) = f x := by
  obtain ⟨c, hc, hce⟩ := out_mk_spec (i := i) x
  rw [hce, hf _ c hc]

theorem IsPer.qsum_translate {j i : ℤ} {f : F → ℂ} (hf : IsPer i f) {x₀ : F} (hx₀ : x₀ ∈ ball p j) :
    qsum j i (fun x => f (x + x₀)) = qsum j i f := by
  unfold qsum
  set y₀ : ball p j := ⟨x₀, hx₀⟩
  have key : ∀ q : Q p j i,
      f (((q.out : ball p j) : F) + x₀) = f (((q + QuotientAddGroup.mk y₀ : Q p j i).out : ball p j) : F) := by
    intro q
    have hq : q + QuotientAddGroup.mk y₀ = QuotientAddGroup.mk (q.out + y₀) := by
      conv_lhs => rw [← QuotientAddGroup.out_eq' q]
      rfl
    rw [hq, hf.apply_out_mk]
    rfl
  simp_rw [key]
  exact Fintype.sum_equiv (Equiv.addRight (QuotientAddGroup.mk y₀)) _ _ fun q => rfl

theorem qsum_psi_eq_zero {j i : ℤ} {b : F} (hper : IsPer i fun x => ψ (b * x))
    {x₀ : F} (hx₀ : x₀ ∈ ball p j) (hne : ψ (b * x₀) ≠ 1) :
    qsum j i (fun x => ψ (b * x)) = 0 := by
  have h := hper.qsum_translate hx₀
  have h2 : (fun x => ψ (b * (x + x₀))) = fun x => ψ (b * x₀) * ψ (b * x) := by
    funext x; rw [mul_add, AddChar.map_add_eq_mul, mul_comm]
  rw [h2, qsum_const_mul] at h
  have h3 : (ψ (b * x₀) - 1) * qsum j i (fun x => ψ (b * x)) = 0 := by rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hne)

theorem qsum_psi_eq_card {j i : ℤ} {b : F} (h : ∀ x ∈ ball p j, ψ (b * x) = 1) :
    qsum j i (fun x => ψ (b * x)) = Fintype.card (Q p j i) := by
  unfold qsum
  rw [Finset.sum_congr rfl fun q _ => h _ (q.out).2, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_univ]

theorem qsum_freq_eq_card {i L : ℤ} {y : F} (hy : y ∈ ball p L) (hyi : y ∈ ball p i) :
    qsum (-i) (-L) (fun a => ψ (a * y)) = (Fintype.card (Q p (-i) (-L)) : ℂ) := by
  have hcomm : (fun a : F => ψ (a * y)) = fun a => ψ (y * a) := by funext a; rw [mul_comm]
  rw [hcomm]
  exact qsum_psi_eq_card (j := -i) (i := -L) fun a ha => psi_mul_eq_one hyi ha (by omega)

theorem qsum_freq_eq_zero {i L : ℤ} {y : F} (hy : y ∈ ball p L) (hyi : y ∉ ball p i) :
    qsum (-i) (-L) (fun a => ψ (a * y)) = 0 := by
  have hper : IsPer (-L) fun a => ψ (y * a) := by
    intro a c hc
    show ψ (y * (a + c)) = ψ (y * a)
    rw [mul_add, AddChar.map_add_eq_mul, psi_mul_eq_one hy hc (by omega), mul_one]
  have hcomm : (fun a : F => ψ (a * y)) = fun a => ψ (y * a) := by funext a; rw [mul_comm]
  rw [mem_ball] at hyi
  obtain ⟨a₀, ha₀, hne⟩ := exists_freq hyi
  rw [hcomm]
  refine qsum_psi_eq_zero (j := -i) (i := -L) hper (mem_ball.mpr ha₀) ?_
  rwa [mul_comm] at hne

theorem inversion {i L : ℤ} {f : F → ℂ} (hf : IsPer i f) {x₀ : F} (hx₀ : x₀ ∈ ball p L) :
    (Fintype.card (Q p (-i) (-L)) : ℂ) * f x₀ =
      ∑ a : Q p (-i) (-L), ψ (((a.out : ball p (-i)) : F) * x₀) *
        qsum L i (fun x => ψ (-((((a.out : ball p (-i)) : F)) * x)) * f x) := by
  classical

  have hswap : ∑ a : Q p (-i) (-L), ψ (((a.out : ball p (-i)) : F) * x₀) *
        qsum L i (fun x => ψ (-((((a.out : ball p (-i)) : F)) * x)) * f x)
      = ∑ q : Q p L i, f ((q.out : ball p L) : F) *
          qsum (-i) (-L) (fun a => ψ (a * (x₀ - ((q.out : ball p L) : F)))) := by
    unfold qsum
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun a _ => ?_
    rw [mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, ← mul_neg]
    ring
  rw [hswap]

  have hinner : ∀ q : Q p L i,
      qsum (-i) (-L) (fun a => ψ (a * (x₀ - ((q.out : ball p L) : F)))) =
        if q = QuotientAddGroup.mk ⟨x₀, hx₀⟩ then (Fintype.card (Q p (-i) (-L)) : ℂ) else 0 := by
    intro q
    have hy : x₀ - ((q.out : ball p L) : F) ∈ ball p L := (ball p L).sub_mem hx₀ (q.out).2
    have hiff : x₀ - ((q.out : ball p L) : F) ∈ ball p i ↔ q = QuotientAddGroup.mk ⟨x₀, hx₀⟩ := by
      conv_rhs => rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      rw [show (((-q.out + ⟨x₀, hx₀⟩ : ball p L)) : F) = x₀ - ((q.out : ball p L) : F) from by
        rw [AddSubgroup.coe_add, AddSubgroup.coe_neg, neg_add_eq_sub]]
    by_cases hq : q = QuotientAddGroup.mk ⟨x₀, hx₀⟩
    · rw [if_pos hq, qsum_freq_eq_card hy (hiff.mpr hq)]
    · rw [if_neg hq, qsum_freq_eq_zero hy (fun h => hq (hiff.mp h))]
  simp_rw [hinner, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ, if_pos (Finset.mem_univ _), hf.apply_out_mk, mul_comm]

theorem apply_eq_apply_zero_of_vanishing {i L M : ℤ} {f : F → ℂ} (hf : IsPer i f) (hML : M ≤ L)
    (hvan : ∀ a : F, a ∈ ball p (-i) → a ∉ ball p (-M) →
      qsum L i (fun x => ψ (-(a * x)) * f x) = 0)
    {x₀ : F} (hx₀ : x₀ ∈ ball p M) : f x₀ = f 0 := by
  have h1 := inversion hf (ball_mono hML hx₀)
  have h0 := inversion hf (zero_mem_ball (p := p) L)
  have hterm : ∀ a : Q p (-i) (-L),
      ψ (((a.out : ball p (-i)) : F) * x₀) *
          qsum L i (fun x => ψ (-((((a.out : ball p (-i)) : F)) * x)) * f x)
        = ψ (((a.out : ball p (-i)) : F) * 0) *
          qsum L i (fun x => ψ (-((((a.out : ball p (-i)) : F)) * x)) * f x) := by
    intro a
    by_cases ha : ((a.out : ball p (-i)) : F) ∈ ball p (-M)
    · rw [psi_mul_eq_one ha hx₀ (by omega), mul_zero, AddChar.map_zero_eq_one]
    · rw [hvan _ (a.out).2 ha, mul_zero, mul_zero]
  rw [Finset.sum_congr rfl fun a _ => hterm a, ← h0] at h1
  have hcard : (Fintype.card (Q p (-i) (-L)) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact mul_left_cancel₀ hcard h1

end KirillovInjectivity
p2m_reactivate "P2MW.S_AutomorphicForm_LocalFunctionSpace_eq_zero_of_forall_apply_diagOne_eq_zero_of_irreducible_of_admissible.KirillovInjectivity"

namespace KirillovInjectivity

variable {p : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => HeightOneSpectrum.adicCompletion ℚ p
local notation "Mat" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)
local notation "ψ" => NumberField.StandardAddChar.psiV p

section Main

variable {S : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ)}
  (hstab : ∀ W ∈ S, ∀ k : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p), (fun g => W (g * k)) ∈ S)
  (hsm : ∀ W ∈ S, ∃ K : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
      IsOpen (K : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) ∧ ∀ k ∈ K, (fun g => W (g * k)) = W)
  (hpsi : ∀ W ∈ S, ∀ (x : HeightOneSpectrum.adicCompletion ℚ p)
      (g : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
      W (AutomorphicForm.unipotentGL2 x * g) = NumberField.StandardAddChar.psiV p x * W g)
  (hirr : ∀ T : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ), T ≤ S →
      (∀ W ∈ T, ∀ k : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p), (fun g => W (g * k)) ∈ T) →
      T = ⊥ ∨ T = S)
  (hadm : ∀ K : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
      IsOpen (K : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) →
      ∀ T : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ), T ≤ S →
        (∀ W ∈ T, ∀ k ∈ K, (fun g => W (g * k)) = W) → FiniteDimensional ℂ T)

include hsm in

theorem exists_nU_fixed {U : G → ℂ} (hU : U ∈ S) :
    ∃ n : ℕ, ∀ c ∈ ball p (-(n : ℤ)), ∀ g : G, U (g * nU c) = U g := by
  obtain ⟨K, hK, hKU⟩ := hsm U hU
  obtain ⟨n, hn⟩ := exists_nU_mem hK
  exact ⟨n, fun c hc g => congrFun (hKU _ (hn c hc)) g⟩

def JP (a : F) (V : G → ℂ) : Prop :=
  ∃ m₀ : ℤ, 0 ≤ m₀ ∧ ∃ i₀ : ℤ, ∀ L : ℤ, m₀ ≤ L → ∀ i : ℤ, i ≤ i₀ → ∀ δ ∈ ball p (-m₀), ∀ g : G,
    qsum L i (fun x => ψ (-((a + δ) * x)) * V (g * nU (a * x))) = 0

theorem JP_zero (a : F) : JP a (0 : G → ℂ) :=
  ⟨0, le_rfl, 0, fun L _ i _ δ _ g => by simp only [Pi.zero_apply, mul_zero]; exact qsum_zero L i⟩

theorem JP_add {a : F} {V₁ V₂ : G → ℂ} (h₁ : JP a V₁) (h₂ : JP a V₂) : JP a (V₁ + V₂) := by
  obtain ⟨m₁, hm₁, i₁, H₁⟩ := h₁
  obtain ⟨m₂, hm₂, i₂, H₂⟩ := h₂
  refine ⟨max m₁ m₂, le_max_of_le_left hm₁, min i₁ i₂, fun L hL i hi δ hδ g => ?_⟩
  have e : (fun x => ψ (-((a + δ) * x)) * (V₁ + V₂) (g * nU (a * x)))
      = fun x => ψ (-((a + δ) * x)) * V₁ (g * nU (a * x)) + ψ (-((a + δ) * x)) * V₂ (g * nU (a * x)) := by
    funext x; rw [Pi.add_apply, mul_add]
  rw [e, qsum_add, H₁ L ((le_max_left _ _).trans hL) i (hi.trans (min_le_left _ _)) δ
      (ball_mono (by omega) hδ) g,
    H₂ L ((le_max_right _ _).trans hL) i (hi.trans (min_le_right _ _)) δ (ball_mono (by omega) hδ) g,
    add_zero]

theorem JP_smul {a : F} (c : ℂ) {V : G → ℂ} (h : JP a V) : JP a (c • V) := by
  obtain ⟨m, hm, i₀, H⟩ := h
  refine ⟨m, hm, i₀, fun L hL i hi δ hδ g => ?_⟩
  have e : (fun x => ψ (-((a + δ) * x)) * (c • V) (g * nU (a * x)))
      = fun x => c * (ψ (-((a + δ) * x)) * V (g * nU (a * x))) := by
    funext x; rw [Pi.smul_apply, smul_eq_mul]; ring
  rw [e, qsum_const_mul, H L hL i hi δ hδ g, mul_zero]

include hsm in

theorem JP_defect {a : F} (ha : a ≠ 0) {U' : G → ℂ} (hU' : U' ∈ S) (y : F) :
    JP a ((fun g => U' (g * nU y)) - ψ y • U') := by
  obtain ⟨nU', hnU'⟩ := exists_nU_fixed hsm hU'
  set s : F := a⁻¹ * y with hs
  obtain ⟨Ms, hMs0, hMs⟩ := exists_v_le_exp s
  obtain ⟨ja, hja0, hja⟩ := exists_v_le_exp a
  refine ⟨Ms, hMs0, -(nU' : ℤ) - ja, fun L hL i hi δ hδ g => ?_⟩

  set Gf : F → ℂ := fun x => ψ (-((a + δ) * x)) * U' (g * nU (a * x)) with hGf
  have haδ : a + δ ∈ ball p ja := (ball p ja).add_mem hja (ball_mono (by omega) hδ)
  have hGper : IsPer i Gf := by
    intro x c hc
    simp only [hGf]
    have h1 : ψ (-((a + δ) * (x + c))) = ψ (-((a + δ) * x)) := by
      rw [mul_add, neg_add, AddChar.map_add_eq_mul]
      rw [show -((a + δ) * c) = (a + δ) * (-c) by ring, psi_mul_eq_one haδ ((ball p i).neg_mem hc) (by omega),
        mul_one]
    have h2 : U' (g * nU (a * (x + c))) = U' (g * nU (a * x)) := by
      rw [mul_add, nU_add, ← mul_assoc]
      exact hnU' _ (ball_mono (by omega) (mul_mem_ball hja hc)) _
    rw [h1, h2]

  have hsL : s ∈ ball p L := ball_mono hL hMs
  have hfirst : ∀ x : F, ψ (-((a + δ) * x)) * U' (g * nU (a * x) * nU y) = ψ y * Gf (x + s) := by
    intro x
    simp only [hGf]
    have e1 : g * nU (a * x) * nU y = g * nU (a * (x + s)) := by
      rw [mul_assoc, ← nU_add]; congr 2; rw [hs]; field_simp
    have e2 : ψ (-((a + δ) * x)) = ψ y * ψ (-((a + δ) * (x + s))) := by
      have : -((a + δ) * x) = (a * s + δ * s) + -((a + δ) * (x + s)) := by ring
      rw [this, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
        psi_mul_eq_one hδ hMs (by omega), mul_one]
      congr 2; rw [hs]; field_simp
    rw [e1, e2, mul_assoc]
  have hsplit : (fun x => ψ (-((a + δ) * x)) * ((fun g => U' (g * nU y)) - ψ y • U') (g * nU (a * x)))
      = fun x => ψ y * Gf (x + s) - ψ y * Gf x := by
    funext x
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, hfirst x]
    simp only [hGf]; ring
  rw [hsplit, qsum_sub, qsum_const_mul, qsum_const_mul, hGper.qsum_translate hsL, sub_self]

include hstab hsm hpsi hirr hadm in

theorem jacquet {W : G → ℂ} (hW : W ∈ S) (hW0 : ∀ y : Fˣ, W (AdelicLevel.diagOne y) = 0)
    {a : F} (ha : a ≠ 0) :
    ∃ m₀ : ℤ, 0 ≤ m₀ ∧ ∃ i₀ : ℤ, ∀ L : ℤ, m₀ ≤ L → ∀ i : ℤ, i ≤ i₀ → ∀ δ ∈ ball p (-m₀), ∀ g : G,
      qsum L i (fun x => ψ (-((a + δ) * x)) * W (g * nU x)) = 0 := by
  set d : G := AdelicLevel.diagOne (Units.mk0 a ha) with hd
  set U : G → ℂ := fun g => W (g * d) with hU
  have hUS : U ∈ S := hstab W hW d
  have hU1 : U 1 = 0 := by simp only [hU, one_mul, hd]; exact hW0 _
  have hmem := AutomorphicForm.LocalFunctionSpace.mem_span_sub_of_apply_one_eq_zero_of_irreducible_of_admissible
    p S hstab hsm hpsi hirr hadm U hUS hU1
  have hJP : JP a U := by
    refine Submodule.span_induction (p := fun V _ => JP (p := p) a V) ?_ (JP_zero a) (fun x y _ _ hx hy => JP_add hx hy)
      (fun c x _ hx => JP_smul c hx) hmem
    rintro V ⟨U', hU', y, rfl⟩
    exact JP_defect hsm ha hU' y
  obtain ⟨m₀, hm₀, i₀, H⟩ := hJP
  refine ⟨m₀, hm₀, i₀, fun L hL i hi δ hδ g => ?_⟩
  have key : ∀ x : F, W (g * nU x) = U (g * d⁻¹ * nU (a * x)) := by
    intro x
    simp only [hU]
    congr 1
    rw [mul_assoc, mul_assoc, hd, nU_mul_diagOne, ← mul_assoc, ← mul_assoc, inv_mul_cancel_right]
    congr 2
    rw [Units.val_mk0, inv_mul_cancel_left₀ ha]
  simp_rw [key]
  exact H L hL i hi δ hδ (g * d⁻¹)

include hstab hsm hpsi hirr hadm in

theorem nU_mem_stab {W : G → ℂ} (hW : W ∈ S) (hW0 : ∀ y : Fˣ, W (AdelicLevel.diagOne y) = 0)
    (x : F) : (nU x : G) ∈ stab W := by
  classical
  intro g
  obtain ⟨nW, hnW⟩ := exists_nU_fixed hsm hW
  set jW : ℤ := -(nW : ℤ) with hjW
  obtain ⟨M, hM0, hxM⟩ := exists_v_le_exp x

  set A : Set F := {a | a ∈ ball p (-jW) ∧ a ∉ ball p (-M)} with hA
  have hAc : IsCompact A :=
    (isCompact_ball (-jW)).inter_right (isClosed_compl_iff.2 (isOpen_ball (-M)))
  have hAne : ∀ a ∈ A, a ≠ 0 := by
    rintro a ⟨_, ha⟩ rfl; exact ha (zero_mem_ball _)
  have hJ : ∀ a : A, ∃ m₀ : ℤ, 0 ≤ m₀ ∧ ∃ i₀ : ℤ, ∀ L : ℤ, m₀ ≤ L → ∀ i : ℤ, i ≤ i₀ →
      ∀ δ ∈ ball p (-m₀), ∀ g : G, qsum L i (fun x => ψ (-(((a : F) + δ) * x)) * W (g * nU x)) = 0 :=
    fun a => jacquet hstab hsm hpsi hirr hadm hW hW0 (hAne a a.2)
  choose m₀ hm₀ i₀ hJ' using hJ
  set b : A → Set F := fun a => (fun a' : F => a' - (a : F)) ⁻¹' (ball p (-m₀ a) : Set F) with hb
  have hbo : ∀ a, IsOpen (b a) := fun a => (isOpen_ball _).preimage (continuous_id.sub continuous_const)
  have hcov : A ⊆ ⋃ a, b a := by
    intro a ha
    rw [Set.mem_iUnion]
    refine ⟨⟨a, ha⟩, ?_⟩
    show a - a ∈ ball p (-m₀ ⟨a, ha⟩)
    rw [sub_self]; exact zero_mem_ball _
  obtain ⟨T, hT⟩ := hAc.elim_finite_subcover b hbo hcov

  set L : ℤ := M + ∑ a ∈ T, m₀ a with hL
  set i : ℤ := -((nW : ℤ) + ∑ a ∈ T, |i₀ a|) with hi
  have hLM : M ≤ L := by
    rw [hL]; exact le_add_of_nonneg_right (Finset.sum_nonneg fun a _ => hm₀ a)
  have hLa : ∀ a ∈ T, m₀ a ≤ L := by
    intro a ha
    rw [hL]
    exact (Finset.single_le_sum (fun a _ => hm₀ a) ha).trans (le_add_of_nonneg_left hM0)
  have hijW : i ≤ jW := by
    rw [hi, hjW]
    have := Finset.sum_nonneg (fun a (_ : a ∈ T) => abs_nonneg (i₀ a))
    omega
  have hia : ∀ a ∈ T, i ≤ i₀ a := by
    intro a ha
    rw [hi]
    have h1 := Finset.single_le_sum (fun a (_ : a ∈ T) => abs_nonneg (i₀ a)) ha
    have h2 := neg_abs_le (i₀ a)
    omega

  set f : F → ℂ := fun x => W (g * nU x) with hf
  have hfper : IsPer i f := by
    intro x c hc
    simp only [hf]
    rw [nU_add, ← mul_assoc]
    exact hnW _ (ball_mono hijW hc) _
  have hvan : ∀ a : F, a ∈ ball p (-i) → a ∉ ball p (-M) → qsum L i (fun x => ψ (-(a * x)) * f x) = 0 := by
    intro a hai haM
    by_cases hajW : a ∈ ball p (-jW)
    ·
      have haA : a ∈ A := ⟨hajW, haM⟩
      have := hT haA
      rw [Set.mem_iUnion₂] at this
      obtain ⟨t, htT, hat⟩ := this
      have hδ : a - (t : F) ∈ ball p (-m₀ t) := hat
      have := hJ' t L (hLa t htT) i (hia t htT) (a - (t : F)) hδ g
      simpa only [add_sub_cancel] using this
    ·
      obtain ⟨c, hc, hne⟩ := exists_freq (mem_ball.not.mp hajW)
      rw [neg_neg] at hc
      have hcjW : c ∈ ball p jW := hc
      set h : F → ℂ := fun x => ψ (-(a * x)) * f x with hh
      have hhper : IsPer i h := by
        refine IsPer.mul (fun x c' hc' => ?_) hfper
        rw [mul_add, neg_add, AddChar.map_add_eq_mul, show -(a * c') = a * (-c') by ring,
          psi_mul_eq_one hai ((ball p i).neg_mem hc') (by omega), mul_one]
      have htr := hhper.qsum_translate (ball_mono (by omega : jW ≤ L) hcjW)
      have hshift : (fun x => h (x + c)) = fun x => ψ (-(a * c)) * h x := by
        funext x
        simp only [hh, hf]
        rw [mul_add, neg_add, AddChar.map_add_eq_mul, nU_add, ← mul_assoc, hnW _ hcjW]
        ring
      rw [hshift, qsum_const_mul] at htr
      have h3 : (ψ (-(a * c)) - 1) * qsum L i h = 0 := by rw [sub_mul, one_mul, htr, sub_self]
      refine (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr ?_)
      rw [mul_comm] at hne
      exact psi_neg_ne_one hne
  have := apply_eq_apply_zero_of_vanishing hfper hLM hvan (mem_ball.mpr hxM)
  simpa only [hf, nU_zero, mul_one] using this

include hstab hsm hpsi hirr hadm in

theorem eq_zero {W : G → ℂ} (hW : W ∈ S) (hW0 : ∀ y : Fˣ, W (AdelicLevel.diagOne y) = 0) : W = 0 := by
  have hN : ∀ x : F, (nU x : G) ∈ stab W := nU_mem_stab hstab hsm hpsi hirr hadm hW hW0

  obtain ⟨K, hK, hKW⟩ := hsm W hW
  obtain ⟨n, hn⟩ := exists_lowU_mem hK
  obtain ⟨y₀, hy₀, hy₀n⟩ := exists_ne_zero_mem_ball (p := p) (-(n : ℤ))
  have hlow₀ : (lowU y₀ : G) ∈ stab W := fun g => congrFun (hKW _ (hn y₀ hy₀n)) g

  have hw'det : (0 : F) * 0 - (-y₀⁻¹) * y₀ ≠ 0 := by field_simp; simp
  have hw'eq : (nU (-y₀⁻¹) : G) * lowU y₀ * nU (-y₀⁻¹) = gl2 0 (-y₀⁻¹) y₀ 0 hw'det := by
    apply gl_eq_of_entries <;> simp [mul_coe_apply, nU_coe, lowU_coe, hy₀]
  have hw' : (gl2 0 (-y₀⁻¹) y₀ 0 hw'det : G) ∈ stab W := by
    rw [← hw'eq]; exact (stab W).mul_mem ((stab W).mul_mem (hN _) hlow₀) (hN _)

  have hlow : ∀ z : F, (lowU z : G) ∈ stab W := by
    intro z
    have hconj : (gl2 0 (-y₀⁻¹) y₀ 0 hw'det : G) * nU (-(y₀⁻¹ * (y₀⁻¹ * z))) * (gl2 0 (-y₀⁻¹) y₀ 0 hw'det)⁻¹
        = lowU z := by
      rw [mul_inv_eq_iff_eq_mul]
      apply gl_eq_of_entries <;> simp [mul_coe_apply, nU_coe, lowU_coe, hy₀] <;> ring
    rw [← hconj]
    exact (stab W).mul_mem ((stab W).mul_mem hw' (hN _)) ((stab W).inv_mem hw')

  funext g
  rw [Pi.zero_apply]
  have hϖ : ψ (unif p)⁻¹ ≠ 1 := psi_unif_inv_ne_one
  by_cases hγ : (g : Mat) 1 0 = 0
  ·
    have hdet : (g : Mat).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero g
    rw [Matrix.det_fin_two, hγ, mul_zero, sub_zero] at hdet
    have hα : (g : Mat) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
    have hδ : (g : Mat) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
    have hD : (g : Mat) 0 0 * (g : Mat) 1 1 - 0 * 0 ≠ 0 := by simpa using hdet
    set D : G := gl2 ((g : Mat) 0 0) 0 0 ((g : Mat) 1 1) hD with hDdef
    have hg : g = nU ((g : Mat) 0 1 / (g : Mat) 1 1) * D := by
      apply gl_eq_of_entries <;> simp [mul_coe_apply, nU_coe, D, hγ, hδ]
    have hDval : W D = 0 := by
      set x : F := (g : Mat) 1 1 * ((g : Mat) 0 0)⁻¹ * (unif p)⁻¹ with hx
      have h1 : W (D * nU x) = W D := hN x D
      rw [hDdef, diag_mul_nU, hpsi W hW] at h1
      have hval : (g : Mat) 0 0 * x * ((g : Mat) 1 1)⁻¹ = (unif p)⁻¹ := by
        rw [hx]; field_simp
      rw [hval] at h1
      have h2 : (ψ (unif p)⁻¹ - 1) * W (gl2 ((g : Mat) 0 0) 0 0 ((g : Mat) 1 1) hD) = 0 := by
        rw [sub_mul, one_mul, h1, sub_self]
      exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hϖ)
    rw [hg, hpsi W hW, hDval, mul_zero]
  ·
    have hdet : (g : Mat).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero g
    rw [Matrix.det_fin_two] at hdet
    set e : F := (g : Mat) 0 1 - (g : Mat) 0 0 * (g : Mat) 1 1 / (g : Mat) 1 0 with he
    have he0 : e ≠ 0 := by
      rw [he]; intro h; apply hdet; field_simp at h; linear_combination -h
    have hg₁det : (g : Mat) 0 0 * 0 - e * (g : Mat) 1 0 ≠ 0 := by
      rw [mul_zero, zero_sub, neg_ne_zero]; exact mul_ne_zero he0 hγ
    set g₁ : G := gl2 ((g : Mat) 0 0) e ((g : Mat) 1 0) 0 hg₁det with hg₁
    have hgg₁ : g * nU (-((g : Mat) 1 1 / (g : Mat) 1 0)) = g₁ := by
      apply gl_eq_of_entries <;> simp [mul_coe_apply, nU_coe, g₁, he, hγ] <;> field_simp <;> ring
    have hWg : W g = W g₁ := by rw [← hgg₁, hN]

    have hcomm : ∀ t : F, (nU t : G) * g₁ = g₁ * lowU (t * (g : Mat) 1 0 / e) := by
      intro t
      apply gl_eq_of_entries <;> simp [mul_coe_apply, nU_coe, lowU_coe, g₁, hγ, he0] <;> field_simp
    have h1 : W (nU (unif p)⁻¹ * g₁) = W g₁ := by rw [hcomm, hlow]
    rw [hpsi W hW] at h1
    have h2 : (ψ (unif p)⁻¹ - 1) * W g₁ = 0 := by rw [sub_mul, one_mul, h1, sub_self]
    rw [hWg]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hϖ)

end Main
p2m_reactivate "P2MW.S_AutomorphicForm_LocalFunctionSpace_eq_zero_of_forall_apply_diagOne_eq_zero_of_irreducible_of_admissible.KirillovInjectivity"

end KirillovInjectivity
p2m_reactivate "P2MW.S_AutomorphicForm_LocalFunctionSpace_eq_zero_of_forall_apply_diagOne_eq_zero_of_irreducible_of_admissible.KirillovInjectivity"

end
p2m_reactivate "P2MW.S_AutomorphicForm_LocalFunctionSpace_eq_zero_of_forall_apply_diagOne_eq_zero_of_irreducible_of_admissible.KirillovInjectivity"

open IsDedekindDomain NumberField in
theorem solution
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (S : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))
    (hstab : ∀ W ∈ S, ∀ k : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * k)) ∈ S)
    (hsm : ∀ W ∈ S, ∃ K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
        IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ K, (fun g => W (g * k)) = W)
    (hpsi : ∀ W ∈ S, ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        W (AutomorphicForm.unipotentGL2 x * g) = NumberField.StandardAddChar.psiV p x * W g)
    (hirr : ∀ T : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), T ≤ S →
        (∀ W ∈ T, ∀ k : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * k)) ∈ T) →
        T = ⊥ ∨ T = S)
    (hadm : ∀ K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
        IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
        ∀ T : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), T ≤ S →
          (∀ W ∈ T, ∀ k ∈ K, (fun g => W (g * k)) = W) → FiniteDimensional ℂ T) :
    ∀ W ∈ S, (∀ y : (p.adicCompletion ℚ)ˣ, W (NumberField.AdelicLevel.diagOne y) = 0) → W = 0 :=
  fun W hW hW0 => KirillovInjectivity.eq_zero hstab hsm hpsi hirr hadm hW hW0

end S_AutomorphicForm_LocalFunctionSpace_eq_zero_of_forall_apply_diagOne_eq_zero_of_irreducible_of_admissible
end P2MW
export P2MW.S_AutomorphicForm_LocalFunctionSpace_eq_zero_of_forall_apply_diagOne_eq_zero_of_irreducible_of_admissible (solution)
