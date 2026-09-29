-- Prove2me | solution 1 for AutomorphicForm.LocalFunctionSpace.mem_span_sub_of_apply_one_eq_zero_of_irreducible_of_admissible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/bd65577d-9d0a-5d25-a757-b177021e2a22

import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Theorems.Thm_AutomorphicForm_LocalFunctionSpace_eq_zero_of_forall_diagonal_mul_mem_span_sub
import Theorems.Thm_AutomorphicForm_LocalFunctionSpace_exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span
import Theorems.Thm_AutomorphicForm_LocalFunctionSpace_exists_smul_eq_of_irreducible_of_admissible
import Theorems.Thm_AutomorphicForm_LocalFunctionSpace_exists_finset_forall_eq_sum_mul_char_mul
import Theorems.Thm_Module_End_rank_le_one_of_countable_of_commute_of_forall_invariant_eq_bot_or_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_LocalFunctionSpace_mem_span_sub_of_apply_one_eq_zero_of_irreducible_of_admissible

set_option autoImplicit false

open scoped Classical

noncomputable section

namespace TwistedCoinvariantsAux

open AutomorphicForm IsDedekindDomain

variable (p : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

local notation "F" => HeightOneSpectrum.adicCompletion ℚ p
local notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)

private def defectSet (S : Submodule ℂ (G → ℂ)) : Set (G → ℂ) :=
  {V | ∃ U ∈ S, ∃ x : F, V = (fun g => U (g * unipotentGL2 x)) - NumberField.StandardAddChar.psiV p x • U}

private abbrev defectSpan (S : Submodule ℂ (G → ℂ)) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ (defectSet p S)

private def rT (k : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun V := fun g => V (g * k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] private theorem rT_apply (k : G) (V : G → ℂ) (g : G) : rT p k V g = V (g * k) := rfl

private theorem rT_rT (k₁ k₂ : G) (V : G → ℂ) : rT p k₁ (rT p k₂ V) = rT p (k₁ * k₂) V := by
  funext g; simp [mul_assoc]

@[scoped simp] private theorem rT_one (V : G → ℂ) : rT p 1 V = V := by funext g; simp

private abbrev coinv (S : Submodule ℂ (G → ℂ)) : Submodule ℂ ((G → ℂ) ⧸ defectSpan p S) :=
  S.map (defectSpan p S).mkQ

local notation "Fx" => Units (HeightOneSpectrum.adicCompletion ℚ p)

private noncomputable def dg (a : Fx) : G where
  val := !![(a : F), 0; 0, 1]
  inv := !![((a⁻¹ : Fx) : F), 0; 0, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] private theorem dg_coe (a : Fx) : (dg p a : Matrix (Fin 2) (Fin 2) F) = !![(a : F), 0; 0, 1] := rfl

private theorem dg_mul (a b : Fx) : dg p (a * b) = dg p a * dg p b := by
  apply Units.ext
  simp only [Units.val_mul, dg_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem dg_one : dg p 1 = 1 := by
  apply Units.ext
  simp only [dg_coe, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem dg_mul_unipotent (a : Fx) (x : F) :
    dg p a * unipotentGL2 x = unipotentGL2 ((a : F) * x) * dg p a := by
  apply Units.ext
  simp only [Units.val_mul, dg_coe, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private def wG : G where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] private theorem wG_coe : (wG p : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := rfl

private theorem wG_mul_wG : wG p * wG p = 1 := by
  apply Units.ext
  simp only [Units.val_mul, wG_coe, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private noncomputable def zG (c : Fx) : G where
  val := !![(c : F), 0; 0, (c : F)]
  inv := !![((c⁻¹ : Fx) : F), 0; 0, ((c⁻¹ : Fx) : F)]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] private theorem zG_coe (c : Fx) :
    (zG p c : Matrix (Fin 2) (Fin 2) F) = !![(c : F), 0; 0, (c : F)] := rfl

private theorem zG_mul_comm (c : Fx) (k : G) : zG p c * k = k * zG p c := by
  apply Units.ext
  simp only [Units.val_mul, zG_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem dg_mul_wG (a : Fx) : dg p a * wG p = wG p * zG p a * dg p a⁻¹ := by
  apply Units.ext
  simp only [Units.val_mul, dg_coe, wG_coe, zG_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

local notation "Γ" => Units (WithZero (Multiplicative ℤ))

private theorem exists_unit_gt (y : F) : ∃ β₀ : Γ, Valued.v y < (β₀ : WithZero (Multiplicative ℤ)) := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨1, by simp⟩
  · have hv : Valued.v y ≠ (0 : WithZero (Multiplicative ℤ)) := (Valuation.ne_zero_iff _).mpr hy
    obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.mp hv
    refine ⟨Units.mk0 ((m * Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      WithZero.coe_ne_zero, ?_⟩
    rw [← hm, Units.val_mk0, WithZero.coe_lt_coe, ← Multiplicative.toAdd_lt, toAdd_mul, toAdd_ofAdd]
    exact lt_add_one _

private theorem exists_ball_subset_of_mem_nhds {s : Set F} (hs : s ∈ nhds (0 : F)) :
    ∃ δ : Γ, ∀ y : F, Valued.v y < (δ : WithZero (Multiplicative ℤ)) → y ∈ s := by
  obtain ⟨γ, hγ⟩ := (Valued.is_topological_valuation _).mp hs
  have hb : MonoidWithZeroHom.ValueGroup₀.embedding γ.val ≠ (0 : WithZero (Multiplicative ℤ)) := by
    intro h
    exact γ.ne_zero (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective (h.trans (map_zero _).symm))
  refine ⟨Units.mk0 _ hb, fun y hy => ?_⟩
  apply hγ
  show Valued.v.restrict y < γ.val
  rw [Valuation.restrict_lt_iff_lt_embedding]
  simpa using hy

private theorem continuous_unipotentGL2 : Continuous (fun x : F => (unipotentGL2 x : G)) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe] <;> fun_prop
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2] <;> fun_prop

private theorem exists_unipotent_mem_of_isOpen (K : Subgroup G) (hK : IsOpen (K : Set G)) :
    ∃ δ : Γ, ∀ z : F, Valued.v z < (δ : WithZero (Multiplicative ℤ)) → unipotentGL2 z ∈ K := by
  have hU : ((fun z : F => (unipotentGL2 z : G)) ⁻¹' (K : Set G)) ∈ nhds (0 : F) := by
    apply (hK.preimage (continuous_unipotentGL2 p)).mem_nhds
    show unipotentGL2 (0 : F) ∈ K
    rw [unipotentGL2_zero]
    exact K.one_mem
  exact exists_ball_subset_of_mem_nhds p hU

private theorem exists_forall_mem_of_continuous (K : Subgroup G) (hK : IsOpen (K : Set G)) (f : Fx → G)
    (hf : Continuous f) (hf1 : f 1 ∈ K) :
    ∃ δ : Γ, ∀ u : Fx, Valued.v ((u : F) - 1) < (δ : WithZero (Multiplicative ℤ)) → f u ∈ K := by
  have h1 : (f ⁻¹' (K : Set G)) ∈ nhds (1 : Fx) := (hK.preimage hf).mem_nhds hf1
  rw [Units.isEmbedding_val₀.toIsInducing.nhds_eq_comap] at h1
  obtain ⟨T, hT, hTsub⟩ := Filter.mem_comap.mp h1
  have hT' : T ∈ nhds (1 : F) := hT
  have hc : ContinuousAt (fun y : F => 1 + y) 0 := (continuous_const.add continuous_id).continuousAt
  have h0 : (fun y : F => 1 + y) ⁻¹' T ∈ nhds (0 : F) := hc.preimage_mem_nhds (by simpa using hT')
  obtain ⟨δ, hδ⟩ := exists_ball_subset_of_mem_nhds p h0
  refine ⟨δ, fun u hu => ?_⟩
  have hmem : (u : F) ∈ T := by
    have h := hδ _ hu
    simpa using h
  exact hTsub hmem

private theorem continuous_dg : Continuous (fun u : Fx => (dg p u : G)) := by
  have hφ : Continuous (fun a : F => !![a, 0; 0, (1 : F)]) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  rw [Units.continuous_iff]
  exact ⟨hφ.comp Units.continuous_val, hφ.comp Units.continuous_coe_inv⟩

private theorem continuous_zG : Continuous (fun c : Fx => (zG p c : G)) := by
  have hφ : Continuous (fun a : F => !![a, 0; 0, a]) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  rw [Units.continuous_iff]
  exact ⟨hφ.comp Units.continuous_val, hφ.comp Units.continuous_coe_inv⟩

private theorem zG_mul (c d : Fx) : zG p (c * d) = zG p c * zG p d := by
  apply Units.ext
  simp only [Units.val_mul, zG_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem zG_one : zG p 1 = 1 := by
  apply Units.ext
  simp only [zG_coe, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem exists_dg_mem_of_isOpen (K : Subgroup G) (hK : IsOpen (K : Set G)) :
    ∃ δ : Γ, ∀ u : Fx, Valued.v ((u : F) - 1) < (δ : WithZero (Multiplicative ℤ)) → dg p u ∈ K :=
  exists_forall_mem_of_continuous p K hK _ (continuous_dg p) (by rw [dg_one]; exact K.one_mem)

private theorem exists_zG_mem_of_isOpen (K : Subgroup G) (hK : IsOpen (K : Set G)) :
    ∃ δ : Γ, ∀ c : Fx, Valued.v ((c : F) - 1) < (δ : WithZero (Multiplicative ℤ)) → zG p c ∈ K :=
  exists_forall_mem_of_continuous p K hK _ (continuous_zG p) (by rw [zG_one]; exact K.one_mem)

private abbrev factPrime (q : Nat.Primes) : Fact q.1.Prime := ⟨q.2⟩

attribute [local instance] factPrime

set_option synthInstance.maxHeartbeats 1600000 in

private theorem isCompact_integers : IsCompact {x : F | Valued.v x ≤ 1} := by
  haveI : CompactSpace (p.adicCompletionIntegers ℚ) :=
    (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv p).symm.toContinuousLinearEquiv.toHomeomorph
      |>.compactSpace
  have h := isCompact_range (continuous_subtype_val (p := fun x : F => x ∈ p.adicCompletionIntegers ℚ))
  convert h using 1
  ext x
  simp [HeightOneSpectrum.mem_adicCompletionIntegers]

private theorem isOpen_unit_ball : IsOpen {x : F | Valued.v x < (1 : WithZero (Multiplicative ℤ))} := by
  have h := Valued.isOpen_ball (R := F) 1
  convert h using 1
  ext x
  simp [Valuation.restrict_lt_iff_lt_embedding]

private theorem isCompact_valuation_eq_one : IsCompact {x : F | Valued.v x = 1} := by
  have hclosed : IsClosed {x : F | Valued.v x = 1} := by
    have h1 : IsClosed {x : F | Valued.v x ≤ 1} := (isCompact_integers p).isClosed
    have h2 : IsClosed {x : F | Valued.v x < (1 : WithZero (Multiplicative ℤ))}ᶜ := (isOpen_unit_ball p).isClosed_compl
    convert h1.inter h2 using 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, not_lt]
    exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩
  exact (isCompact_integers p).of_isClosed_subset hclosed (fun x hx => le_of_eq hx)

private theorem exists_valuation_eq (r : Γ) : ∃ c : F, Valued.v c = (r : WithZero (Multiplicative ℤ)) := by
  obtain ⟨π, hπ⟩ := p.valuation_exists_uniformizer' ℚ
  have hπ' : Valued.v (algebraMap (NumberField.RingOfIntegers ℚ) F π) = WithZero.exp (-1 : ℤ) :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) (v := p) π).trans hπ
  refine ⟨algebraMap (NumberField.RingOfIntegers ℚ) F π ^ (-WithZero.log (r : WithZero (Multiplicative ℤ))), ?_⟩
  rw [map_zpow₀, hπ', ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, neg_neg,
    WithZero.exp_log r.ne_zero]

private theorem isOpen_radiusBall (r : Γ) : IsOpen {x : F | Valued.v x < (r : WithZero (Multiplicative ℤ))} := by
  obtain ⟨c, hc⟩ := exists_valuation_eq p r
  have hset : {x : F | Valued.v x < (r : WithZero (Multiplicative ℤ))}
      = (fun x : F => c⁻¹ * x) ⁻¹' {y : F | Valued.v y < (1 : WithZero (Multiplicative ℤ))} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul, map_inv₀, hc]
    constructor
    · intro hx
      calc ((r : WithZero (Multiplicative ℤ)))⁻¹ * Valued.v x
          < ((r : WithZero (Multiplicative ℤ)))⁻¹ * (r : WithZero (Multiplicative ℤ)) :=
            mul_lt_mul_of_pos_left hx (zero_lt_iff.mpr (inv_ne_zero r.ne_zero))
        _ = 1 := inv_mul_cancel₀ r.ne_zero
    · intro hx
      have h := mul_lt_mul_of_pos_left hx (zero_lt_iff.mpr r.ne_zero)
      rwa [← mul_assoc, mul_inv_cancel₀ r.ne_zero, one_mul, mul_one] at h
  rw [hset]
  exact (isOpen_unit_ball p).preimage (continuous_const.mul continuous_id)

private theorem radiusBall_mem_nhds (y : F) (r : Γ) :
    {x : F | Valued.v (x - y) < (r : WithZero (Multiplicative ℤ))} ∈ nhds y := by
  have hopen : IsOpen {x : F | Valued.v (x - y) < (r : WithZero (Multiplicative ℤ))} :=
    (isOpen_radiusBall p r).preimage (continuous_id.sub continuous_const)
  exact hopen.mem_nhds (by simp)

private def UF : Subgroup Fx where
  carrier := {u | Valued.v (u : F) = 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at ha hb ⊢
    rw [ha, hb, mul_one]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, Units.val_inv_eq_inv_val, map_inv₀] at ha ⊢
    rw [ha, inv_one]

private theorem v_coe_UF (u : UF p) : Valued.v ((u : Fx) : F) = 1 := u.2

private def Um (δ : Γ) : Subgroup (UF p) where
  carrier := {u | Valued.v (((u : Fx) : F) - 1) < (δ : WithZero (Multiplicative ℤ))}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have e : (((a * b : UF p) : Fx) : F) - 1 = ((a : Fx) : F) * (((b : Fx) : F) - 1) + (((a : Fx) : F) - 1) := by
      simp only [Subgroup.coe_mul, Units.val_mul]
      ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans_lt (max_lt ?_ ha)
    rw [map_mul, v_coe_UF, one_mul]
    exact hb
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have e : (((a⁻¹ : UF p) : Fx) : F) - 1 = (((a⁻¹ : UF p) : Fx) : F) * (1 - ((a : Fx) : F)) := by
      have h : (((a⁻¹ : UF p) : Fx) : F) * ((a : Fx) : F) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
      rw [mul_sub, mul_one, h]
    rw [e, map_mul, v_coe_UF, one_mul, Valuation.map_sub_swap]
    exact ha

private theorem mem_Um_iff (δ : Γ) (u : UF p) :
    u ∈ Um p δ ↔ Valued.v (((u : Fx) : F) - 1) < (δ : WithZero (Multiplicative ℤ)) := Iff.rfl

private abbrev Qm (δ : Γ) : Type := UF p ⧸ Um p δ

private theorem mk_eq_mk_of_close (δ : Γ) (u x : UF p)
    (h : Valued.v (((x : Fx) : F) - ((u : Fx) : F)) < (δ : WithZero (Multiplicative ℤ))) :
    ((x : Qm p δ) = (u : Qm p δ)) := by
  rw [QuotientGroup.eq, mem_Um_iff]
  have e : (((x⁻¹ * u : UF p) : Fx) : F) - 1 = (((x⁻¹ : UF p) : Fx) : F) * (((u : Fx) : F) - ((x : Fx) : F)) := by
    have h1 : (((x⁻¹ : UF p) : Fx) : F) * ((x : Fx) : F) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
    rw [mul_sub, h1, Subgroup.coe_mul, Units.val_mul]
  rw [e, map_mul, v_coe_UF, one_mul, Valuation.map_sub_swap]
  exact h

private scoped instance finite_Qm (δ : Γ) : Finite (Qm p δ) := by
  obtain ⟨T, hT, hcover⟩ := (isCompact_valuation_eq_one p).elim_nhds_subcover
    (fun y => {x : F | Valued.v (x - y) < (δ : WithZero (Multiplicative ℤ))}) (fun y _ => radiusBall_mem_nhds p y δ)

  have hsurj : ∀ q : Qm p δ, ∃ t ∈ T, ∃ u : UF p, ((u : Fx) : F) = t ∧ (u : Qm p δ) = q := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : ((x : Fx) : F) ∈ {x : F | Valued.v x = 1} := v_coe_UF p x
    have hxU := hcover hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hxU
    obtain ⟨t, htT, hxt⟩ := hxU
    have ht1 : Valued.v t = 1 := hT t htT
    have ht0 : t ≠ 0 := by
      rintro rfl
      simp at ht1
    refine ⟨t, htT, ⟨Units.mk0 t ht0, ?_⟩, rfl, ?_⟩
    · show Valued.v ((Units.mk0 t ht0 : Fx) : F) = 1
      simpa using ht1
    · exact (mk_eq_mk_of_close p δ _ _ (by simpa using hxt)).symm
  choose ft hftT fu hfu hfq using hsurj

  have hinj : Function.Injective (fun q : Qm p δ => (⟨ft q, hftT q⟩ : T)) := by
    intro q₁ q₂ h
    have h' : ft q₁ = ft q₂ := congrArg Subtype.val h
    rw [← hfq q₁, ← hfq q₂]
    have hu : ((fu q₁ : Fx) : F) = ((fu q₂ : Fx) : F) := by rw [hfu, hfu, h']
    have hu' : fu q₁ = fu q₂ := Subtype.ext (Units.ext hu)
    rw [hu']
  exact Finite.of_injective _ hinj

private noncomputable scoped instance fintype_Qm (δ : Γ) : Fintype (Qm p δ) := Fintype.ofFinite _

private noncomputable def rep (δ : Γ) (q : Qm p δ) : UF p := q.out

private theorem mk_rep (δ : Γ) (q : Qm p δ) : ((rep p δ q : UF p) : Qm p δ) = q := QuotientGroup.out_eq' q

section charGeneric

variable {A : Type*} [AddCommGroup A]

private abbrev charAddCommGroup : AddCommGroup (AddChar A ℂ) := inferInstance

private noncomputable abbrev charFintype [Finite A] : Fintype (AddChar A ℂ) := inferInstance

private theorem char_map_add (ψ : AddChar A ℂ) (a b : A) : ψ (a + b) = ψ a * ψ b := AddChar.map_add_eq_mul ψ a b

private theorem char_map_zero (ψ : AddChar A ℂ) : ψ 0 = 1 := AddChar.map_zero_eq_one ψ

private theorem char_map_neg (ψ : AddChar A ℂ) (a : A) : ψ (-a) = (ψ a)⁻¹ := AddChar.map_neg_eq_inv ψ a

private theorem char_add_apply (ψ φ : AddChar A ℂ) (a : A) : (ψ + φ) a = ψ a * φ a := AddChar.add_apply ψ φ a

private theorem char_neg_apply (ψ : AddChar A ℂ) (a : A) : (-ψ) a = (ψ a)⁻¹ := AddChar.neg_apply' ψ a

private theorem char_zero_apply (a : A) : (0 : AddChar A ℂ) a = 1 := AddChar.zero_apply a

private theorem char_ext {ψ φ : AddChar A ℂ} (h : ∀ a : A, ψ a = φ a) : ψ = φ := AddChar.ext ψ φ h

private theorem char_sum_apply_of_eq_zero [Fintype A] {a : A} (ha : a = 0) :
    ∑ ψ : AddChar A ℂ, ψ a = (Fintype.card A : ℂ) := by
  classical
  rw [AddChar.sum_apply_eq_ite, if_pos ha]

private theorem char_sum_apply_of_ne_zero [Fintype A] {a : A} (ha : a ≠ 0) : ∑ ψ : AddChar A ℂ, ψ a = 0 := by
  classical
  rw [AddChar.sum_apply_eq_ite, if_neg ha]

private theorem char_sum_of_eq_zero [Fintype A] {ψ : AddChar A ℂ} (hψ : ψ = 0) : ∑ a, ψ a = (Fintype.card A : ℂ) := by
  classical
  rw [AddChar.sum_eq_ite, if_pos hψ]

private theorem char_sum_of_ne_zero [Fintype A] {ψ : AddChar A ℂ} (hψ : ψ ≠ 0) : ∑ a, ψ a = 0 := by
  classical
  rw [AddChar.sum_eq_ite, if_neg hψ]

end charGeneric

private scoped instance addCommGroup_additive_Qm (δ : Γ) : AddCommGroup (Additive (Qm p δ)) :=
  @Additive.addCommGroup _ (QuotientGroup.Quotient.commGroup _)

private scoped instance finite_additive_Qm (δ : Γ) : Finite (Additive (Qm p δ)) := Finite.of_equiv _ Additive.ofMul

private def Ch (δ : Γ) : Type := AddChar (Additive (Qm p δ)) ℂ

private scoped instance addCommGroup_Ch (δ : Γ) : AddCommGroup (Ch p δ) := charAddCommGroup (A := Additive (Qm p δ))

private noncomputable scoped instance fintype_Ch (δ : Γ) : Fintype (Ch p δ) := charFintype (A := Additive (Qm p δ))

private noncomputable scoped instance decidableEq_Ch (δ : Γ) : DecidableEq (Ch p δ) := Classical.decEq _

variable {p} in

private def Ch.toChar {δ : Γ} (χ : Ch p δ) : AddChar (Additive (Qm p δ)) ℂ := χ

variable {p} in

private noncomputable def chv {δ : Γ} (χ : Ch p δ) (u : UF p) : ℂ := Ch.toChar χ (Additive.ofMul (u : Qm p δ))

variable {p} in
private theorem chv_mul {δ : Γ} (χ : Ch p δ) (u v : UF p) : chv χ (u * v) = chv χ u * chv χ v := by
  unfold chv
  rw [QuotientGroup.mk_mul, ofMul_mul]
  exact char_map_add (Ch.toChar χ) _ _

variable {p} in
private theorem chv_one {δ : Γ} (χ : Ch p δ) : chv χ (1 : UF p) = 1 := by
  unfold chv
  rw [QuotientGroup.mk_one, ofMul_one]
  exact char_map_zero (Ch.toChar χ)

variable {p} in
private theorem chv_inv {δ : Γ} (χ : Ch p δ) (u : UF p) : chv χ u⁻¹ = (chv χ u)⁻¹ := by
  unfold chv
  rw [QuotientGroup.mk_inv, ofMul_inv]
  exact char_map_neg (Ch.toChar χ) _

variable {p} in
private theorem chv_ne_zero {δ : Γ} (χ : Ch p δ) (u : UF p) : chv χ u ≠ 0 := by
  intro h
  have h1 := chv_mul χ u u⁻¹
  rw [mul_inv_cancel, chv_one, h, zero_mul] at h1
  exact one_ne_zero h1

variable {p} in

private theorem chv_of_mem {δ : Γ} (χ : Ch p δ) {m : UF p} (hm : m ∈ Um p δ) : chv χ m = 1 := by
  unfold chv
  rw [(QuotientGroup.eq_one_iff m).mpr hm, ofMul_one]
  exact char_map_zero (Ch.toChar χ)

variable {p} in
private theorem chv_add {δ : Γ} (χ ρ : Ch p δ) (u : UF p) : chv (χ + ρ) u = chv χ u * chv ρ u :=
  char_add_apply (A := Additive (Qm p δ)) χ ρ _

variable {p} in
private theorem chv_neg {δ : Γ} (χ : Ch p δ) (u : UF p) : chv (-χ) u = (chv χ u)⁻¹ :=
  char_neg_apply (A := Additive (Qm p δ)) χ _

variable {p} in
private theorem chv_zero {δ : Γ} (u : UF p) : chv (0 : Ch p δ) u = 1 :=
  char_zero_apply (A := Additive (Qm p δ)) _

variable {p} in

private theorem ext_chv {δ : Γ} {χ ρ : Ch p δ} (h : ∀ u : UF p, chv χ u = chv ρ u) : χ = ρ := by
  apply char_ext (A := Additive (Qm p δ))
  intro a
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul a)
  have h1 := h u
  unfold chv Ch.toChar at h1
  rw [hu, ofMul_toMul] at h1
  exact h1

variable {p} in

private theorem sum_chv_eq {δ : Γ} (u : UF p) :
    ∑ χ : Ch p δ, chv χ u = if (u : Qm p δ) = 1 then (Fintype.card (Qm p δ) : ℂ) else 0 := by
  unfold chv
  rw [Fintype.card_congr (Additive.ofMul : Qm p δ ≃ Additive (Qm p δ))]
  split_ifs with h
  · exact char_sum_apply_of_eq_zero (A := Additive (Qm p δ)) (ofMul_eq_zero.mpr h)
  · exact char_sum_apply_of_ne_zero (A := Additive (Qm p δ)) (fun h' => h (ofMul_eq_zero.mp h'))

variable {p} in

private theorem sum_toChar_eq {δ : Γ} (χ : Ch p δ) :
    ∑ a : Additive (Qm p δ), Ch.toChar χ a = if χ = 0 then (Fintype.card (Qm p δ) : ℂ) else 0 := by
  rw [Fintype.card_congr (Additive.ofMul : Qm p δ ≃ Additive (Qm p δ))]
  split_ifs with h
  · exact char_sum_of_eq_zero (A := Additive (Qm p δ)) (by rw [h]; rfl)
  · exact char_sum_of_ne_zero (A := Additive (Qm p δ)) h

section fourier

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

private def IsLvl (δ : Γ) (f : UF p → X) : Prop := ∀ u : UF p, ∀ m ∈ Um p δ, f (u * m) = f u

private noncomputable def _root_.TwistedCoinvariantsAux.comp (δ : Γ) (f : UF p → X) (χ : Ch p δ) : X :=
  (Fintype.card (Qm p δ) : ℂ)⁻¹ • ∑ q : Qm p δ, chv χ (rep p δ q) • f (rep p δ q)

p2m_export "TwistedCoinvariantsAux" "comp"
private theorem size_Qm_ne_zero (δ : Γ) : (Fintype.card (Qm p δ) : ℂ) ≠ 0 := by
  exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Qm p δ) ≠ 0)

omit [AddCommGroup X] [Module ℂ X] in
private theorem apply_rep_mk_of_isLvl {δ : Γ} {f : UF p → X} (hf : IsLvl p δ f) (u : UF p) :
    f (rep p δ (u : Qm p δ)) = f u := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (Um p δ) u
  show f ((u : Qm p δ).out) = f u
  rw [hm]
  exact hf u m m.2

private theorem mk_mul_inv_eq_one_iff (δ : Γ) (q : Qm p δ) (u : UF p) :
    ((rep p δ q * u⁻¹ : UF p) : Qm p δ) = 1 ↔ q = (u : Qm p δ) := by
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mk_rep, mul_inv_eq_one]

private theorem chv_rep_mk {δ δ₁ : Γ} (hδ : δ ≤ δ₁) (χ : Ch p δ₁) (u : UF p) :
    chv χ (rep p δ (u : Qm p δ)) = chv χ u := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (Um p δ) u
  have hm₁ : (m : UF p) ∈ Um p δ₁ :=
    (mem_Um_iff p δ₁ m).mpr (((mem_Um_iff p δ m).mp m.2).trans_le (Units.val_le_val.mpr hδ))
  show chv χ ((u : Qm p δ).out) = chv χ u
  rw [hm, chv_mul, chv_of_mem χ hm₁, mul_one]

private noncomputable def chOfFun (δ : Γ) (f : UF p → ℂ) (hmul : ∀ u v : UF p, f (u * v) = f u * f v)
    (htriv : ∀ m ∈ Um p δ, f m = 1) : Ch p δ where
  toFun a := f (rep p δ (Additive.toMul a))
  map_zero_eq_one' := by
    show f (rep p δ (1 : Qm p δ)) = 1
    apply htriv
    rw [← QuotientGroup.eq_one_iff, mk_rep]
  map_add_eq_mul' a b := by
    show f (rep p δ (Additive.toMul a * Additive.toMul b)) =
      f (rep p δ (Additive.toMul a)) * f (rep p δ (Additive.toMul b))
    rw [← hmul]

    obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (Um p δ)
      (rep p δ (Additive.toMul a) * rep p δ (Additive.toMul b))
    have hclass : rep p δ (Additive.toMul a * Additive.toMul b) =
        ((rep p δ (Additive.toMul a) * rep p δ (Additive.toMul b) : UF p) : Qm p δ).out := by
      unfold rep
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq']
    rw [hclass, hm, hmul, htriv m m.2, mul_one]

private theorem chv_chOfFun (δ : Γ) (f : UF p → ℂ) (hmul : ∀ u v : UF p, f (u * v) = f u * f v)
    (htriv : ∀ m ∈ Um p δ, f m = 1) (u : UF p) : chv (chOfFun p δ f hmul htriv) u = f u := by
  show f (rep p δ (Additive.toMul (Additive.ofMul (u : Qm p δ)))) = f u
  rw [toMul_ofMul]
  obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (Um p δ) u
  show f ((u : Qm p δ).out) = f u
  rw [hm, hmul, htriv m m.2, mul_one]

private theorem Um_mono {δ δ₁ : Γ} (h : δ ≤ δ₁) : Um p δ ≤ Um p δ₁ := fun m hm =>
  ((mem_Um_iff p δ m).mp hm).trans_le (Units.val_le_val.mpr h)

private noncomputable def refineCh {δ δ₁ : Γ} (h : δ ≤ δ₁) (τ : Ch p δ₁) : Ch p δ :=
  chOfFun p δ (chv τ) (chv_mul τ) fun _ hm => chv_of_mem τ (Um_mono p h hm)

private theorem chv_refineCh {δ δ₁ : Γ} (h : δ ≤ δ₁) (τ : Ch p δ₁) (u : UF p) : chv (refineCh p h τ) u = chv τ u :=
  chv_chOfFun p δ _ _ _ u

private theorem sum_inv_chv_smul_comp {δ : Γ} {f : UF p → X} (hf : IsLvl p δ f) (u : UF p) :
    ∑ χ : Ch p δ, (chv χ u)⁻¹ • comp p δ f χ = f u := by
  have h1 : ∀ χ : Ch p δ, (chv χ u)⁻¹ • comp p δ f χ =
      (Fintype.card (Qm p δ) : ℂ)⁻¹ • ∑ q : Qm p δ, chv χ (rep p δ q * u⁻¹) • f (rep p δ q) := by
    intro χ
    unfold comp
    rw [smul_comm]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [smul_smul, chv_mul, chv_inv, mul_comm]
  have h2 : ∀ q : Qm p δ, (∑ χ : Ch p δ, chv χ (rep p δ q * u⁻¹)) • f (rep p δ q) =
      if q = (u : Qm p δ) then (Fintype.card (Qm p δ) : ℂ) • f (rep p δ q) else 0 := by
    intro q
    rw [sum_chv_eq, ite_smul, zero_smul]
    exact if_congr (mk_mul_inv_eq_one_iff p δ q u) rfl rfl
  calc ∑ χ : Ch p δ, (chv χ u)⁻¹ • comp p δ f χ
      = (Fintype.card (Qm p δ) : ℂ)⁻¹ •
          ∑ χ : Ch p δ, ∑ q : Qm p δ, chv χ (rep p δ q * u⁻¹) • f (rep p δ q) := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun χ _ => h1 χ
    _ = (Fintype.card (Qm p δ) : ℂ)⁻¹ •
          ∑ q : Qm p δ, (∑ χ : Ch p δ, chv χ (rep p δ q * u⁻¹)) • f (rep p δ q) := by
        rw [Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun q _ => (Finset.sum_smul).symm
    _ = (Fintype.card (Qm p δ) : ℂ)⁻¹ • ((Fintype.card (Qm p δ) : ℂ) • f (rep p δ (u : Qm p δ))) := by
        congr 1
        simp only [h2, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    _ = f u := by
        rw [smul_smul, inv_mul_cancel₀ (size_Qm_ne_zero p δ), one_smul, apply_rep_mk_of_isLvl p hf]

private theorem eq_zero_of_forall_comp_eq_zero {δ : Γ} {f : UF p → X} (hf : IsLvl p δ f)
    (h : ∀ χ : Ch p δ, comp p δ f χ = 0) (u : UF p) : f u = 0 := by
  rw [← sum_inv_chv_smul_comp p hf u]
  simp [h]

private theorem comp_add (δ : Γ) (f g : UF p → X) (χ : Ch p δ) :
    comp p δ (fun v => f v + g v) χ = comp p δ f χ + comp p δ g χ := by
  unfold comp
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun q _ => smul_add _ _ _

private theorem comp_sub (δ : Γ) (f g : UF p → X) (χ : Ch p δ) :
    comp p δ (fun v => f v - g v) χ = comp p δ f χ - comp p δ g χ := by
  unfold comp
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun q _ => smul_sub _ _ _

private theorem comp_const_smul (δ : Γ) (c : ℂ) (f : UF p → X) (χ : Ch p δ) :
    comp p δ (fun v => c • f v) χ = c • comp p δ f χ := by
  unfold comp
  rw [smul_comm]
  congr 1
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun q _ => smul_comm (chv χ (rep p δ q)) c (f (rep p δ q))

private theorem comp_smul_const (δ : Γ) (g : UF p → ℂ) (ξ : X) (χ : Ch p δ) :
    comp p δ (fun v => g v • ξ) χ = comp p δ g χ • ξ := by
  unfold comp
  rw [smul_assoc, Finset.sum_smul]
  congr 1
  exact Finset.sum_congr rfl fun q _ => (smul_assoc _ _ _).symm

private theorem comp_chv_smul (δ : Γ) (ρ : Ch p δ) (f : UF p → X) (χ : Ch p δ) :
    comp p δ (fun v => chv ρ v • f v) χ = comp p δ f (χ + ρ) := by
  unfold comp
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [smul_smul, chv_add]

private theorem comp_chv (δ : Γ) (ρ χ : Ch p δ) :
    comp p δ (fun v => chv ρ v) χ = if χ + ρ = 0 then 1 else 0 := by
  unfold comp
  have h : ∀ q : Qm p δ, chv χ (rep p δ q) • chv ρ (rep p δ q) = chv (χ + ρ) (rep p δ q) := by
    intro q
    rw [smul_eq_mul, chv_add]
  simp only [h]
  have h2 : ∑ q : Qm p δ, chv (χ + ρ) (rep p δ q) = ∑ a : Additive (Qm p δ), Ch.toChar (χ + ρ) a := by
    unfold chv
    simp only [mk_rep]
    exact Fintype.sum_equiv Additive.ofMul _ _ (fun _ => rfl)
  rw [h2, sum_toChar_eq]
  split_ifs
  · rw [smul_eq_mul, inv_mul_cancel₀ (size_Qm_ne_zero p δ)]
  · simp

private theorem comp_sum {ι : Type*} (δ : Γ) (s : Finset ι) (f : ι → UF p → X) (χ : Ch p δ) :
    comp p δ (fun v => ∑ i ∈ s, f i v) χ = ∑ i ∈ s, comp p δ (f i) χ := by
  unfold comp
  rw [← Finset.smul_sum]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => Finset.smul_sum

private theorem comp_zero (δ : Γ) (χ : Ch p δ) : comp p δ (fun _ : UF p => (0 : X)) χ = 0 := by
  unfold comp
  simp

omit [AddCommGroup X] [Module ℂ X] in

private theorem apply_eq_of_mk_eq_of_isLvl {δ : Γ} {f : UF p → X} (hf : IsLvl p δ f) {u v : UF p}
    (h : (u : Qm p δ) = (v : Qm p δ)) : f u = f v := by
  rw [QuotientGroup.eq] at h
  have hv : v = u * (u⁻¹ * v) := (mul_inv_cancel_left u v).symm
  rw [hv, hf u _ h]

private theorem chv_eq_of_mk_eq {δ δ₁ : Γ} (hδ : δ ≤ δ₁) (τ : Ch p δ₁) {u v : UF p}
    (h : (u : Qm p δ) = (v : Qm p δ)) : chv τ u = chv τ v := by
  rw [QuotientGroup.eq] at h
  have hv : v = u * (u⁻¹ * v) := (mul_inv_cancel_left u v).symm
  rw [hv, chv_mul, chv_of_mem τ (Um_mono p hδ h), mul_one]

private noncomputable def qmap {δ' δ : Γ} (h : δ' ≤ δ) : Qm p δ' →* Qm p δ :=
  QuotientGroup.map (Um p δ') (Um p δ) (MonoidHom.id (UF p)) fun _ hm => Um_mono p h hm

private theorem qmap_mk {δ' δ : Γ} (h : δ' ≤ δ) (u : UF p) : qmap p h (u : Qm p δ') = (u : Qm p δ) := rfl

private theorem qmap_surjective {δ' δ : Γ} (h : δ' ≤ δ) : Function.Surjective (qmap p h) := by
  intro q
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨(u : Qm p δ'), rfl⟩

private theorem comp_refineCh {δ' δ : Γ} (h : δ' ≤ δ) {f : UF p → X} (hf : IsLvl p δ f) (σ : Ch p δ) :
    comp p δ' f (refineCh p h σ) = comp p δ f σ := by
  classical
  unfold comp

  have hterm : ∀ q' : Qm p δ', chv (refineCh p h σ) (rep p δ' q') • f (rep p δ' q') =
      chv σ (rep p δ (qmap p h q')) • f (rep p δ (qmap p h q')) := by
    intro q'
    have hcl : ((rep p δ' q' : UF p) : Qm p δ) = ((rep p δ (qmap p h q') : UF p) : Qm p δ) := by
      rw [mk_rep, ← qmap_mk p h, mk_rep]
    rw [chv_refineCh, chv_eq_of_mk_eq p le_rfl σ hcl, apply_eq_of_mk_eq_of_isLvl p hf hcl]
  simp_rw [hterm]

  set nF : ℕ := (Finset.univ.filter fun q' : Qm p δ' => qmap p h q' = 1).card with hF
  have hfib : ∀ q : Qm p δ, (Finset.univ.filter fun q' : Qm p δ' => qmap p h q' = q).card = nF := by
    intro q
    exact MonoidHom.card_fiber_eq_of_mem_range (qmap p h) (qmap_surjective p h q) (qmap_surjective p h 1)
  have hsum : ∀ g : Qm p δ → X, ∑ q' : Qm p δ', g (qmap p h q') = ∑ q : Qm p δ, (nF : ℂ) • g q := by
    intro g
    rw [← Finset.sum_fiberwise' Finset.univ (qmap p h) g]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_const, hfib q, Nat.cast_smul_eq_nsmul]
  have hcard : (Fintype.card (Qm p δ') : ℂ) = (Fintype.card (Qm p δ) : ℂ) * nF := by
    have h1 : Fintype.card (Qm p δ') = Fintype.card (Qm p δ) * nF := by
      rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise fun q' _ => Finset.mem_univ (qmap p h q')]
      simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [h1, Nat.cast_mul]
  have hF0 : (nF : ℂ) ≠ 0 := by
    have : 0 < nF := by
      rw [hF, Finset.card_pos]
      obtain ⟨q₁, hq₁⟩ := qmap_surjective p h 1
      exact ⟨q₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq₁⟩⟩
    exact_mod_cast this.ne'
  rw [hsum fun q => chv σ (rep p δ q) • f (rep p δ q), ← Finset.smul_sum, smul_smul, hcard, mul_inv,
    mul_assoc, inv_mul_cancel₀ hF0, mul_one]

end fourier

section central

variable (S : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ))
  (hstab : ∀ W ∈ S, ∀ k : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p), (fun g => W (g * k)) ∈ S)
  (hsm : ∀ W ∈ S, ∃ K : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
    IsOpen (K : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) ∧ ∀ k ∈ K, (fun g => W (g * k)) = W)
  (hirr : ∀ T : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ), T ≤ S →
    (∀ W ∈ T, ∀ k : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p), (fun g => W (g * k)) ∈ T) → T = ⊥ ∨ T = S)
  (hadm : ∀ K : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
    IsOpen (K : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) →
    ∀ T : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ), T ≤ S →
      (∀ W ∈ T, ∀ k ∈ K, (fun g => W (g * k)) = W) → FiniteDimensional ℂ T)

include hstab hsm hirr hadm in

private theorem exists_central_scalar (c : Fx) : ∃ ω : ℂ, ∀ W ∈ S, rT p (zG p c) W = ω • W := by
  refine AutomorphicForm.LocalFunctionSpace.exists_smul_eq_of_irreducible_of_admissible p S hstab hsm hirr hadm
    (rT p (zG p c)) (fun W hW => hstab W hW _) ?_
  intro W _ k
  funext g
  simp only [rT_apply]
  rw [mul_assoc, mul_assoc, zG_mul_comm]

private noncomputable def omega (c : Fx) : ℂ :=
  Classical.choose (exists_central_scalar p S hstab hsm hirr hadm c)

private theorem rT_zG_eq (c : Fx) {W : G → ℂ} (hW : W ∈ S) :
    rT p (zG p c) W = omega p S hstab hsm hirr hadm c • W :=
  Classical.choose_spec (exists_central_scalar p S hstab hsm hirr hadm c) W hW

private noncomputable def kirillov (V : G → ℂ) (a : Fx) : (G → ℂ) ⧸ defectSpan p S :=
  (defectSpan p S).mkQ (rT p (dg p a) V)

private noncomputable def theta (V : G → ℂ) : (G → ℂ) ⧸ defectSpan p S :=
  (defectSpan p S).mkQ (rT p (wG p) V)

private theorem mkQ_rT_unipotent {U : G → ℂ} (hU : U ∈ S) (x : F) :
    (defectSpan p S).mkQ (rT p (unipotentGL2 x) U) =
      NumberField.StandardAddChar.psiV p x • (defectSpan p S).mkQ U := by
  rw [← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  refine Submodule.subset_span ?_
  simp only [defectSet, Set.mem_setOf_eq]
  exact ⟨U, hU, x, rfl⟩

include hstab in
private theorem kirillov_rT_unipotent {V : G → ℂ} (hV : V ∈ S) (x : F) (a : Fx) :
    kirillov p S (rT p (unipotentGL2 x) V) a =
      NumberField.StandardAddChar.psiV p ((a : F) * x) • kirillov p S V a := by
  unfold kirillov
  rw [rT_rT, dg_mul_unipotent, ← rT_rT, mkQ_rT_unipotent p S (U := rT p (dg p a) V) (hstab V hV _)]

private theorem kirillov_rT_dg (V : G → ℂ) (b a : Fx) : kirillov p S (rT p (dg p b) V) a = kirillov p S V (a * b) := by
  unfold kirillov
  rw [rT_rT, dg_mul]

include hstab hsm hirr hadm in
private theorem kirillov_rT_zG {V : G → ℂ} (hV : V ∈ S) (c a : Fx) :
    kirillov p S (rT p (zG p c) V) a = omega p S hstab hsm hirr hadm c • kirillov p S V a := by
  unfold kirillov
  rw [rT_zG_eq p S hstab hsm hirr hadm c hV, map_smul, map_smul]

include hstab hsm hirr hadm in

private theorem kirillov_rT_wG {V : G → ℂ} (hV : V ∈ S) (a : Fx) :
    kirillov p S (rT p (wG p) V) a = omega p S hstab hsm hirr hadm a • theta p S (rT p (dg p a⁻¹) V) := by
  unfold kirillov theta
  rw [rT_rT, dg_mul_wG, mul_assoc, ← rT_rT, ← rT_rT,
    rT_zG_eq p S hstab hsm hirr hadm a (W := rT p (dg p a⁻¹) V) (hstab V hV _), map_smul, map_smul]

private theorem kirillov_one (V : G → ℂ) : kirillov p S V 1 = (defectSpan p S).mkQ V := by
  unfold kirillov
  rw [dg_one, rT_one]

include hstab hsm hirr hadm in
private theorem omega_mul (hS : S ≠ ⊥) (c d : Fx) :
    omega p S hstab hsm hirr hadm (c * d) = omega p S hstab hsm hirr hadm c * omega p S hstab hsm hirr hadm d := by
  obtain ⟨W, hW, hW0⟩ := (Submodule.ne_bot_iff S).mp hS
  have h1 := rT_zG_eq p S hstab hsm hirr hadm (c * d) hW
  have h2 : rT p (zG p (c * d)) W =
      (omega p S hstab hsm hirr hadm c * omega p S hstab hsm hirr hadm d) • W := by
    rw [zG_mul, ← rT_rT, rT_zG_eq p S hstab hsm hirr hadm d hW, map_smul, rT_zG_eq p S hstab hsm hirr hadm c hW,
      smul_smul, mul_comm]
  exact smul_left_injective ℂ hW0 (h1.symm.trans h2)

include hstab hsm hirr hadm in
private theorem omega_one (hS : S ≠ ⊥) : omega p S hstab hsm hirr hadm 1 = 1 := by
  obtain ⟨W, hW, hW0⟩ := (Submodule.ne_bot_iff S).mp hS
  have h1 := rT_zG_eq p S hstab hsm hirr hadm 1 hW
  rw [zG_one, rT_one] at h1
  exact (smul_left_injective ℂ hW0 (h1.symm.trans (one_smul ℂ W).symm))

include hstab hsm hirr hadm in
private theorem omega_ne_zero (hS : S ≠ ⊥) (c : Fx) : omega p S hstab hsm hirr hadm c ≠ 0 := by
  have h := omega_mul p S hstab hsm hirr hadm hS c c⁻¹
  rw [mul_inv_cancel, omega_one p S hstab hsm hirr hadm hS] at h
  exact left_ne_zero_of_mul_eq_one h.symm

include hstab hsm hirr hadm in

private theorem exists_forall_omega_eq_one (hS : S ≠ ⊥) :
    ∃ δ : Γ, ∀ c : Fx, Valued.v ((c : F) - 1) < (δ : WithZero (Multiplicative ℤ)) →
      omega p S hstab hsm hirr hadm c = 1 := by
  obtain ⟨W, hW, hW0⟩ := (Submodule.ne_bot_iff S).mp hS
  obtain ⟨K, hKo, hKW⟩ := hsm W hW
  obtain ⟨δ, hδ⟩ := exists_zG_mem_of_isOpen p K hKo
  refine ⟨δ, fun c hc => ?_⟩
  have h1 := rT_zG_eq p S hstab hsm hirr hadm c hW
  have h2 : rT p (zG p c) W = W := hKW _ (hδ c hc)
  rw [h2] at h1
  exact smul_left_injective ℂ hW0 (h1.symm.trans (one_smul ℂ W).symm)

include hsm in

private theorem exists_forall_kirillov_mul_eq {V : G → ℂ} (hV : V ∈ S) :
    ∃ δ : Γ, ∀ (a u : Fx), Valued.v ((u : F) - 1) < (δ : WithZero (Multiplicative ℤ)) →
      kirillov p S V (a * u) = kirillov p S V a := by
  obtain ⟨K, hKo, hKV⟩ := hsm V hV
  obtain ⟨δ, hδ⟩ := exists_dg_mem_of_isOpen p K hKo
  refine ⟨δ, fun a u hu => ?_⟩
  rw [← kirillov_rT_dg]
  have h : rT p (dg p u) V = V := hKV _ (hδ u hu)
  rw [h]

include hstab hsm in

private theorem exists_forall_kirillov_eq_zero {V : G → ℂ} (hV : V ∈ S) :
    ∃ β : Γ, ∀ a : Fx, (β : WithZero (Multiplicative ℤ)) ≤ Valued.v (a : F) → kirillov p S V a = 0 := by
  obtain ⟨K, hKo, hKV⟩ := hsm V hV
  obtain ⟨δ, hδ⟩ := exists_unipotent_mem_of_isOpen p K hKo
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : F, NumberField.StandardAddChar.psiV p x₀ ≠ 1 :=
    ⟨_, NumberField.StandardAddChar.psiV_algebraMap_inv_ne_one p⟩
  have hx₀0 : x₀ ≠ 0 := by
    rintro rfl
    exact hx₀ (AddChar.map_zero_eq_one _)
  set vx : Γ := Units.mk0 (Valued.v x₀) ((Valuation.ne_zero_iff _).mpr hx₀0) with hvx
  obtain ⟨g, hg⟩ := exists_unit_gt p (1 : F)
  have hg1 : (1 : Γ) < g := by
    rw [← Units.val_lt_val]
    simpa using hg
  refine ⟨δ⁻¹ * vx * g, fun a ha => ?_⟩
  set ua : Γ := Units.mk0 (Valued.v (a : F)) ((Valuation.ne_zero_iff _).mpr a.ne_zero) with hua
  have hβa : δ⁻¹ * vx * g ≤ ua := by
    rw [← Units.val_le_val]
    simpa [hua] using ha

  have hy : Valued.v (x₀ * (a : F)⁻¹) < (δ : WithZero (Multiplicative ℤ)) := by
    have hlt : vx * ua⁻¹ < δ := by
      rw [mul_inv_lt_iff_lt_mul]
      calc vx < vx * g := lt_mul_of_one_lt_right' vx hg1
        _ = δ * (δ⁻¹ * vx * g) := by rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
        _ ≤ δ * ua := mul_le_mul_right hβa δ
    have hval : Valued.v (x₀ * (a : F)⁻¹) = ((vx * ua⁻¹ : Γ) : WithZero (Multiplicative ℤ)) := by
      rw [map_mul, map_inv₀, Units.val_mul, Units.val_inv_eq_inv_val, hvx, hua, Units.val_mk0, Units.val_mk0]
    rw [hval, Units.val_lt_val]
    exact hlt
  have hfix : rT p (unipotentGL2 (x₀ * (a : F)⁻¹)) V = V := hKV _ (hδ _ hy)
  have h := kirillov_rT_unipotent p S hstab hV (x₀ * (a : F)⁻¹) a
  rw [hfix] at h
  have hax : (a : F) * (x₀ * (a : F)⁻¹) = x₀ := by
    rw [mul_comm x₀, ← mul_assoc, mul_inv_cancel₀ a.ne_zero, one_mul]
  rw [hax] at h
  have h0 : (NumberField.StandardAddChar.psiV p x₀ - 1) • kirillov p S V a = 0 := by
    rw [sub_smul, one_smul, ← h, sub_self]
  exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hx₀)

end central

section kirillov

variable (S : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ))
  (hstab : ∀ W ∈ S, ∀ k : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p), (fun g => W (g * k)) ∈ S)
  (hsm : ∀ W ∈ S, ∃ K : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
    IsOpen (K : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) ∧ ∀ k ∈ K, (fun g => W (g * k)) = W)
  (ϖ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ)
  (hϖ : Valued.v (ϖ : HeightOneSpectrum.adicCompletion ℚ p) = WithZero.exp (-1 : ℤ))

private theorem kirillov_add (V W : G → ℂ) (a : Fx) :
    kirillov p S (V + W) a = kirillov p S V a + kirillov p S W a := by
  unfold kirillov
  rw [map_add, map_add]

private theorem kirillov_smul (c : ℂ) (V : G → ℂ) (a : Fx) : kirillov p S (c • V) a = c • kirillov p S V a := by
  unfold kirillov
  rw [map_smul, map_smul]

private theorem kirillov_sum {ι : Type*} (s : Finset ι) (f : ι → G → ℂ) (a : Fx) :
    kirillov p S (∑ i ∈ s, f i) a = ∑ i ∈ s, kirillov p S (f i) a := by
  have h : kirillov p S (∑ i ∈ s, f i) a = ((defectSpan p S).mkQ.comp (rT p (dg p a))) (∑ i ∈ s, f i) := rfl
  rw [h, map_sum]
  rfl

include hϖ in
private theorem v_pi_zpow (n : ℤ) : Valued.v (((ϖ ^ n : Fx) : F)) = WithZero.exp (-n) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one]

include hϖ in
private theorem v_pi_zpow_ne (n : ℤ) : Valued.v (((ϖ ^ n : Fx) : F)) ≠ 0 := by
  rw [v_pi_zpow p ϖ hϖ]
  exact WithZero.exp_ne_zero

include hϖ in

private theorem eq_of_v_sub_lt {k n : ℤ} (u r : UF p) {δ : Γ} (hδ : δ ≤ 1)
    (h : Valued.v (((ϖ ^ k * (u : Fx) : Fx) : F) - ((ϖ ^ n * (r : Fx) : Fx) : F)) <
      (δ : WithZero (Multiplicative ℤ)) * Valued.v (((ϖ ^ n : Fx) : F))) : k = n := by
  have hδ' : (δ : WithZero (Multiplicative ℤ)) ≤ 1 := Units.val_le_val.mpr hδ
  have hvn : Valued.v (((ϖ ^ n * (r : Fx) : Fx) : F)) = Valued.v (((ϖ ^ n : Fx) : F)) := by
    rw [Units.val_mul, map_mul, v_coe_UF, mul_one]
  have hvk : Valued.v (((ϖ ^ k * (u : Fx) : Fx) : F)) = Valued.v (((ϖ ^ k : Fx) : F)) := by
    rw [Units.val_mul, map_mul, v_coe_UF, mul_one]
  have hlt : Valued.v (((ϖ ^ k * (u : Fx) : Fx) : F) - ((ϖ ^ n * (r : Fx) : Fx) : F)) <
      Valued.v (((ϖ ^ n * (r : Fx) : Fx) : F)) := by
    rw [hvn]
    refine h.trans_le ?_
    calc (δ : WithZero (Multiplicative ℤ)) * Valued.v (((ϖ ^ n : Fx) : F))
        ≤ 1 * Valued.v (((ϖ ^ n : Fx) : F)) := mul_le_mul_left hδ' _
      _ = _ := one_mul _

  have heq : Valued.v (((ϖ ^ k * (u : Fx) : Fx) : F)) = Valued.v (((ϖ ^ n * (r : Fx) : Fx) : F)) := by
    have e : ((ϖ ^ k * (u : Fx) : Fx) : F) =
        (((ϖ ^ k * (u : Fx) : Fx) : F) - ((ϖ ^ n * (r : Fx) : Fx) : F)) + ((ϖ ^ n * (r : Fx) : Fx) : F) := by ring
    rw [e, Valuation.map_add_eq_of_lt_right _ hlt]
  rw [hvk, hvn, v_pi_zpow p ϖ hϖ, v_pi_zpow p ϖ hϖ] at heq
  exact neg_injective (WithZero.exp_injective heq)

private theorem v_sub_lt_iff_mk_eq (δ : Γ) (u r : UF p) :
    Valued.v (((u : Fx) : F) - ((r : Fx) : F)) < (δ : WithZero (Multiplicative ℤ)) ↔ (u : Qm p δ) = (r : Qm p δ) := by
  constructor
  · intro h
    exact mk_eq_mk_of_close p δ r u h
  · intro h
    rw [eq_comm, QuotientGroup.eq, mem_Um_iff] at h
    have e : ((u : Fx) : F) - ((r : Fx) : F) = ((r : Fx) : F) * ((((r⁻¹ * u : UF p) : Fx) : F) - 1) := by
      have h1 : ((r : Fx) : F) * (((r⁻¹ : UF p) : Fx) : F) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
      rw [Subgroup.coe_mul, Units.val_mul, mul_sub, mul_one, ← mul_assoc, h1, one_mul]
    rw [e, map_mul, v_coe_UF, one_mul]
    exact h

private noncomputable def shell (V : G → ℂ) (n : ℤ) (u : UF p) : (G → ℂ) ⧸ defectSpan p S :=
  kirillov p S V (ϖ ^ n * (u : Fx))

private noncomputable def mel (δ : Γ) (V : G → ℂ) (n : ℤ) (χ : Ch p δ) : (G → ℂ) ⧸ defectSpan p S :=
  comp p δ (shell p S ϖ V n) χ

include hsm in

private theorem exists_forall_isLvl_shell {V : G → ℂ} (hV : V ∈ S) :
    ∃ δ₀ : Γ, ∀ δ : Γ, δ ≤ δ₀ → ∀ n : ℤ, IsLvl p δ (shell p S ϖ V n) := by
  obtain ⟨δ₀, hδ₀⟩ := exists_forall_kirillov_mul_eq p S hsm hV
  refine ⟨δ₀, fun δ hδ n u m hm => ?_⟩
  unfold shell
  rw [Subgroup.coe_mul, ← mul_assoc]
  apply hδ₀
  exact (mem_Um_iff p δ m).mp hm |>.trans_le (Units.val_le_val.mpr hδ)

private theorem shell_add (V W : G → ℂ) (n : ℤ) (u : UF p) :
    shell p S ϖ (V + W) n u = shell p S ϖ V n u + shell p S ϖ W n u := kirillov_add p S V W _

private theorem shell_smul (c : ℂ) (V : G → ℂ) (n : ℤ) (u : UF p) :
    shell p S ϖ (c • V) n u = c • shell p S ϖ V n u := kirillov_smul p S c V _

private theorem shell_sum {ι : Type*} (s : Finset ι) (f : ι → G → ℂ) (n : ℤ) (u : UF p) :
    shell p S ϖ (∑ i ∈ s, f i) n u = ∑ i ∈ s, shell p S ϖ (f i) n u := kirillov_sum p S s f _

include hstab hsm in

private theorem exists_cut {V : G → ℂ} (hV : V ∈ S) (a₀ : F) (δ : Γ) :
    ∃ V' ∈ S, ∀ a : Fx, kirillov p S V' a =
      if Valued.v ((a : F) - a₀) < (δ : WithZero (Multiplicative ℤ)) then kirillov p S V a else 0 := by
  obtain ⟨V', hV'S, h⟩ :=
    AutomorphicForm.LocalFunctionSpace.exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span p S hstab V hV
      (hsm V hV) a₀ δ
  refine ⟨V', hV'S, fun a => ?_⟩
  obtain ⟨h1, h2⟩ := h (dg p a) (by simp) (by simp) (by simp)
  have e : (dg p a : Matrix (Fin 2) (Fin 2) F) 0 0 = (a : F) := by simp
  rw [e] at h1 h2
  split_ifs with ha
  · unfold kirillov
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact h1 ha
  · unfold kirillov
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact h2 ha

include hstab hsm hϖ in

private theorem exists_charBump {V₀ : G → ℂ} (hV₀ : V₀ ∈ S) (n : ℤ) {δ₁ : Γ} (χ : Ch p δ₁) :
    ∃ E ∈ S, (∀ u : UF p, shell p S ϖ E n u = chv χ u • (defectSpan p S).mkQ V₀) ∧
      ∀ k : ℤ, k ≠ n → ∀ u : UF p, shell p S ϖ E k u = 0 := by
  obtain ⟨δ₀, hδ₀⟩ := exists_forall_kirillov_mul_eq p S hsm hV₀

  set δ : Γ := min (min δ₀ δ₁) 1 with hδdef
  have hδ0 : δ ≤ δ₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hδ1 : δ ≤ δ₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hδle1 : δ ≤ 1 := min_le_right _ _

  set ρ : Γ := δ * Units.mk0 (Valued.v (((ϖ ^ n : Fx) : F))) (v_pi_zpow_ne p ϖ hϖ n) with hρdef
  have hρval : (ρ : WithZero (Multiplicative ℤ)) =
      (δ : WithZero (Multiplicative ℤ)) * Valued.v (((ϖ ^ n : Fx) : F)) := by
    rw [hρdef, Units.val_mul, Units.val_mk0]

  have hbump : ∀ q : Qm p δ, ∃ B ∈ S, ∀ (k : ℤ) (u : UF p), shell p S ϖ B k u =
      if k = n ∧ (u : Qm p δ) = q then (defectSpan p S).mkQ V₀ else 0 := by
    intro q
    set c : Fx := ϖ ^ n * (rep p δ q : Fx) with hcdef
    obtain ⟨B, hBS, hB⟩ := exists_cut p S hstab hsm (hstab V₀ hV₀ (dg p c⁻¹)) (c : F) ρ
    refine ⟨B, hBS, fun k u => ?_⟩
    unfold shell
    rw [hB]
    have hkir : kirillov p S (fun g => V₀ (g * dg p c⁻¹)) (ϖ ^ k * (u : Fx)) =
        kirillov p S V₀ (ϖ ^ k * (u : Fx) * c⁻¹) :=
      kirillov_rT_dg p S V₀ c⁻¹ _
    rw [hkir, hρval]
    by_cases hk : k = n
    · rw [hk]
      by_cases hq : (u : Qm p δ) = q
      · rw [if_pos (show n = n ∧ (u : Qm p δ) = q from ⟨rfl, hq⟩), if_pos]
        ·
          have hmem : (rep p δ q)⁻¹ * u ∈ Um p δ := by
            rw [← QuotientGroup.eq, mk_rep]
            exact hq.symm
          have harg : ϖ ^ n * (u : Fx) * c⁻¹ = 1 * (((rep p δ q)⁻¹ * u : UF p) : Fx) := by
            rw [hcdef, one_mul, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev,
              mul_comm ((rep p δ q : Fx))⁻¹ (ϖ ^ n)⁻¹, mul_comm (ϖ ^ n) (u : Fx), mul_assoc, mul_inv_cancel_left,
              mul_comm]
          rw [harg, hδ₀ 1 _ (((mem_Um_iff p δ _).mp hmem).trans_le (Units.val_le_val.mpr hδ0)), kirillov_one]
        ·
          have hclose := (v_sub_lt_iff_mk_eq p δ u (rep p δ q)).mpr (by rw [hq, mk_rep])
          have e : ((ϖ ^ n * (u : Fx) : Fx) : F) - (c : F) =
              ((ϖ ^ n : Fx) : F) * (((u : Fx) : F) - ((rep p δ q : Fx) : F)) := by
            rw [hcdef, Units.val_mul, Units.val_mul, mul_sub]
          rw [e, map_mul, mul_comm]
          exact mul_lt_mul_of_pos_right hclose (zero_lt_iff.mpr (v_pi_zpow_ne p ϖ hϖ n))
      · rw [if_neg (show ¬ (n = n ∧ (u : Qm p δ) = q) from fun h => hq h.2), ite_eq_right_iff]
        intro hlt
        exfalso
        apply hq
        have e : ((ϖ ^ n * (u : Fx) : Fx) : F) - (c : F) =
            ((ϖ ^ n : Fx) : F) * (((u : Fx) : F) - ((rep p δ q : Fx) : F)) := by
          rw [hcdef, Units.val_mul, Units.val_mul, mul_sub]
        rw [e, map_mul, mul_comm] at hlt
        have hclose : Valued.v (((u : Fx) : F) - ((rep p δ q : Fx) : F)) < (δ : WithZero (Multiplicative ℤ)) :=
          lt_of_mul_lt_mul_right hlt zero_le
        rw [(v_sub_lt_iff_mk_eq p δ u (rep p δ q)).mp hclose, mk_rep]
    · rw [if_neg (show ¬ (k = n ∧ (u : Qm p δ) = q) from fun h => hk h.1), ite_eq_right_iff]
      intro hlt
      exfalso
      rw [hcdef] at hlt
      exact hk (eq_of_v_sub_lt p ϖ hϖ u (rep p δ q) hδle1 hlt)
  choose B hBS hB using hbump
  refine ⟨∑ q : Qm p δ, chv χ (rep p δ q) • B q, Submodule.sum_mem _ fun q _ => S.smul_mem _ (hBS q), ?_, ?_⟩
  · intro u
    rw [shell_sum]
    simp only [shell_smul, hB, true_and, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [chv_rep_mk p hδ1]
  · intro k hk u
    rw [shell_sum]
    simp only [shell_smul, hB, hk, false_and, if_false, smul_zero, Finset.sum_const_zero]

end kirillov

section operators

variable (S : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ))
  (hstab : ∀ W ∈ S, ∀ k : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p), (fun g => W (g * k)) ∈ S)
  (hsm : ∀ W ∈ S, ∃ K : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
    IsOpen (K : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) ∧ ∀ k ∈ K, (fun g => W (g * k)) = W)
  (hpsi : ∀ W ∈ S, ∀ (x : HeightOneSpectrum.adicCompletion ℚ p)
    (g : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
    W (unipotentGL2 x * g) = NumberField.StandardAddChar.psiV p x * W g)
  (hirr : ∀ T : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ), T ≤ S →
    (∀ W ∈ T, ∀ k : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p), (fun g => W (g * k)) ∈ T) → T = ⊥ ∨ T = S)
  (hadm : ∀ K : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
    IsOpen (K : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) →
    ∀ T : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ), T ≤ S →
      (∀ W ∈ T, ∀ k ∈ K, (fun g => W (g * k)) = W) → FiniteDimensional ℂ T)
  (ϖ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ)
  (hϖ : Valued.v (ϖ : HeightOneSpectrum.adicCompletion ℚ p) = WithZero.exp (-1 : ℤ))

include hϖ in

private theorem exists_shell_decomp (a : Fx) : ∃ (k : ℤ) (u : UF p), a = ϖ ^ k * (u : Fx) := by
  have hva : Valued.v (a : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr a.ne_zero
  set k : ℤ := -WithZero.log (Valued.v (a : F)) with hk
  have hvk : Valued.v (((ϖ ^ k : Fx) : F)) = Valued.v (a : F) := by
    rw [v_pi_zpow p ϖ hϖ, hk, neg_neg, WithZero.exp_log hva]
  have hu : Valued.v ((((ϖ ^ k)⁻¹ * a : Fx) : F)) = 1 := by
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hvk, inv_mul_cancel₀ hva]
  exact ⟨k, ⟨(ϖ ^ k)⁻¹ * a, hu⟩, (mul_inv_cancel_left (ϖ ^ k) a).symm⟩

private theorem shell_sub (V W : G → ℂ) (n : ℤ) (u : UF p) :
    shell p S ϖ (V - W) n u = shell p S ϖ V n u - shell p S ϖ W n u := by
  unfold shell kirillov
  rw [map_sub, map_sub]

include hsm hpsi hϖ in

private theorem eq_zero_of_forall_shell_eq_zero {V : G → ℂ} (hV : V ∈ S)
    (h : ∀ (k : ℤ) (u : UF p), shell p S ϖ V k u = 0) : V = 0 := by
  refine AutomorphicForm.LocalFunctionSpace.eq_zero_of_forall_diagonal_mul_mem_span_sub p S hsm V (hpsi V hV) ?_
  intro t h01 h10 h11
  have hdet : (t : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    have hu := (Matrix.isUnits_det_units t).ne_zero
    rwa [Matrix.det_fin_two, h01, h11, mul_one, zero_mul, sub_zero] at hu
  have ht : t = dg p (Units.mk0 _ hdet) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10, h11]
  obtain ⟨k, u, hku⟩ := exists_shell_decomp p ϖ hϖ (Units.mk0 _ hdet)
  have hk : kirillov p S V (Units.mk0 _ hdet) = 0 := by
    rw [hku]
    exact h k u
  unfold kirillov at hk
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hk
  rw [ht]
  exact hk

include hsm hpsi hϖ in

private theorem eq_of_forall_shell_eq {V W : G → ℂ} (hV : V ∈ S) (hW : W ∈ S)
    (h : ∀ (k : ℤ) (u : UF p), shell p S ϖ V k u = shell p S ϖ W k u) : V = W := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_shell_eq_zero p S hsm hpsi ϖ hϖ (S.sub_mem hV hW) fun k u => ?_
  rw [shell_sub, h, sub_self]

include hstab hsm hϖ in

private theorem exists_bump {δ : Γ} (n : ℤ) (τ : Ch p δ) (ξ : coinv p S) :
    ∃ E ∈ S, (∀ u : UF p, shell p S ϖ E n u = chv τ u • (ξ : (G → ℂ) ⧸ defectSpan p S)) ∧
      ∀ k : ℤ, k ≠ n → ∀ u : UF p, shell p S ϖ E k u = 0 := by
  obtain ⟨V₀, hV₀, hξ⟩ := Submodule.mem_map.mp ξ.2
  obtain ⟨E, hE, h1, h2⟩ := exists_charBump p S hstab hsm ϖ hϖ hV₀ n τ
  exact ⟨E, hE, fun u => by rw [h1 u, hξ], h2⟩

private noncomputable def bump {δ : Γ} (n : ℤ) (τ : Ch p δ) (ξ : coinv p S) : G → ℂ :=
  Classical.choose (exists_bump p S hstab hsm ϖ hϖ n τ ξ)

private theorem bump_mem {δ : Γ} (n : ℤ) (τ : Ch p δ) (ξ : coinv p S) : bump p S hstab hsm ϖ hϖ n τ ξ ∈ S :=
  (Classical.choose_spec (exists_bump p S hstab hsm ϖ hϖ n τ ξ)).1

private theorem shell_bump_self {δ : Γ} (n : ℤ) (τ : Ch p δ) (ξ : coinv p S) (u : UF p) :
    shell p S ϖ (bump p S hstab hsm ϖ hϖ n τ ξ) n u = chv τ u • (ξ : (G → ℂ) ⧸ defectSpan p S) :=
  (Classical.choose_spec (exists_bump p S hstab hsm ϖ hϖ n τ ξ)).2.1 u

private theorem shell_bump_of_ne {δ : Γ} (n : ℤ) (τ : Ch p δ) (ξ : coinv p S) {k : ℤ} (hk : k ≠ n) (u : UF p) :
    shell p S ϖ (bump p S hstab hsm ϖ hϖ n τ ξ) k u = 0 :=
  (Classical.choose_spec (exists_bump p S hstab hsm ϖ hϖ n τ ξ)).2.2 k hk u

private theorem shell_bump {δ : Γ} (n : ℤ) (τ : Ch p δ) (ξ : coinv p S) (k : ℤ) (u : UF p) :
    shell p S ϖ (bump p S hstab hsm ϖ hϖ n τ ξ) k u =
      if k = n then chv τ u • (ξ : (G → ℂ) ⧸ defectSpan p S) else 0 := by
  split_ifs with hk
  · subst hk
    exact shell_bump_self p S hstab hsm ϖ hϖ _ τ ξ u
  · exact shell_bump_of_ne p S hstab hsm ϖ hϖ n τ ξ hk u

include hpsi in

private theorem eq_bump_of_forall_shell {δ : Γ} (n : ℤ) (τ : Ch p δ) (ξ : coinv p S) {E : G → ℂ} (hE : E ∈ S)
    (h : ∀ (k : ℤ) (u : UF p), shell p S ϖ E k u =
      if k = n then chv τ u • (ξ : (G → ℂ) ⧸ defectSpan p S) else 0) :
    E = bump p S hstab hsm ϖ hϖ n τ ξ :=
  eq_of_forall_shell_eq p S hsm hpsi ϖ hϖ hE (bump_mem p S hstab hsm ϖ hϖ n τ ξ) fun k u => by
    rw [h, shell_bump]

include hpsi in
private theorem bump_add {δ : Γ} (n : ℤ) (τ : Ch p δ) (ξ η : coinv p S) :
    bump p S hstab hsm ϖ hϖ n τ (ξ + η) = bump p S hstab hsm ϖ hϖ n τ ξ + bump p S hstab hsm ϖ hϖ n τ η := by
  symm
  refine eq_bump_of_forall_shell p S hstab hsm hpsi ϖ hϖ n τ (ξ + η)
    (S.add_mem (bump_mem p S hstab hsm ϖ hϖ n τ ξ) (bump_mem p S hstab hsm ϖ hϖ n τ η)) fun k u => ?_
  rw [shell_add, shell_bump, shell_bump, Submodule.coe_add, smul_add]
  split_ifs <;> simp

include hpsi in
private theorem bump_smul {δ : Γ} (n : ℤ) (τ : Ch p δ) (c : ℂ) (ξ : coinv p S) :
    bump p S hstab hsm ϖ hϖ n τ (c • ξ) = c • bump p S hstab hsm ϖ hϖ n τ ξ := by
  symm
  refine eq_bump_of_forall_shell p S hstab hsm hpsi ϖ hϖ n τ (c • ξ)
    (S.smul_mem c (bump_mem p S hstab hsm ϖ hϖ n τ ξ)) fun k u => ?_
  rw [shell_smul, shell_bump, Submodule.coe_smul, smul_comm]
  split_ifs <;> simp

include hstab in

private theorem theta_mem {V : G → ℂ} (hV : V ∈ S) : theta p S V ∈ coinv p S :=
  Submodule.mem_map_of_mem (hstab V hV (wG p))

private noncomputable def Cop {δ : Γ} (n : ℤ) (τ : Ch p δ) : coinv p S →ₗ[ℂ] coinv p S where
  toFun ξ := ⟨theta p S (bump p S hstab hsm ϖ hϖ n τ ξ), theta_mem p S hstab (bump_mem p S hstab hsm ϖ hϖ n τ ξ)⟩
  map_add' ξ η := by
    apply Subtype.ext
    show theta p S (bump p S hstab hsm ϖ hϖ n τ (ξ + η)) = theta p S (bump p S hstab hsm ϖ hϖ n τ ξ) +
      theta p S (bump p S hstab hsm ϖ hϖ n τ η)
    rw [bump_add p S hstab hsm hpsi]
    unfold theta
    rw [map_add, map_add]
  map_smul' c ξ := by
    apply Subtype.ext
    show theta p S (bump p S hstab hsm ϖ hϖ n τ (c • ξ)) = c • theta p S (bump p S hstab hsm ϖ hϖ n τ ξ)
    rw [bump_smul p S hstab hsm hpsi]
    unfold theta
    rw [map_smul, map_smul]

private theorem Cop_apply_coe {δ : Γ} (n : ℤ) (τ : Ch p δ) (ξ : coinv p S) :
    ((Cop p S hstab hsm hpsi ϖ hϖ n τ ξ : coinv p S) : (G → ℂ) ⧸ defectSpan p S) =
      theta p S (bump p S hstab hsm ϖ hϖ n τ ξ) := rfl

include hpsi in

private theorem rT_dg_bump {δ : Γ} (n : ℤ) (τ : Ch p δ) (ξ : coinv p S) (m : ℤ) (v : UF p) :
    rT p (dg p (ϖ ^ m * (v : Fx))) (bump p S hstab hsm ϖ hϖ n τ ξ) =
      chv τ v • bump p S hstab hsm ϖ hϖ (n - m) τ ξ := by
  refine eq_of_forall_shell_eq p S hsm hpsi ϖ hϖ (hstab _ (bump_mem p S hstab hsm ϖ hϖ n τ ξ) _)
    (S.smul_mem _ (bump_mem p S hstab hsm ϖ hϖ (n - m) τ ξ)) fun k u => ?_
  rw [shell_smul, shell_bump]
  unfold shell
  rw [kirillov_rT_dg]
  have e : ϖ ^ k * (u : Fx) * (ϖ ^ m * (v : Fx)) = ϖ ^ (k + m) * ((u * v : UF p) : Fx) := by
    rw [zpow_add, Subgroup.coe_mul]
    rw [mul_mul_mul_comm]
  rw [e]
  have h := shell_bump p S hstab hsm ϖ hϖ n τ ξ (k + m) (u * v)
  unfold shell at h
  rw [h, chv_mul]
  by_cases hk : k = n - m
  · rw [if_pos (by omega), if_pos hk, mul_comm, mul_smul]
  · rw [if_neg (by omega), if_neg hk, smul_zero]

include hsm hirr hadm in

private theorem shell_rT_wG_bump {δ : Γ} (n : ℤ) (τ : Ch p δ) (ξ : coinv p S) (k : ℤ) (u : UF p) :
    shell p S ϖ (rT p (wG p) (bump p S hstab hsm ϖ hϖ n τ ξ)) k u =
      (omega p S hstab hsm hirr hadm (ϖ ^ k * (u : Fx)) * (chv τ u)⁻¹) •
        ((Cop p S hstab hsm hpsi ϖ hϖ (n + k) τ ξ : coinv p S) : (G → ℂ) ⧸ defectSpan p S) := by
  unfold shell
  rw [kirillov_rT_wG p S hstab hsm hirr hadm (bump_mem p S hstab hsm ϖ hϖ n τ ξ), Cop_apply_coe]
  have e : (ϖ ^ k * (u : Fx))⁻¹ = ϖ ^ (-k) * ((u⁻¹ : UF p) : Fx) := by
    rw [mul_inv, zpow_neg, Subgroup.coe_inv]
  rw [e, rT_dg_bump p S hstab hsm hpsi ϖ hϖ, chv_inv, sub_neg_eq_add]
  unfold theta
  rw [map_smul, map_smul, smul_smul]

include hsm hirr hadm in

private theorem exists_forall_Cop_eq_zero (hS : S ≠ ⊥) {δ : Γ} (τ : Ch p δ) (ξ : coinv p S) :
    ∃ m₀ : ℤ, ∀ m : ℤ, m ≤ m₀ → Cop p S hstab hsm hpsi ϖ hϖ m τ ξ = 0 := by
  obtain ⟨β, hβ⟩ := exists_forall_kirillov_eq_zero p S hstab hsm
    (show rT p (wG p) (bump p S hstab hsm ϖ hϖ 0 τ ξ) ∈ S from hstab _ (bump_mem p S hstab hsm ϖ hϖ 0 τ ξ) (wG p))
  refine ⟨-WithZero.log (β : WithZero (Multiplicative ℤ)), fun m hm => ?_⟩
  have h := shell_rT_wG_bump p S hstab hsm hpsi hirr hadm ϖ hϖ 0 τ ξ m 1
  unfold shell at h
  rw [hβ, zero_add] at h
  · have hne : omega p S hstab hsm hirr hadm (ϖ ^ m * ((1 : UF p) : Fx)) * (chv τ 1)⁻¹ ≠ 0 :=
      mul_ne_zero (omega_ne_zero p S hstab hsm hirr hadm hS _) (inv_ne_zero (chv_ne_zero τ 1))
    have h' := (smul_eq_zero.mp h.symm).resolve_left hne
    exact Subtype.ext h'
  ·
    rw [Units.val_mul, map_mul, v_coe_UF, mul_one, v_pi_zpow p ϖ hϖ,
      ← WithZero.exp_log β.ne_zero, WithZero.exp_le_exp]
    omega

include hstab in

private theorem shell_mem {V : G → ℂ} (hV : V ∈ S) (k : ℤ) (u : UF p) : shell p S ϖ V k u ∈ coinv p S :=
  Submodule.mem_map_of_mem (hstab V hV _)

include hstab in

private noncomputable def melC (δ : Γ) {V : G → ℂ} (hV : V ∈ S) (k : ℤ) (σ : Ch p δ) : coinv p S :=
  ⟨comp p δ (shell p S ϖ V k) σ, by
    unfold comp
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ =>
      Submodule.smul_mem _ _ (shell_mem p S hstab ϖ hV k (rep p δ q)))⟩

private theorem coe_melC (δ : Γ) {V : G → ℂ} (hV : V ∈ S) (k : ℤ) (σ : Ch p δ) :
    ((melC p S hstab ϖ δ hV k σ : coinv p S) : (G → ℂ) ⧸ defectSpan p S) = comp p δ (shell p S ϖ V k) σ := rfl

include hpsi in

private theorem eq_sum_bump {δ : Γ} {V : G → ℂ} (hV : V ∈ S) (W : Finset ℤ)
    (hW : ∀ k : ℤ, k ∉ W → ∀ u : UF p, shell p S ϖ V k u = 0)
    (hlvl : ∀ k ∈ W, IsLvl p δ (shell p S ϖ V k)) :
    V = ∑ k ∈ W, ∑ σ : Ch p δ, bump p S hstab hsm ϖ hϖ k (-σ) (melC p S hstab ϖ δ hV k σ) := by
  refine eq_of_forall_shell_eq p S hsm hpsi ϖ hϖ hV
    (Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun σ _ => bump_mem p S hstab hsm ϖ hϖ _ _ _) fun j u => ?_
  rw [shell_sum]
  simp_rw [shell_sum, shell_bump, coe_melC]

  by_cases hj : j ∈ W
  · rw [Finset.sum_eq_single j (fun k _ hk => by simp [Ne.symm hk]) (fun h => (h hj).elim)]
    simp only [if_true]
    rw [← sum_inv_chv_smul_comp p (hlvl j hj) u]
    exact Finset.sum_congr rfl fun σ _ => by rw [chv_neg]
  · rw [hW j hj u]
    symm
    refine Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun σ _ => ?_
    have hkj : j ≠ k := fun h => hj (h ▸ hk)
    simp [hkj]

end operators

private def negUF : UF p := ⟨-1, by
  show Valued.v (((-1 : Fx) : F)) = 1
  rw [Units.val_neg, Units.val_one, Valuation.map_neg, Valuation.map_one]⟩

private theorem wG_identity :
    wG p * (unipotentGL2 (1 : F) * wG p) =
      unipotentGL2 (1 : F) * (dg p ((negUF p : UF p) : Fx) * (wG p * unipotentGL2 (1 : F))) := by
  apply Units.ext
  simp only [Units.val_mul, wG_coe, dg_coe, unipotentGL2_coe]
  have h : (((negUF p : UF p) : Fx) : F) = -1 := by
    show (((-1 : Fx)) : F) = -1
    rw [Units.val_neg, Units.val_one]
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

section relation

variable (S : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ))
  (hstab : ∀ W ∈ S, ∀ k : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p), (fun g => W (g * k)) ∈ S)
  (hsm : ∀ W ∈ S, ∃ K : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
    IsOpen (K : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) ∧ ∀ k ∈ K, (fun g => W (g * k)) = W)
  (hpsi : ∀ W ∈ S, ∀ (x : HeightOneSpectrum.adicCompletion ℚ p)
    (g : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
    W (unipotentGL2 x * g) = NumberField.StandardAddChar.psiV p x * W g)
  (hirr : ∀ T : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ), T ≤ S →
    (∀ W ∈ T, ∀ k : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p), (fun g => W (g * k)) ∈ T) → T = ⊥ ∨ T = S)
  (hadm : ∀ K : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
    IsOpen (K : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) →
    ∀ T : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ), T ≤ S →
      (∀ W ∈ T, ∀ k ∈ K, (fun g => W (g * k)) = W) → FiniteDimensional ℂ T)
  (hS : S ≠ ⊥)
  (ϖ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ)
  (hϖ : Valued.v (ϖ : HeightOneSpectrum.adicCompletion ℚ p) = WithZero.exp (-1 : ℤ))
  (δ : Units (WithZero (Multiplicative ℤ)))
  (hδω : ∀ m ∈ Um p δ, omega p S hstab hsm hirr hadm (m : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) = 1)

local notation "COP" => Cop p S hstab hsm hpsi ϖ hϖ
local notation "BUMP" => bump p S hstab hsm ϖ hϖ
local notation "QD" => (G → ℂ) ⧸ defectSpan p S

include hS hδω in

private noncomputable def omCh : Ch p δ :=
  chOfFun p δ (fun u => omega p S hstab hsm hirr hadm (u : Fx))
    (fun u v => by
      rw [Subgroup.coe_mul]
      exact omega_mul p S hstab hsm hirr hadm hS _ _) hδω

private theorem chv_omCh (u : UF p) :
    chv (omCh p S hstab hsm hirr hadm hS δ hδω) u = omega p S hstab hsm hirr hadm (u : Fx) :=
  chv_chOfFun p δ _ _ _ u

private noncomputable def psh (k : ℤ) (u : UF p) : ℂ :=
  NumberField.StandardAddChar.psiV p (((ϖ ^ k * (u : Fx) : Fx) : F))

private noncomputable def pik (k : ℤ) : ℂ := omega p S hstab hsm hirr hadm (ϖ ^ k)

include hϖ in
private theorem psh_eq_one_of_nonneg {k : ℤ} (hk : 0 ≤ k) (u : UF p) : psh p ϖ k u = 1 := by
  unfold psh
  apply NumberField.StandardAddChar.psiV_eq_one_of_mem_integers
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_mul, map_mul, v_coe_UF, mul_one, v_pi_zpow p ϖ hϖ,
    ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

private noncomputable def gco (k : ℤ) (γ : Ch p δ) : ℂ := comp p δ (fun u => psh p ϖ k u - 1) γ

private noncomputable def hco (k : ℤ) (γ : Ch p δ) : ℂ := comp p δ (psh p ϖ k) γ

local notation "OMC" => omCh p S hstab hsm hirr hadm hS δ hδω
local notation "PIK" => pik p S hstab hsm hirr hadm ϖ
local notation "HCO" => hco p ϖ δ
local notation "GCO" => gco p ϖ δ

include hϖ in
private theorem gco_eq_zero_of_nonneg {k : ℤ} (hk : 0 ≤ k) (γ : Ch p δ) : GCO k γ = 0 := by
  unfold gco
  simp_rw [psh_eq_one_of_nonneg p ϖ hϖ hk, sub_self]
  exact comp_zero p δ γ

private theorem isLvl_chv (τ : Ch p δ) : IsLvl p δ (chv τ) := fun u m hm => by
  rw [chv_mul, chv_of_mem τ hm, mul_one]

private theorem comp_const {X : Type*} [AddCommGroup X] [Module ℂ X] (ξ : X) (γ : Ch p δ) :
    comp p δ (fun _ : UF p => ξ) γ = if γ = 0 then ξ else 0 := by
  have h : (fun _ : UF p => ξ) = fun u => chv (0 : Ch p δ) u • ξ := by
    funext u
    rw [chv_zero, one_smul]
  rw [h, comp_smul_const, comp_chv, add_zero]
  split_ifs <;> simp

private theorem comp_mul_chv_smul {X : Type*} [AddCommGroup X] [Module ℂ X] (c : ℂ) (χ : Ch p δ) (ξ : X)
    (γ : Ch p δ) : comp p δ (fun u => (c * chv χ u) • ξ) γ = if γ + χ = 0 then c • ξ else 0 := by
  have h : (fun u => (c * chv χ u) • ξ) = fun u => chv χ u • (c • ξ) := by
    funext u
    rw [smul_smul, mul_comm]
  rw [h, comp_chv_smul, comp_const]

private theorem shell_bump_w (n : ℤ) (τ : Ch p δ) (ξ : coinv p S) (k : ℤ) (u : UF p) :
    shell p S ϖ (rT p (wG p) (BUMP n τ ξ)) k u =
      (PIK k *
        chv (OMC + -τ) u) •
        ((COP (n + k) τ ξ : coinv p S) : QD) := by
  rw [shell_rT_wG_bump p S hstab hsm hpsi hirr hadm ϖ hϖ, omega_mul p S hstab hsm hirr hadm hS, chv_add, chv_neg,
    chv_omCh]
  unfold pik
  rw [mul_assoc]

include hstab in
private theorem rT_mem (g : G) {E : G → ℂ} (hE : E ∈ S) : rT p g E ∈ S := hstab E hE g

include hstab in
private theorem A_mem {E : G → ℂ} (hE : E ∈ S) : rT p (wG p) E ∈ S := hstab E hE _

include hstab in
private theorem N1_mem {E : G → ℂ} (hE : E ∈ S) : rT p (unipotentGL2 (1 : F)) E ∈ S := hstab E hE _

include hstab in
private theorem B_mem {E : G → ℂ} (hE : E ∈ S) :
    rT p (unipotentGL2 (1 : F)) (rT p (wG p) E) - rT p (wG p) E ∈ S :=
  S.sub_mem (hstab _ (hstab E hE _) _) (hstab E hE _)

private theorem shell_B (n : ℤ) (τ : Ch p δ) (ξ : coinv p S) (k : ℤ) (u : UF p) :
    shell p S ϖ (rT p (unipotentGL2 (1 : F)) (rT p (wG p) (BUMP n τ ξ)) -
        rT p (wG p) (BUMP n τ ξ)) k u =
      ((psh p ϖ k u - 1) * (PIK k *
        chv (OMC + -τ) u)) •
        ((COP (n + k) τ ξ : coinv p S) : QD) := by
  rw [shell_sub]
  have h1 : shell p S ϖ (rT p (unipotentGL2 (1 : F)) (rT p (wG p) (BUMP n τ ξ))) k u =
      psh p ϖ k u • shell p S ϖ (rT p (wG p) (BUMP n τ ξ)) k u := by
    unfold shell
    rw [kirillov_rT_unipotent p S hstab (A_mem p S hstab (bump_mem p S hstab hsm ϖ hϖ n τ ξ)), mul_one]
    rfl
  rw [h1, shell_bump_w p S hstab hsm hpsi hirr hadm hS ϖ hϖ δ hδω, smul_smul, ← sub_smul, sub_one_mul]

include hpsi hirr hadm hS hδω in

private theorem shell_B_eq_zero (n : ℤ) (τ : Ch p δ) (ξ : coinv p S) (K : ℤ)
    (hK : ∀ k : ℤ, k < K → COP (n + k) τ ξ = 0) (k : ℤ) (hk : k ∉ Finset.Ico K 0)
    (u : UF p) :
    shell p S ϖ (rT p (unipotentGL2 (1 : F)) (rT p (wG p) (BUMP n τ ξ)) -
        rT p (wG p) (BUMP n τ ξ)) k u = 0 := by
  rw [shell_B p S hstab hsm hpsi hirr hadm hS ϖ hϖ δ hδω]
  rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hk
  rcases hk with hk | hk
  · rw [hK k hk, Submodule.coe_zero, smul_zero]
  · rw [psh_eq_one_of_nonneg p ϖ hϖ hk, sub_self, zero_mul, zero_smul]

include hpsi hirr hadm hS hδω in

private theorem isLvl_shell_B (n : ℤ) (τ : Ch p δ) (ξ : coinv p S) (k : ℤ) (hk : IsLvl p δ (psh p ϖ k)) :
    IsLvl p δ (shell p S ϖ (rT p (unipotentGL2 (1 : F)) (rT p (wG p) (BUMP n τ ξ)) -
        rT p (wG p) (BUMP n τ ξ)) k) := by
  intro u m hm
  rw [shell_B p S hstab hsm hpsi hirr hadm hS ϖ hϖ δ hδω, shell_B p S hstab hsm hpsi hirr hadm hS ϖ hϖ δ hδω,
    hk u m hm, isLvl_chv p δ _ u m hm]

private theorem melC_B (n : ℤ) (τ : Ch p δ) (ξ : coinv p S) (k : ℤ) (σ : Ch p δ) :
    melC p S hstab ϖ δ (B_mem p S hstab (bump_mem p S hstab hsm ϖ hϖ n τ ξ)) k σ =
      (PIK k * GCO k (σ + (OMC + -τ))) •
        COP (n + k) τ ξ := by
  apply Subtype.ext
  rw [coe_melC, Submodule.coe_smul]
  have h : shell p S ϖ (rT p (unipotentGL2 (1 : F)) (rT p (wG p) (BUMP n τ ξ)) -
      rT p (wG p) (BUMP n τ ξ)) k = fun u =>
        (PIK k *
          (chv (OMC + -τ) u * (psh p ϖ k u - 1))) •
          ((COP (n + k) τ ξ : coinv p S) : QD) := by
    funext u
    rw [shell_B p S hstab hsm hpsi hirr hadm hS ϖ hϖ δ hδω]
    congr 1
    ring
  rw [h, comp_smul_const]
  congr 1
  unfold gco
  have h2 : (fun u => PIK k *
      (chv (OMC + -τ) u * (psh p ϖ k u - 1))) =
      fun u => PIK k • (chv (OMC + -τ) u •
        (psh p ϖ k u - 1)) := by
    funext u
    rfl
  rw [h2, comp_const_smul, comp_chv_smul, smul_eq_mul]

include hstab in

private theorem shell_rT_n1 {V : G → ℂ} (hV : V ∈ S) (k : ℤ) (u : UF p) :
    shell p S ϖ (rT p (unipotentGL2 (1 : F)) V) k u = psh p ϖ k u • shell p S ϖ V k u := by
  unfold shell
  rw [kirillov_rT_unipotent p S hstab hV, mul_one]
  rfl

private theorem shell_rT_dg_unit (V : G → ℂ) (ν : UF p) (k : ℤ) (u : UF p) :
    shell p S ϖ (rT p (dg p (ν : Fx)) V) k u = shell p S ϖ V k (u * ν) := by
  unfold shell
  rw [kirillov_rT_dg, mul_assoc, Subgroup.coe_mul]

private theorem melC_E₁ (n : ℤ) (τ : Ch p δ) (ξ : coinv p S) (σ : Ch p δ) :
    melC p S hstab ϖ δ (N1_mem p S hstab (bump_mem p S hstab hsm ϖ hϖ n τ ξ)) n σ =
      HCO n (σ + τ) • ξ := by
  apply Subtype.ext
  rw [coe_melC, Submodule.coe_smul]
  have h : shell p S ϖ (rT p (unipotentGL2 (1 : F)) (BUMP n τ ξ)) n =
      fun u => chv τ u • (psh p ϖ n u • (ξ : QD)) := by
    funext u
    rw [shell_rT_n1 p S hstab ϖ (bump_mem p S hstab hsm ϖ hϖ n τ ξ), shell_bump_self, smul_comm]
  rw [h, comp_chv_smul, comp_smul_const]
  rfl

include hpsi in

private theorem E₁_eq_sum (n : ℤ) (τ : Ch p δ) (ξ : coinv p S) (hδn : IsLvl p δ (psh p ϖ n)) :
    rT p (unipotentGL2 (1 : F)) (BUMP n τ ξ) =
      ∑ σ : Ch p δ, HCO n (σ + τ) • BUMP n (-σ) ξ := by
  have hE₁ := eq_sum_bump p S hstab hsm hpsi ϖ hϖ
    (N1_mem p S hstab (bump_mem p S hstab hsm ϖ hϖ n τ ξ)) {n}
    (fun k hk u => by
      rw [shell_rT_n1 p S hstab ϖ (bump_mem p S hstab hsm ϖ hϖ n τ ξ),
        shell_bump_of_ne p S hstab hsm ϖ hϖ n τ ξ (fun h => hk (Finset.mem_singleton.mpr h)), smul_zero])
    (fun k hk u m hm => by
      rw [Finset.mem_singleton] at hk
      subst hk
      rw [shell_rT_n1 p S hstab ϖ (bump_mem p S hstab hsm ϖ hϖ _ τ ξ),
        shell_rT_n1 p S hstab ϖ (bump_mem p S hstab hsm ϖ hϖ _ τ ξ),
        hδn u m hm, shell_bump_self, shell_bump_self, chv_mul, chv_of_mem τ hm, mul_one])
  rw [Finset.sum_singleton] at hE₁
  refine hE₁.trans ?_
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [melC_E₁ p S hstab hsm ϖ hϖ δ, bump_smul p S hstab hsm hpsi]

private theorem B_eq_sum (n : ℤ) (τ : Ch p δ) (ξ : coinv p S) (K : ℤ)
    (hK : ∀ k : ℤ, k < K → COP (n + k) τ ξ = 0)
    (hδψ : ∀ k : ℤ, K ≤ k → IsLvl p δ (psh p ϖ k)) :
    rT p (unipotentGL2 (1 : F)) (rT p (wG p) (BUMP n τ ξ)) -
        rT p (wG p) (BUMP n τ ξ) =
      ∑ k ∈ Finset.Ico K 0, ∑ σ : Ch p δ,
        (PIK k * GCO k (σ + (OMC + -τ))) •
          BUMP k (-σ) (COP (n + k) τ ξ) := by
  have hB := eq_sum_bump p S hstab hsm hpsi ϖ hϖ (B_mem p S hstab (bump_mem p S hstab hsm ϖ hϖ n τ ξ))
    (Finset.Ico K 0) (shell_B_eq_zero p S hstab hsm hpsi hirr hadm hS ϖ hϖ δ hδω n τ ξ K hK)
    (fun k hk => isLvl_shell_B p S hstab hsm hpsi hirr hadm hS ϖ hϖ δ hδω n τ ξ k (hδψ k (Finset.mem_Ico.mp hk).1))
  refine hB.trans ?_
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [melC_B p S hstab hsm hpsi hirr hadm hS ϖ hϖ δ hδω, bump_smul p S hstab hsm hpsi]

private theorem L_eq (n : ℤ) (τ : Ch p δ) (ξ : coinv p S) :
    rT p (wG p) (rT p (unipotentGL2 (1 : F)) (rT p (wG p) (BUMP n τ ξ))) =
      rT p (wG p) (rT p (unipotentGL2 (1 : F)) (rT p (wG p) (BUMP n τ ξ)) -
        rT p (wG p) (BUMP n τ ξ)) + BUMP n τ ξ := by
  rw [map_sub, sub_add_eq_add_sub, rT_rT p (wG p) (wG p), wG_mul_wG, rT_one, add_sub_cancel_right]

private theorem comp_shell_bump (n : ℤ) (τ : Ch p δ) (ξ : coinv p S) (j : ℤ) (ρ : Ch p δ) :
    comp p δ (shell p S ϖ (BUMP n τ ξ) j) ρ = (if j = n then (if ρ + τ = 0 then (ξ : QD) else 0) else 0) := by
  by_cases hjn : j = n
  · rw [hjn]
    have h : shell p S ϖ (BUMP n τ ξ) n = fun u => chv τ u • (ξ : QD) := by
      funext u
      exact shell_bump_self p S hstab hsm ϖ hϖ n τ ξ u
    rw [h, comp_chv_smul, comp_const, if_pos rfl]
  · have h : shell p S ϖ (BUMP n τ ξ) j = fun _ => (0 : QD) := by
      funext u
      exact shell_bump_of_ne p S hstab hsm ϖ hϖ n τ ξ hjn u
    rw [h, comp_zero, if_neg hjn]

private theorem shell_rT_wG_B (n : ℤ) (τ : Ch p δ) (ξ : coinv p S) (K : ℤ)
    (hK : ∀ k : ℤ, k < K → COP (n + k) τ ξ = 0)
    (hδψ : ∀ k : ℤ, K ≤ k → IsLvl p δ (psh p ϖ k)) (j : ℤ) :
    shell p S ϖ (rT p (wG p)
        (rT p (unipotentGL2 (1 : F)) (rT p (wG p) (BUMP n τ ξ)) -
          rT p (wG p) (BUMP n τ ξ))) j = fun u =>
      ∑ k ∈ Finset.Ico K 0, ∑ σ : Ch p δ,
        (PIK j * chv (OMC + σ) u) •
          ((PIK k * GCO k (σ + (OMC + -τ))) •
            ((COP (k + j) (-σ) (COP (n + k) τ ξ) : coinv p S) : QD)) := by
  rw [B_eq_sum p S hstab hsm hpsi hirr hadm hS ϖ hϖ δ hδω n τ ξ K hK hδψ]
  funext u
  rw [map_sum, shell_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_sum, shell_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_smul, shell_smul, shell_bump_w p S hstab hsm hpsi hirr hadm hS ϖ hϖ δ hδω, neg_neg, smul_comm]

private theorem comp_rT_wG_B (n : ℤ) (τ : Ch p δ) (ξ : coinv p S) (K : ℤ)
    (hK : ∀ k : ℤ, k < K → COP (n + k) τ ξ = 0)
    (hδψ : ∀ k : ℤ, K ≤ k → IsLvl p δ (psh p ϖ k)) (j : ℤ) (ρ : Ch p δ) :
    comp p δ (shell p S ϖ (rT p (wG p)
        (rT p (unipotentGL2 (1 : F)) (rT p (wG p) (BUMP n τ ξ)) -
          rT p (wG p) (BUMP n τ ξ))) j) ρ =
      PIK j • ∑ k ∈ Finset.Ico K 0,
        (PIK k * GCO k (-(ρ + OMC) + (OMC + -τ))) •
          ((COP (k + j) (ρ + OMC) (COP (n + k) τ ξ) : coinv p S) : QD) := by
  rw [shell_rT_wG_B p S hstab hsm hpsi hirr hadm hS ϖ hϖ δ hδω n τ ξ K hK hδψ j, comp_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [comp_sum]
  simp_rw [comp_mul_chv_smul]
  rw [Finset.sum_eq_single (-(ρ + OMC))]
  · rw [if_pos (by abel), neg_neg]
  · intro σ _ hσ
    rw [if_neg]
    intro h
    apply hσ
    rw [← add_assoc] at h
    exact eq_neg_of_add_eq_zero_right h
  · intro h
    exact (h (Finset.mem_univ _)).elim

private theorem comp_L (n : ℤ) (τ : Ch p δ) (ξ : coinv p S) (K : ℤ)
    (hK : ∀ k : ℤ, k < K → COP (n + k) τ ξ = 0)
    (hδψ : ∀ k : ℤ, K ≤ k → IsLvl p δ (psh p ϖ k)) (j : ℤ) (ρ : Ch p δ) :
    comp p δ (shell p S ϖ
        (rT p (wG p) (rT p (unipotentGL2 (1 : F)) (rT p (wG p) (BUMP n τ ξ)))) j) ρ =
      PIK j • ∑ k ∈ Finset.Ico K 0,
        (PIK k * GCO k (-(ρ + OMC) + (OMC + -τ))) •
          ((COP (k + j) (ρ + OMC) (COP (n + k) τ ξ) : coinv p S) : QD) +
        (if j = n then (if ρ + τ = 0 then (ξ : QD) else 0) else 0) := by
  rw [L_eq p S hstab hsm ϖ hϖ δ n τ ξ]
  have hsplit : shell p S ϖ (rT p (wG p)
      (rT p (unipotentGL2 (1 : F)) (rT p (wG p) (BUMP n τ ξ)) -
          rT p (wG p) (BUMP n τ ξ)) + BUMP n τ ξ) j = fun u =>
        shell p S ϖ (rT p (wG p)
          (rT p (unipotentGL2 (1 : F)) (rT p (wG p) (BUMP n τ ξ)) -
          rT p (wG p) (BUMP n τ ξ))) j u + shell p S ϖ (BUMP n τ ξ) j u := by
    funext u
    exact shell_add p S ϖ _ _ j u
  rw [hsplit, comp_add, comp_rT_wG_B p S hstab hsm hpsi hirr hadm hS ϖ hϖ δ hδω n τ ξ K hK hδψ j ρ,
    comp_shell_bump p S hstab hsm ϖ hϖ δ n τ ξ j ρ]

private theorem comp_R (n : ℤ) (τ : Ch p δ) (ξ : coinv p S) (hδn : IsLvl p δ (psh p ϖ n)) (j : ℤ) (ρ : Ch p δ) :
    comp p δ (shell p S ϖ (rT p (unipotentGL2 (1 : F)) (rT p (dg p ((negUF p : UF p) : Fx))
        (rT p (wG p) (rT p (unipotentGL2 (1 : F)) (BUMP n τ ξ))))) j) ρ =
      PIK j • ∑ σ : Ch p δ,
        (chv (OMC + σ) (negUF p) * HCO n (σ + τ) * HCO j (ρ + (OMC + σ))) •
          ((COP (n + j) (-σ) ξ : coinv p S) : QD) := by
  rw [E₁_eq_sum p S hstab hsm hpsi ϖ hϖ δ n τ ξ hδn]
  simp_rw [map_sum, map_smul]
  have hsh : shell p S ϖ (∑ σ : Ch p δ, HCO n (σ + τ) •
      rT p (unipotentGL2 (1 : F)) (rT p (dg p ((negUF p : UF p) : Fx)) (rT p (wG p) (BUMP n (-σ) ξ)))) j =
      fun u => ∑ σ : Ch p δ, chv (OMC + σ) u • (psh p ϖ j u •
        ((HCO n (σ + τ) * (PIK j * chv (OMC + σ) (negUF p))) •
          ((COP (n + j) (-σ) ξ : coinv p S) : QD))) := by
    funext u
    rw [shell_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [shell_smul, shell_rT_n1 p S hstab ϖ (rT_mem p S hstab (dg p ((negUF p : UF p) : Fx))
      (A_mem p S hstab (bump_mem p S hstab hsm ϖ hϖ n (-σ) ξ))),
      shell_rT_dg_unit, shell_bump_w p S hstab hsm hpsi hirr hadm hS ϖ hϖ δ hδω, neg_neg, chv_mul]
    simp only [smul_smul]
    congr 1
    ring
  rw [hsh, comp_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [comp_chv_smul, comp_smul_const]
  unfold hco
  simp only [smul_smul]
  congr 1
  ring

private theorem smul_cancel_of_ne_zero {X : Type*} [AddCommGroup X] [Module ℂ X] {c : ℂ} (hc : c ≠ 0) {a b : X}
    (h : c • a = c • b) : a = b := by
  have h' := congrArg (fun x : X => c⁻¹ • x) h
  simp only [smul_smul, inv_mul_cancel₀ hc, one_smul] at h'
  exact h'

private theorem rT_identity (E : G → ℂ) :
    rT p (wG p) (rT p (unipotentGL2 (1 : F)) (rT p (wG p) E)) =
      rT p (unipotentGL2 (1 : F))
        (rT p (dg p ((negUF p : UF p) : Fx)) (rT p (wG p) (rT p (unipotentGL2 (1 : F)) E))) := by
  simp only [rT_rT]
  rw [wG_identity]

private theorem sum_commutator_eq_zero (n j : ℤ) (τ α : Ch p δ) (ξ : coinv p S) (K : ℤ)
    (hKn : ∀ k : ℤ, k < K → COP (n + k) τ ξ = 0) (hKj : ∀ k : ℤ, k < K → COP (j + k) α ξ = 0)
    (hδψ : ∀ k : ℤ, K ≤ k → IsLvl p δ (psh p ϖ k)) (hδn : IsLvl p δ (psh p ϖ n)) (hδj : IsLvl p δ (psh p ϖ j)) :
    ∑ k ∈ Finset.Ico K 0, (PIK k * GCO k (-α + (OMC + -τ))) •
        (((COP (k + j) α (COP (n + k) τ ξ) : coinv p S) : QD) -
          ((COP (k + n) τ (COP (j + k) α ξ) : coinv p S) : QD)) = 0 := by
  have h₁ := comp_L p S hstab hsm hpsi hirr hadm hS ϖ hϖ δ hδω n τ ξ K hKn hδψ j (α + -OMC)
  have h₂ := comp_L p S hstab hsm hpsi hirr hadm hS ϖ hϖ δ hδω j α ξ K hKj hδψ n (τ + -OMC)
  rw [rT_identity, comp_R p S hstab hsm hpsi hirr hadm hS ϖ hϖ δ hδω n τ ξ hδn] at h₁
  rw [rT_identity, comp_R p S hstab hsm hpsi hirr hadm hS ϖ hϖ δ hδω j α ξ hδj] at h₂
  simp_rw [neg_add_cancel_right] at h₁ h₂

  have hT : ∑ σ : Ch p δ,
      (chv (OMC + σ) (negUF p) * HCO j (σ + α) * HCO n (τ + -OMC + (OMC + σ))) •
        ((COP (j + n) (-σ) ξ : coinv p S) : QD) =
      ∑ σ : Ch p δ,
      (chv (OMC + σ) (negUF p) * HCO n (σ + τ) * HCO j (α + -OMC + (OMC + σ))) •
        ((COP (n + j) (-σ) ξ : coinv p S) : QD) := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    have e1 : τ + -OMC + (OMC + σ) = σ + τ := by abel
    have e2 : α + -OMC + (OMC + σ) = σ + α := by abel
    rw [e1, e2, add_comm j n, mul_right_comm]
  rw [hT] at h₂

  have hite : (if n = j then (if τ + -OMC + α = 0 then (ξ : QD) else 0) else 0) =
      (if j = n then (if α + -OMC + τ = 0 then (ξ : QD) else 0) else 0) := by
    have e3 : τ + -OMC + α = α + -OMC + τ := by abel
    rw [e3]
    by_cases h : j = n
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  rw [hite] at h₂

  have e4 : -τ + (OMC + -α) = -α + (OMC + -τ) := by abel
  simp_rw [e4] at h₂

  have hsums : ∑ k ∈ Finset.Ico K 0, (PIK k * GCO k (-α + (OMC + -τ))) •
        ((COP (k + j) α (COP (n + k) τ ξ) : coinv p S) : QD) =
      ∑ k ∈ Finset.Ico K 0, (PIK k * GCO k (-α + (OMC + -τ))) •
        ((COP (k + n) τ (COP (j + k) α ξ) : coinv p S) : QD) := by
    have hpj : PIK j ≠ 0 := omega_ne_zero p S hstab hsm hirr hadm hS _
    have hpn : PIK n ≠ 0 := omega_ne_zero p S hstab hsm hirr hadm hS _
    by_cases hjn : j = n
    · have hp : PIK j = PIK n := by rw [hjn]
      rw [hp] at h₁
      exact smul_cancel_of_ne_zero hpn (add_right_cancel (h₁.symm.trans h₂))
    · rw [if_neg hjn, add_zero] at h₁ h₂
      exact (smul_cancel_of_ne_zero hpj h₁).symm.trans (smul_cancel_of_ne_zero hpn h₂)
  have hsplit : ∑ k ∈ Finset.Ico K 0, (PIK k * GCO k (-α + (OMC + -τ))) •
        (((COP (k + j) α (COP (n + k) τ ξ) : coinv p S) : QD) -
          ((COP (k + n) τ (COP (j + k) α ξ) : coinv p S) : QD)) =
      ∑ k ∈ Finset.Ico K 0, (PIK k * GCO k (-α + (OMC + -τ))) •
          ((COP (k + j) α (COP (n + k) τ ξ) : coinv p S) : QD) -
        ∑ k ∈ Finset.Ico K 0, (PIK k * GCO k (-α + (OMC + -τ))) •
          ((COP (k + n) τ (COP (j + k) α ξ) : coinv p S) : QD) := by
    exact (Finset.sum_congr rfl fun k _ => smul_sub _ _ _).trans (Finset.sum_sub_distrib _ _)
  exact hsplit.trans (sub_eq_zero.mpr hsums)

end relation

section levels

variable (S : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ))
  (hstab : ∀ W ∈ S, ∀ k : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p), (fun g => W (g * k)) ∈ S)
  (hsm : ∀ W ∈ S, ∃ K : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
    IsOpen (K : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) ∧ ∀ k ∈ K, (fun g => W (g * k)) = W)
  (hpsi : ∀ W ∈ S, ∀ (x : HeightOneSpectrum.adicCompletion ℚ p)
    (g : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
    W (unipotentGL2 x * g) = NumberField.StandardAddChar.psiV p x * W g)
  (ϖ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ)
  (hϖ : Valued.v (ϖ : HeightOneSpectrum.adicCompletion ℚ p) = WithZero.exp (-1 : ℤ))

private theorem comp_translate {X : Type*} [AddCommGroup X] [Module ℂ X] {δ : Γ} {f : UF p → X} (hf : IsLvl p δ f)
    (ν : UF p) (γ : Ch p δ) : comp p δ (fun u => f (u * ν)) γ = (chv γ ν)⁻¹ • comp p δ f γ := by
  unfold comp
  rw [smul_comm]
  congr 1

  rw [Finset.smul_sum, ← Equiv.sum_comp (Equiv.mulRight ((ν : Qm p δ)⁻¹))]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Equiv.coe_mulRight]
  have h1 : ((rep p δ (q * (ν : Qm p δ)⁻¹) * ν : UF p) : Qm p δ) = ((rep p δ q : UF p) : Qm p δ) := by
    rw [QuotientGroup.mk_mul, mk_rep, mk_rep, inv_mul_cancel_right]
  have h2 : ((rep p δ (q * (ν : Qm p δ)⁻¹) : UF p) : Qm p δ) = ((rep p δ q * ν⁻¹ : UF p) : Qm p δ) := by
    rw [mk_rep, QuotientGroup.mk_mul, QuotientGroup.mk_inv, mk_rep]
  rw [apply_eq_of_mk_eq_of_isLvl p hf h1, chv_eq_of_mk_eq p le_rfl γ h2, chv_mul, chv_inv, smul_smul, mul_comm]

include hpsi in

private theorem bump_refineCh {δ δ₁ : Γ} (h : δ ≤ δ₁) (n : ℤ) (τ : Ch p δ₁) (ξ : coinv p S) :
    bump p S hstab hsm ϖ hϖ n (refineCh p h τ) ξ = bump p S hstab hsm ϖ hϖ n τ ξ := by
  symm
  refine eq_bump_of_forall_shell p S hstab hsm hpsi ϖ hϖ n (refineCh p h τ) ξ (bump_mem p S hstab hsm ϖ hϖ n τ ξ)
    fun k u => ?_
  rw [shell_bump, chv_refineCh]

private theorem Cop_refineCh {δ δ₁ : Γ} (h : δ ≤ δ₁) (n : ℤ) (τ : Ch p δ₁) :
    Cop p S hstab hsm hpsi ϖ hϖ n (refineCh p h τ) = Cop p S hstab hsm hpsi ϖ hϖ n τ := by
  ext ξ
  rw [Cop_apply_coe, Cop_apply_coe, bump_refineCh p S hstab hsm hpsi ϖ hϖ h]

private noncomputable def lvl (K : ℤ) : Γ := Units.mk0 (WithZero.exp K) WithZero.exp_ne_zero

private theorem lvl_val (K : ℤ) : ((lvl K : Γ) : WithZero (Multiplicative ℤ)) = WithZero.exp K := rfl

include hϖ in

private theorem isLvl_psh_of_le (K : ℤ) (k : ℤ) (hk : K ≤ k) : IsLvl p (lvl K) (psh p ϖ k) := by
  intro u m hm
  unfold psh
  have hm' := (mem_Um_iff p _ m).mp hm
  rw [lvl_val] at hm'
  rw [Subgroup.coe_mul, ← mul_assoc, Units.val_mul]
  set a : F := ((ϖ ^ k * (u : Fx) : Fx) : F) with ha
  have hsplit : a * ((m : Fx) : F) = a + a * (((m : Fx) : F) - 1) := by ring
  rw [hsplit, AddChar.map_add_eq_mul]
  have hint : a * (((m : Fx) : F) - 1) ∈ p.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, ha, Units.val_mul, map_mul, v_coe_UF, mul_one,
      v_pi_zpow p ϖ hϖ]
    calc WithZero.exp (-k) * Valued.v (((m : Fx) : F) - 1)
        ≤ WithZero.exp (-k) * WithZero.exp K := by
          apply mul_le_mul_right
          exact le_of_lt hm'
      _ = WithZero.exp (-k + K) := (WithZero.exp_add _ _).symm
      _ ≤ WithZero.exp 0 := by
          rw [WithZero.exp_le_exp]
          omega
      _ = 1 := WithZero.exp_zero
  rw [NumberField.StandardAddChar.psiV_eq_one_of_mem_integers p hint, mul_one]

end levels

section nonvanishing

variable (ϖ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ)
  (hϖ : Valued.v (ϖ : HeightOneSpectrum.adicCompletion ℚ p) = WithZero.exp (-1 : ℤ))

private theorem norm_exp_aux (a : ℤ) (k : ℕ) {q : ℕ} (hq : q ≠ 0) :
    ‖Complex.exp (-(2 * Real.pi * Complex.I) * ((a : ℂ) / (q : ℂ) ^ k))‖ = 1 := by
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  refine Complex.norm_eq_one_of_pow_eq_one (n := q ^ k) ?_ (pow_ne_zero k hq)
  rw [← Complex.exp_nat_mul]
  have h : ((q ^ k : ℕ) : ℂ) * (-(2 * Real.pi * Complex.I) * ((a : ℂ) / (q : ℂ) ^ k)) =
      ((-a : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    field_simp
  rw [h]
  exact Complex.exp_int_mul_two_pi_mul_I (-a)

private theorem norm_psiPadicFun {q : ℕ} [hq : Fact q.Prime] (y : ℚ_[q]) :
    ‖NumberField.StandardAddChar.psiPadicFun y‖ = 1 := by
  unfold NumberField.StandardAddChar.psiPadicFun
  exact norm_exp_aux _ _ hq.out.ne_zero

private theorem norm_psiV (x : F) : ‖NumberField.StandardAddChar.psiV p x‖ = 1 := by
  rw [NumberField.StandardAddChar.psiV_apply, NumberField.StandardAddChar.psiPadic_apply]
  exact norm_psiPadicFun _

private theorem eq_one_of_norm_eq_one_of_re_eq_one {z : ℂ} (hz : ‖z‖ = 1) (hre : z.re = 1) : z = 1 := by
  have h2 : z.re * z.re + z.im * z.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hz, one_pow]
  rw [hre, one_mul] at h2
  have him : z.im = 0 := mul_self_eq_zero.mp (by linarith)
  exact Complex.ext (by simpa using hre) (by simpa using him)

private theorem forall_eq_one_of_sum_eq {ι : Type*} (s : Finset ι) (z : ι → ℂ) (hz : ∀ i ∈ s, ‖z i‖ = 1)
    (hsum : ∑ i ∈ s, (z i - 1) = 0) : ∀ i ∈ s, z i = 1 := by
  have hre : ∑ i ∈ s, (1 - (z i).re) = 0 := by
    have h := congrArg Complex.re hsum
    rw [Complex.re_sum] at h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at h
    rw [← neg_eq_zero, ← Finset.sum_neg_distrib]
    simpa [neg_sub] using h
  have hnn : ∀ i ∈ s, 0 ≤ 1 - (z i).re := fun i hi => by
    have := Complex.re_le_norm (z i)
    rw [hz i hi] at this
    linarith
  intro i hi
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hre i hi
  exact eq_one_of_norm_eq_one_of_re_eq_one (hz i hi) (by linarith)

include hϖ in

private theorem exists_psh_ne_one : ∃ (k : ℤ) (u₀ : UF p), psh p ϖ k u₀ ≠ 1 := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : F, NumberField.StandardAddChar.psiV p x₀ ≠ 1 :=
    ⟨_, NumberField.StandardAddChar.psiV_algebraMap_inv_ne_one p⟩
  have hx₀0 : x₀ ≠ 0 := by
    rintro rfl
    exact hx₀ (AddChar.map_zero_eq_one _)
  obtain ⟨k, u₀, hku⟩ := exists_shell_decomp p ϖ hϖ (Units.mk0 x₀ hx₀0)
  refine ⟨k, u₀, ?_⟩
  unfold psh
  rw [← hku, Units.val_mk0]
  exact hx₀

include hϖ in

private theorem exists_gco_zero_ne_zero :
    ∃ (k : ℤ) (δ : Γ), IsLvl p δ (psh p ϖ k) ∧ comp p δ (fun u => psh p ϖ k u - 1) (0 : Ch p δ) ≠ 0 := by
  obtain ⟨k, u₀, hu₀⟩ := exists_psh_ne_one p ϖ hϖ
  refine ⟨k, lvl k, isLvl_psh_of_le p ϖ hϖ k k le_rfl, fun h => hu₀ ?_⟩
  unfold comp at h
  simp only [chv_zero, smul_eq_mul, one_mul] at h
  rcases mul_eq_zero.mp h with h | h
  · exact (inv_ne_zero (size_Qm_ne_zero p (lvl k)) h).elim
  · have hall := forall_eq_one_of_sum_eq Finset.univ (fun q : Qm p (lvl k) => psh p ϖ k (rep p (lvl k) q))
      (fun q _ => norm_psiV p _) h (u₀ : Qm p (lvl k)) (Finset.mem_univ _)
    rw [apply_eq_of_mk_eq_of_isLvl p (isLvl_psh_of_le p ϖ hϖ k k le_rfl) (mk_rep p (lvl k) _)] at hall
    exact hall

end nonvanishing

section nonvanishing₂

variable (ϖ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ)
  (hϖ : Valued.v (ϖ : HeightOneSpectrum.adicCompletion ℚ p) = WithZero.exp (-1 : ℤ))

private theorem isLvl_mono {X : Type*} [AddCommGroup X] [Module ℂ X] {δ δ₁ : Γ} (h : δ ≤ δ₁) {f : UF p → X}
    (hf : IsLvl p δ₁ f) : IsLvl p δ f := fun u m hm => hf u m (Um_mono p h hm)

private theorem comp_const_mul (δ : Γ) (c : ℂ) (g : UF p → ℂ) (γ : Ch p δ) :
    comp p δ (fun u => c * g u) γ = c * comp p δ g γ :=
  comp_const_smul p δ c g γ

private theorem refineCh_zero {δ δ₁ : Γ} (h : δ ≤ δ₁) : refineCh p h (0 : Ch p δ₁) = 0 :=
  ext_chv fun u => by rw [chv_refineCh, chv_zero, chv_zero]

private theorem refineCh_ne_zero {δ δ₁ : Γ} (h : δ ≤ δ₁) {γ : Ch p δ₁} (hγ : γ ≠ 0) : refineCh p h γ ≠ 0 := by
  intro h0
  apply hγ
  apply ext_chv
  intro u
  rw [← chv_refineCh p h γ u, h0, chv_zero, chv_zero]

private noncomputable def chExt {δ : Γ} (γ : Ch p δ) (x : F) : ℂ :=
  if h : ∃ u : UF p, ((u : Fx) : F) = x then chv γ h.choose else 0

private theorem chExt_coe {δ : Γ} (γ : Ch p δ) (u : UF p) : chExt p γ ((u : Fx) : F) = chv γ u := by
  unfold chExt
  have h : ∃ u' : UF p, ((u' : Fx) : F) = ((u : Fx) : F) := ⟨u, rfl⟩
  rw [dif_pos h]
  congr 1
  exact Subtype.ext (Units.ext h.choose_spec)

private theorem chExt_of_not {δ : Γ} (γ : Ch p δ) {x : F} (hx : ¬ ∃ u : UF p, ((u : Fx) : F) = x) :
    chExt p γ x = 0 := by
  unfold chExt
  rw [dif_neg hx]

private theorem exists_eq_mul_of_close {δ : Γ} (hδ : δ ≤ 1) (u : UF p) {y : F}
    (hy : Valued.v (((u : Fx) : F) - y) < (δ : WithZero (Multiplicative ℤ))) :
    ∃ m ∈ Um p δ, (((u * m : UF p) : Fx) : F) = y := by
  set t : F := (((u : Fx) : F))⁻¹ * (y - ((u : Fx) : F)) with ht
  have hu0 : ((u : Fx) : F) ≠ 0 := (u : Fx).ne_zero
  have hvt : Valued.v t < (δ : WithZero (Multiplicative ℤ)) := by
    rw [ht, map_mul, map_inv₀, v_coe_UF, inv_one, one_mul, Valuation.map_sub_swap]
    exact hy
  have hvt1 : Valued.v t < Valued.v (1 : F) := by
    rw [Valuation.map_one]
    exact lt_of_lt_of_le hvt (by exact_mod_cast hδ)
  have hv1t : Valued.v (1 + t) = 1 := by
    rw [Valuation.map_add_eq_of_lt_left _ hvt1, Valuation.map_one]
  have h1t : (1 + t : F) ≠ 0 := fun h => by
    rw [h, Valuation.map_zero] at hv1t
    exact zero_ne_one hv1t
  refine ⟨⟨Units.mk0 (1 + t) h1t, by
    show Valued.v ((Units.mk0 (1 + t) h1t : Fx) : F) = 1
    rw [Units.val_mk0]
    exact hv1t⟩, ?_, ?_⟩
  · rw [mem_Um_iff]
    show Valued.v (((Units.mk0 (1 + t) h1t : Fx) : F) - 1) < (δ : WithZero (Multiplicative ℤ))
    rw [Units.val_mk0, add_sub_cancel_left]
    exact hvt
  · rw [Subgroup.coe_mul, Units.val_mul]
    show ((u : Fx) : F) * ((Units.mk0 (1 + t) h1t : Fx) : F) = y
    rw [Units.val_mk0, ht, mul_add, mul_one, mul_inv_cancel_left₀ hu0, add_sub_cancel]

private theorem chExt_eq_of_close {δ : Γ} (γ : Ch p δ) (x y : F)
    (hxy : Valued.v (x - y) < ((min δ 1 : Γ) : WithZero (Multiplicative ℤ))) : chExt p γ x = chExt p γ y := by
  have hδ1 : (min δ 1 : Γ) ≤ 1 := min_le_right _ _
  have hδδ : (min δ 1 : Γ) ≤ δ := min_le_left _ _
  by_cases hx : ∃ u : UF p, ((u : Fx) : F) = x
  · obtain ⟨u, rfl⟩ := hx
    obtain ⟨m, hm, hym⟩ := exists_eq_mul_of_close p hδ1 u hxy
    rw [← hym, chExt_coe, chExt_coe, chv_mul, chv_of_mem γ (Um_mono p hδδ hm), mul_one]
  · by_cases hy : ∃ u : UF p, ((u : Fx) : F) = y
    · exfalso
      obtain ⟨u, rfl⟩ := hy
      rw [Valuation.map_sub_swap] at hxy
      obtain ⟨m, _, hxm⟩ := exists_eq_mul_of_close p hδ1 u hxy
      exact hx ⟨u * m, hxm⟩
    · rw [chExt_of_not p γ hx, chExt_of_not p γ hy]

include hϖ in

private theorem exists_honest_gco_ne_zero_of_ne_zero {δ : Γ} (γ : Ch p δ) (hγ : γ ≠ 0) :
    ∃ (k : ℤ) (δ' : Γ) (h : δ' ≤ δ), IsLvl p δ' (psh p ϖ k) ∧
      comp p δ' (fun u => psh p ϖ k u - 1) (refineCh p h γ) ≠ 0 := by
  by_contra hcon
  push Not at hcon

  obtain ⟨T, c, hT⟩ := AutomorphicForm.LocalFunctionSpace.exists_finset_forall_eq_sum_mul_char_mul p
    (NumberField.StandardAddChar.psiV p) (fun x y => AddChar.map_add_eq_mul _ x y)
    ⟨1, fun x hx => NumberField.StandardAddChar.psiV_eq_one_of_mem_integers p (by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      exact le_of_lt (by simpa using hx))⟩
    ⟨_, NumberField.StandardAddChar.psiV_algebraMap_inv_ne_one p⟩
    (chExt p (-γ)) (min δ 1) (fun x y hxy => chExt_eq_of_close p (-γ) x y hxy) (lvl 1)
  have hexp : ∀ u : UF p, chv (-γ) u = ∑ y ∈ T, c y * NumberField.StandardAddChar.psiV p (((u : Fx) : F) * y) := by
    intro u
    rw [← chExt_coe p (-γ) u]
    apply hT
    rw [v_coe_UF, lvl_val, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    exact zero_lt_one

  classical
  let kf : F → ℤ := fun y => if hy : y = 0 then 0 else (exists_shell_decomp p ϖ hϖ (Units.mk0 y hy)).choose
  set K : ℤ := -∑ y ∈ T, |kf y| with hKdef
  have hK : ∀ y ∈ T, K ≤ kf y := fun y hy => by
    have h1 : |kf y| ≤ ∑ z ∈ T, |kf z| := Finset.single_le_sum (fun z _ => abs_nonneg (kf z)) hy
    rw [hKdef]
    exact le_trans (neg_le_neg h1) (neg_abs_le (kf y))
  set δ' : Γ := min (lvl K) δ with hδ'
  have hδ'δ : δ' ≤ δ := min_le_right _ _
  have hδ'K : δ' ≤ lvl K := min_le_left _ _
  set γ' : Ch p δ' := refineCh p hδ'δ γ with hγ'
  have hγ'0 : γ' ≠ 0 := refineCh_ne_zero p hδ'δ hγ

  have hleft : comp p δ' (fun u => chv (-γ) u) γ' = 1 := by
    have h1 : (fun u => chv (-γ) u) = fun u => chv (-γ') u := by
      funext u
      rw [chv_neg, chv_neg, hγ', chv_refineCh]
    rw [h1, comp_chv, if_pos (add_neg_cancel γ')]

  have hright :
      comp p δ' (fun u => ∑ y ∈ T, c y * NumberField.StandardAddChar.psiV p (((u : Fx) : F) * y)) γ' = 0 := by
    rw [comp_sum]
    refine Finset.sum_eq_zero fun y hy => ?_
    rw [comp_const_mul]
    refine mul_eq_zero_of_right _ ?_
    by_cases hy0 : y = 0
    · subst hy0
      simp only [mul_zero, AddChar.map_zero_eq_one]
      rw [comp_const, if_neg hγ'0]
    · have hk : K ≤ kf y := hK y hy
      have hkf : kf y = (exists_shell_decomp p ϖ hϖ (Units.mk0 y hy0)).choose := dif_neg hy0
      obtain ⟨v, hv⟩ := (exists_shell_decomp p ϖ hϖ (Units.mk0 y hy0)).choose_spec
      rw [hkf] at hk
      set k : ℤ := (exists_shell_decomp p ϖ hϖ (Units.mk0 y hy0)).choose with hkdef
      have hfun : (fun u : UF p => NumberField.StandardAddChar.psiV p (((u : Fx) : F) * y)) =
          fun u => psh p ϖ k (u * v) := by
        funext u
        unfold psh
        congr 1
        have hy' : y = ((ϖ ^ k * (v : Fx) : Fx) : F) := by
          rw [← hv, Units.val_mk0]
        rw [hy', Subgroup.coe_mul]
        simp only [Units.val_mul]
        ring
      have hlvl : IsLvl p δ' (psh p ϖ k) := isLvl_mono p hδ'K (isLvl_psh_of_le p ϖ hϖ K k hk)
      rw [hfun, comp_translate p hlvl, smul_eq_mul]
      refine mul_eq_zero_of_right _ ?_
      have h2 : psh p ϖ k = fun u => (psh p ϖ k u - 1) + 1 := by
        funext u
        ring
      have hc := hcon k δ' hδ'δ hlvl
      rw [← hγ'] at hc
      rw [h2, comp_add, hc, comp_const, if_neg hγ'0, add_zero]
  have h : comp p δ' (fun u => chv (-γ) u) γ' =
      comp p δ' (fun u => ∑ y ∈ T, c y * NumberField.StandardAddChar.psiV p (((u : Fx) : F) * y)) γ' :=
    congrArg (fun f : UF p → ℂ => comp p δ' f γ') (funext hexp)
  rw [hleft, hright] at h
  exact one_ne_zero h

end nonvanishing₂

section commutation

variable (S : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ))
  (hstab : ∀ W ∈ S, ∀ k : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p), (fun g => W (g * k)) ∈ S)
  (hsm : ∀ W ∈ S, ∃ K : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
    IsOpen (K : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) ∧ ∀ k ∈ K, (fun g => W (g * k)) = W)
  (hpsi : ∀ W ∈ S, ∀ (x : HeightOneSpectrum.adicCompletion ℚ p)
    (g : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
    W (unipotentGL2 x * g) = NumberField.StandardAddChar.psiV p x * W g)
  (hirr : ∀ T : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ), T ≤ S →
    (∀ W ∈ T, ∀ k : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p), (fun g => W (g * k)) ∈ T) → T = ⊥ ∨ T = S)
  (hadm : ∀ K : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
    IsOpen (K : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) →
    ∀ T : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ), T ≤ S →
      (∀ W ∈ T, ∀ k ∈ K, (fun g => W (g * k)) = W) → FiniteDimensional ℂ T)
  (hS : S ≠ ⊥)
  (ϖ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ)
  (hϖ : Valued.v (ϖ : HeightOneSpectrum.adicCompletion ℚ p) = WithZero.exp (-1 : ℤ))

private theorem comp_honest_eq {X : Type*} [AddCommGroup X] [Module ℂ X] {δ δ' δ'' : Γ} (h' : δ' ≤ δ) (h'' : δ'' ≤ δ)
    {f : UF p → X} (hf' : IsLvl p δ' f) (hf'' : IsLvl p δ'' f) (γ : Ch p δ) :
    comp p δ' f (refineCh p h' γ) = comp p δ'' f (refineCh p h'' γ) := by
  have e1 := comp_refineCh p (min_le_left δ' δ'') hf' (refineCh p h' γ)
  have e2 := comp_refineCh p (min_le_right δ' δ'') hf'' (refineCh p h'' γ)
  rw [← e1, ← e2]
  congr 1
  apply ext_chv
  intro u
  rw [chv_refineCh, chv_refineCh, chv_refineCh, chv_refineCh]

private noncomputable def ghat {δ : Γ} (γ : Ch p δ) (k : ℤ) : ℂ :=
  comp p (min (lvl k) δ) (fun u => psh p ϖ k u - 1) (refineCh p (min_le_right _ _) γ)

include hϖ in
private theorem isLvl_ghat_level (δ : Γ) (k : ℤ) : IsLvl p (min (lvl k) δ) (psh p ϖ k) :=
  isLvl_mono p (min_le_left _ _) (isLvl_psh_of_le p ϖ hϖ k k le_rfl)

private theorem isLvl_psh_sub_one {δ : Γ} {k : ℤ} (h : IsLvl p δ (psh p ϖ k)) :
    IsLvl p δ (fun u => psh p ϖ k u - 1) := fun u m hm => by
  simp only
  rw [h u m hm]

include hϖ in

private theorem comp_eq_ghat {δ δ' : Γ} (h' : δ' ≤ δ) (k : ℤ) (hk : IsLvl p δ' (psh p ϖ k)) (γ : Ch p δ) :
    comp p δ' (fun u => psh p ϖ k u - 1) (refineCh p h' γ) = ghat p ϖ γ k :=
  comp_honest_eq p h' (min_le_right _ _) (isLvl_psh_sub_one p ϖ hk)
    (isLvl_psh_sub_one p ϖ (isLvl_ghat_level p ϖ hϖ δ k)) γ

include hϖ in
private theorem ghat_eq_zero_of_nonneg {δ : Γ} (γ : Ch p δ) {k : ℤ} (hk : 0 ≤ k) : ghat p ϖ γ k = 0 := by
  unfold ghat
  simp_rw [psh_eq_one_of_nonneg p ϖ hϖ hk, sub_self]
  exact comp_zero p _ _

include hϖ in
private theorem exists_ghat_ne_zero {δ : Γ} (γ : Ch p δ) : ∃ k : ℤ, ghat p ϖ γ k ≠ 0 := by
  by_cases hγ : γ = 0
  · subst hγ
    obtain ⟨k, δ₁, hlvl, hne⟩ := exists_gco_zero_ne_zero p ϖ hϖ
    refine ⟨k, ?_⟩
    have h := comp_eq_ghat p ϖ hϖ (min_le_right δ₁ δ) k (isLvl_mono p (min_le_left _ _) hlvl) (0 : Ch p δ)
    rw [← h, refineCh_zero]
    have h2 := comp_refineCh p (min_le_left δ₁ δ) (isLvl_psh_sub_one p ϖ hlvl) (0 : Ch p δ₁)
    rw [refineCh_zero] at h2
    rw [h2]
    exact hne
  · obtain ⟨k, δ', h', hlvl, hne⟩ := exists_honest_gco_ne_zero_of_ne_zero p ϖ hϖ γ hγ
    exact ⟨k, by rw [← comp_eq_ghat p ϖ hϖ h' k hlvl γ]; exact hne⟩

include hϖ in

private theorem exists_top_ghat {δ : Γ} (γ : Ch p δ) :
    ∃ k₀ : ℤ, ghat p ϖ γ k₀ ≠ 0 ∧ (∀ k : ℤ, k₀ < k → ghat p ϖ γ k = 0) ∧ k₀ < 0 := by
  classical
  obtain ⟨k₀, hk₀, hmax⟩ := Int.exists_greatest_of_bdd (P := fun k => ghat p ϖ γ k ≠ 0)
    ⟨-1, fun k hk => by
      by_contra h
      exact hk (ghat_eq_zero_of_nonneg p ϖ hϖ γ (by omega))⟩
    (exists_ghat_ne_zero p ϖ hϖ γ)
  refine ⟨k₀, hk₀, fun k hk => ?_, ?_⟩
  · by_contra h
    exact absurd (hmax k h) (not_le.mpr hk)
  · by_contra h
    exact hk₀ (ghat_eq_zero_of_nonneg p ϖ hϖ γ (not_lt.mp h))

local notation "COP" => Cop p S hstab hsm hpsi ϖ hϖ
local notation "QD" => (G → ℂ) ⧸ defectSpan p S

private noncomputable def cbr {δ : Γ} (τ α : Ch p δ) (ξ : coinv p S) (d b : ℤ) : QD :=
  ((COP (b + d) α (COP b τ ξ) : coinv p S) : QD) - ((COP b τ (COP (b + d) α ξ) : coinv p S) : QD)

private theorem sum_ghat_comm_eq_zero {δ : Γ} (hδ : ∀ m ∈ Um p δ, omega p S hstab hsm hirr hadm (m : Fx) = 1)
    (τ α : Ch p δ) (ξ : coinv p S) (d n K : ℤ)
    (hKn : ∀ k : ℤ, k < K → COP (n + k) τ ξ = 0) (hKj : ∀ k : ℤ, k < K → COP (n + d + k) α ξ = 0)
    (δw : Γ) (hw : δw ≤ δ) (hwψ : ∀ k : ℤ, K ≤ k → IsLvl p δw (psh p ϖ k)) (hwn : IsLvl p δw (psh p ϖ n))
    (hwj : IsLvl p δw (psh p ϖ (n + d))) :
    ∑ k ∈ Finset.Ico K 0,
      (pik p S hstab hsm hirr hadm ϖ k * ghat p ϖ (-α + (omCh p S hstab hsm hirr hadm hS δ hδ + -τ)) k) •
        cbr p S hstab hsm hpsi ϖ hϖ τ α ξ d (n + k) = 0 := by
  have hδw : ∀ m ∈ Um p δw, omega p S hstab hsm hirr hadm (m : Fx) = 1 := fun m hm => hδ m (Um_mono p hw hm)
  have h := sum_commutator_eq_zero p S hstab hsm hpsi hirr hadm hS ϖ hϖ δw hδw n (n + d) (refineCh p hw τ)
    (refineCh p hw α) ξ K (by simpa only [Cop_refineCh p S hstab hsm hpsi ϖ hϖ hw] using hKn)
    (by simpa only [Cop_refineCh p S hstab hsm hpsi ϖ hϖ hw] using hKj) hwψ hwn hwj
  simp only [Cop_refineCh p S hstab hsm hpsi ϖ hϖ hw] at h
  have hchar : -refineCh p hw α + (omCh p S hstab hsm hirr hadm hS δw hδw + -refineCh p hw τ) =
      refineCh p hw (-α + (omCh p S hstab hsm hirr hadm hS δ hδ + -τ)) := by
    apply ext_chv
    intro u
    simp only [chv_add, chv_neg, chv_refineCh, chv_omCh]
  rw [hchar] at h
  refine (Finset.sum_congr rfl fun k hk => ?_).trans h
  unfold cbr gco
  rw [comp_eq_ghat p ϖ hϖ hw k (hwψ k (Finset.mem_Ico.mp hk).1), show k + (n + d) = n + k + d by ring,
    show k + n = n + k by ring, show n + d + k = n + k + d by ring]

include hS in

private theorem comm_eq_zero {δ : Γ} (hδ : ∀ m ∈ Um p δ, omega p S hstab hsm hirr hadm (m : Fx) = 1)
    (τ α : Ch p δ) (ξ : coinv p S) (d : ℤ) (b : ℤ) : cbr p S hstab hsm hpsi ϖ hϖ τ α ξ d b = 0 := by
  obtain ⟨m₀, hm₀⟩ := exists_forall_Cop_eq_zero p S hstab hsm hpsi hirr hadm ϖ hϖ hS τ ξ
  obtain ⟨m₁, hm₁⟩ := exists_forall_Cop_eq_zero p S hstab hsm hpsi hirr hadm ϖ hϖ hS α ξ
  set B₀ : ℤ := min m₀ (m₁ - d) with hB₀
  have hbase : ∀ b : ℤ, b < B₀ → cbr p S hstab hsm hpsi ϖ hϖ τ α ξ d b = 0 := by
    intro b hb
    unfold cbr
    rw [hm₀ b (by omega), hm₁ (b + d) (by omega), map_zero, map_zero, Submodule.coe_zero, sub_zero]
  set γ : Ch p δ := -α + (omCh p S hstab hsm hirr hadm hS δ hδ + -τ) with hγ
  obtain ⟨k₀, hk₀, htop, hk₀neg⟩ := exists_top_ghat p ϖ hϖ γ
  induction' hb : (b - B₀).toNat using Nat.strong_induction_on with m ih generalizing b
  by_cases hbB : b < B₀
  · exact hbase b hbB
  · push Not at hbB
    set n : ℤ := b - k₀ with hn
    set K : ℤ := B₀ - n with hK
    have hKn : ∀ k : ℤ, k < K → COP (n + k) τ ξ = 0 := fun k hk => hm₀ _ (by omega)
    have hKj : ∀ k : ℤ, k < K → COP (n + d + k) α ξ = 0 := fun k hk => hm₁ _ (by omega)
    set Kw : ℤ := min K (min n (n + d)) with hKw
    have hwψ : ∀ k : ℤ, Kw ≤ k → IsLvl p (min (lvl Kw) δ) (psh p ϖ k) := fun k hk =>
      isLvl_mono p (min_le_left _ _) (isLvl_psh_of_le p ϖ hϖ Kw k hk)
    have hrel := sum_ghat_comm_eq_zero p S hstab hsm hpsi hirr hadm hS ϖ hϖ hδ τ α ξ d n K hKn hKj
      (min (lvl Kw) δ) (min_le_right _ _) (fun k hk => hwψ k (by omega)) (hwψ n (by omega))
      (hwψ (n + d) (by omega))
    rw [← hγ] at hrel
    rw [Finset.sum_eq_single k₀] at hrel
    · have hne : pik p S hstab hsm hirr hadm ϖ k₀ * ghat p ϖ γ k₀ ≠ 0 :=
        mul_ne_zero (omega_ne_zero p S hstab hsm hirr hadm hS _) hk₀
      have h := smul_cancel_of_ne_zero hne (hrel.trans (smul_zero _).symm)
      rwa [show n + k₀ = b by omega] at h
    · intro k hk hkne
      obtain ⟨hkK, hk0⟩ := Finset.mem_Ico.mp hk
      rcases lt_or_gt_of_ne hkne with hlt | hgt
      · rw [ih ((n + k - B₀).toNat) (by omega) (n + k) rfl, smul_zero]
      · rw [htop k hgt, mul_zero, zero_smul]
    · intro hmem
      exact absurd (Finset.mem_Ico.mpr ⟨by omega, hk₀neg⟩) hmem

include hirr hadm hS in

private theorem Cop_mul_comm {δ₁ δ₂ : Γ} (τ : Ch p δ₁) (α : Ch p δ₂) (a b : ℤ) :
    COP a α * COP b τ = COP b τ * COP a α := by
  obtain ⟨δω, hδω⟩ := exists_forall_omega_eq_one p S hstab hsm hirr hadm hS
  set δ : Γ := min (min δ₁ δ₂) δω with hδdef
  have h1 : δ ≤ δ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have h2 : δ ≤ δ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have h3 : δ ≤ δω := min_le_right _ _
  have hδ : ∀ m ∈ Um p δ, omega p S hstab hsm hirr hadm (m : Fx) = 1 := fun m hm =>
    hδω _ (lt_of_lt_of_le ((mem_Um_iff p δ m).mp hm) (Units.val_le_val.mpr h3))
  apply LinearMap.ext
  intro ξ
  apply Subtype.ext
  have h := comm_eq_zero p S hstab hsm hpsi hirr hadm hS ϖ hϖ hδ (refineCh p h1 τ) (refineCh p h2 α) ξ (a - b) b
  unfold cbr at h
  rw [show b + (a - b) = a by ring, Cop_refineCh p S hstab hsm hpsi ϖ hϖ, Cop_refineCh p S hstab hsm hpsi ϖ hϖ,
    sub_eq_zero] at h
  rw [Module.End.mul_apply, Module.End.mul_apply]
  exact h

end commutation

private def evalOne : (G → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj (1 : G)

@[scoped simp] private theorem evalOne_apply (V : G → ℂ) : evalOne p V = V 1 := rfl

private theorem defectSpan_le_ker_evalOne (S : Submodule ℂ (G → ℂ))
    (hpsi : ∀ W ∈ S, ∀ (x : F) (g : G),
      W (unipotentGL2 x * g) = NumberField.StandardAddChar.psiV p x * W g) :
    defectSpan p S ≤ LinearMap.ker (evalOne p) := by
  refine Submodule.span_le.mpr ?_
  rintro V ⟨U, hU, x, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, evalOne_apply, Pi.sub_apply, Pi.smul_apply, one_mul,
    smul_eq_mul]
  have h := hpsi U hU x 1
  rw [mul_one] at h
  rw [h, sub_self]

private noncomputable def evalQ (S : Submodule ℂ (G → ℂ))
    (hpsi : ∀ W ∈ S, ∀ (x : F) (g : G),
      W (unipotentGL2 x * g) = NumberField.StandardAddChar.psiV p x * W g) :
    ((G → ℂ) ⧸ defectSpan p S) →ₗ[ℂ] ℂ :=
  (defectSpan p S).liftQ (evalOne p) (defectSpan_le_ker_evalOne p S hpsi)

@[scoped simp] private theorem evalQ_mkQ (S : Submodule ℂ (G → ℂ))
    (hpsi : ∀ W ∈ S, ∀ (x : F) (g : G),
      W (unipotentGL2 x * g) = NumberField.StandardAddChar.psiV p x * W g) (V : G → ℂ) :
    evalQ p S hpsi ((defectSpan p S).mkQ V) = V 1 := rfl

section bruhat

private theorem eq_mul_of_ne_zero (g : G) {a b c d : F} (hg : (g : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d])
    (hd : d ≠ 0) (he : a * d - b * c ≠ 0) :
    g = unipotentGL2 (b / d) * (zG p (Units.mk0 d hd) *
      (dg p (Units.mk0 (a * d - b * c) he * ((Units.mk0 d hd)⁻¹ * (Units.mk0 d hd)⁻¹)) *
        (wG p * (unipotentGL2 (c / d) * wG p)))) := by
  apply Units.ext
  simp only [Units.val_mul, unipotentGL2_coe, zG_coe, dg_coe, wG_coe, Units.val_mk0, Units.val_inv_eq_inv_val]
  rw [hg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp
  ring

private theorem eq_mul_of_eq_zero (g : G) {a b c : F} (hg : (g : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, 0])
    (hb : b ≠ 0) (hc : c ≠ 0) :
    g = unipotentGL2 (a / c) * (zG p (Units.mk0 c hc) * (dg p (Units.mk0 b hb * (Units.mk0 c hc)⁻¹) * wG p)) := by
  apply Units.ext
  simp only [Units.val_mul, unipotentGL2_coe, zG_coe, dg_coe, wG_coe, Units.val_mk0, Units.val_inv_eq_inv_val]
  rw [hg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

private theorem rT_mem_of_forall_gen (W : Submodule ℂ (G → ℂ))
    (hN : ∀ x : F, ∀ V ∈ W, rT p (unipotentGL2 x) V ∈ W) (hD : ∀ t : Fx, ∀ V ∈ W, rT p (dg p t) V ∈ W)
    (hZ : ∀ c : Fx, ∀ V ∈ W, rT p (zG p c) V ∈ W) (hW : ∀ V ∈ W, rT p (wG p) V ∈ W) (g : G) {V : G → ℂ}
    (hV : V ∈ W) : rT p g V ∈ W := by
  obtain ⟨a, b, c, d, hg⟩ : ∃ a b c d : F, (g : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have he : a * d - b * c ≠ 0 := by
    rw [← Matrix.det_fin_two_of, ← hg]
    exact (Matrix.isUnits_det_units g).ne_zero
  by_cases hd : d = 0
  · subst hd
    have hb : b ≠ 0 := fun h => he (by rw [h]; ring)
    have hc : c ≠ 0 := fun h => he (by rw [h]; ring)
    rw [eq_mul_of_eq_zero p g hg hb hc, ← rT_rT, ← rT_rT, ← rT_rT]
    exact hN _ _ (hZ _ _ (hD _ _ (hW _ hV)))
  · rw [eq_mul_of_ne_zero p g hg hd he, ← rT_rT, ← rT_rT, ← rT_rT, ← rT_rT, ← rT_rT]
    exact hN _ _ (hZ _ _ (hD _ _ (hW _ (hN _ _ (hW _ hV)))))

end bruhat

section invariant

variable (S : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ))
  (hstab : ∀ W ∈ S, ∀ k : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p), (fun g => W (g * k)) ∈ S)
  (hsm : ∀ W ∈ S, ∃ K : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
    IsOpen (K : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) ∧ ∀ k ∈ K, (fun g => W (g * k)) = W)
  (hpsi : ∀ W ∈ S, ∀ (x : HeightOneSpectrum.adicCompletion ℚ p)
    (g : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
    W (unipotentGL2 x * g) = NumberField.StandardAddChar.psiV p x * W g)
  (hirr : ∀ T : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ), T ≤ S →
    (∀ W ∈ T, ∀ k : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p), (fun g => W (g * k)) ∈ T) → T = ⊥ ∨ T = S)
  (hadm : ∀ K : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
    IsOpen (K : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) →
    ∀ T : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ), T ≤ S →
      (∀ W ∈ T, ∀ k ∈ K, (fun g => W (g * k)) = W) → FiniteDimensional ℂ T)
  (hS : S ≠ ⊥)
  (ϖ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ)
  (hϖ : Valued.v (ϖ : HeightOneSpectrum.adicCompletion ℚ p) = WithZero.exp (-1 : ℤ))

local notation "COP" => Cop p S hstab hsm hpsi ϖ hϖ
local notation "BUMP" => bump p S hstab hsm ϖ hϖ
local notation "QD" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ) ⧸ defectSpan p S

private theorem shell_zero (n : ℤ) (u : UF p) : shell p S ϖ (0 : G → ℂ) n u = 0 := by
  unfold shell kirillov
  rw [map_zero, map_zero]

private theorem shell_zero_one (V : G → ℂ) : shell p S ϖ V 0 (1 : UF p) = (defectSpan p S).mkQ V := by
  unfold shell
  rw [zpow_zero, OneMemClass.coe_one, mul_one, kirillov_one]

include hstab hsm hϖ in

private theorem exists_forall_shell_eq_zero_of_le {V : G → ℂ} (hV : V ∈ S) :
    ∃ M : ℤ, ∀ k : ℤ, k ≤ M → ∀ u : UF p, shell p S ϖ V k u = 0 := by
  obtain ⟨β, hβ⟩ := exists_forall_kirillov_eq_zero p S hstab hsm hV
  refine ⟨-WithZero.log (β : WithZero (Multiplicative ℤ)), fun k hk u => ?_⟩
  apply hβ
  rw [Units.val_mul, map_mul, v_coe_UF, mul_one, v_pi_zpow p ϖ hϖ, ← WithZero.exp_log β.ne_zero,
    WithZero.exp_le_exp]
  omega

include hϖ in

private theorem exists_zpow_mul (t : Fx) : ∃ (m : ℤ) (ν : UF p), t = ϖ ^ m * (ν : Fx) := by
  have ht : Valued.v (t : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr t.ne_zero
  refine ⟨-WithZero.log (Valued.v (t : F)), ⟨(ϖ ^ (-WithZero.log (Valued.v (t : F))))⁻¹ * t, ?_⟩, ?_⟩
  · show Valued.v ((((ϖ ^ (-WithZero.log (Valued.v (t : F))))⁻¹ * t : Fx) : F)) = 1
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, v_pi_zpow p ϖ hϖ, neg_neg,
      WithZero.exp_log ht, inv_mul_cancel₀ ht]
  · exact (mul_inv_cancel_left _ _).symm

private theorem comp_mem {X : Type*} [AddCommGroup X] [Module ℂ X] (T : Submodule ℂ X) (δ : Γ) {f : UF p → X}
    (hf : ∀ u : UF p, f u ∈ T) (σ : Ch p δ) : comp p δ f σ ∈ T := by
  unfold comp
  exact T.smul_mem _ (T.sum_mem fun q _ => T.smul_mem _ (hf _))

private def vzero (T : Submodule ℂ QD) : Submodule ℂ (G → ℂ) where
  carrier := {V | V ∈ S ∧ (∃ N : ℤ, ∀ k : ℤ, N ≤ k → ∀ u : UF p, shell p S ϖ V k u = 0) ∧
    ∀ (k : ℤ) (u : UF p), shell p S ϖ V k u ∈ T}
  add_mem' := by
    rintro V V' ⟨hV, ⟨N, hN⟩, hT⟩ ⟨hV', ⟨N', hN'⟩, hT'⟩
    refine ⟨S.add_mem hV hV', ⟨max N N', fun k hk u => ?_⟩, fun k u => ?_⟩
    · rw [shell_add, hN k ((le_max_left N N').trans hk) u, hN' k ((le_max_right N N').trans hk) u, add_zero]
    · rw [shell_add]
      exact T.add_mem (hT k u) (hT' k u)
  zero_mem' := ⟨S.zero_mem, ⟨0, fun k _ u => shell_zero p S ϖ k u⟩, fun k u => by
    rw [shell_zero]
    exact T.zero_mem⟩
  smul_mem' := by
    rintro c V ⟨hV, ⟨N, hN⟩, hT⟩
    refine ⟨S.smul_mem c hV, ⟨N, fun k hk u => ?_⟩, fun k u => ?_⟩
    · rw [shell_smul, hN k hk u, smul_zero]
    · rw [shell_smul]
      exact T.smul_mem c (hT k u)

private theorem mem_vzero_iff (T : Submodule ℂ QD) (V : G → ℂ) :
    V ∈ vzero p S ϖ T ↔ V ∈ S ∧ (∃ N : ℤ, ∀ k : ℤ, N ≤ k → ∀ u : UF p, shell p S ϖ V k u = 0) ∧
      ∀ (k : ℤ) (u : UF p), shell p S ϖ V k u ∈ T := Iff.rfl

private theorem vzero_le (T : Submodule ℂ QD) : vzero p S ϖ T ≤ S := fun _ hV => ((mem_vzero_iff p S ϖ T _).mp hV).1

private abbrev wzero (T : Submodule ℂ QD) : Submodule ℂ (G → ℂ) := vzero p S ϖ T ⊔ (vzero p S ϖ T).map (rT p (wG p))

include hstab in
private theorem wzero_le (T : Submodule ℂ QD) : wzero p S ϖ T ≤ S := by
  refine sup_le (vzero_le p S ϖ T) fun V hV => ?_
  obtain ⟨V₁, hV₁, rfl⟩ := Submodule.mem_map.mp hV
  exact hstab V₁ (vzero_le p S ϖ T hV₁) (wG p)

include hstab in
private theorem rT_unipotent_mem_vzero (T : Submodule ℂ QD) (x : F) {V : G → ℂ} (hV : V ∈ vzero p S ϖ T) :
    rT p (unipotentGL2 x) V ∈ vzero p S ϖ T := by
  obtain ⟨hVS, ⟨N, hN⟩, hT⟩ := (mem_vzero_iff p S ϖ T V).mp hV
  have hsh : ∀ (k : ℤ) (u : UF p), shell p S ϖ (rT p (unipotentGL2 x) V) k u =
      NumberField.StandardAddChar.psiV p (((ϖ ^ k * (u : Fx) : Fx) : F) * x) • shell p S ϖ V k u :=
    fun k u => kirillov_rT_unipotent p S hstab hVS x _
  refine (mem_vzero_iff p S ϖ T _).mpr ⟨hstab V hVS _, ⟨N, fun k hk u => ?_⟩, fun k u => ?_⟩
  · rw [hsh, hN k hk u, smul_zero]
  · rw [hsh]
    exact T.smul_mem _ (hT k u)

include hstab hϖ in
private theorem rT_dg_mem_vzero (T : Submodule ℂ QD) (t : Fx) {V : G → ℂ} (hV : V ∈ vzero p S ϖ T) :
    rT p (dg p t) V ∈ vzero p S ϖ T := by
  obtain ⟨hVS, ⟨N, hN⟩, hT⟩ := (mem_vzero_iff p S ϖ T V).mp hV
  obtain ⟨m, ν, rfl⟩ := exists_zpow_mul p ϖ hϖ t
  have hsh : ∀ (k : ℤ) (u : UF p), shell p S ϖ (rT p (dg p (ϖ ^ m * (ν : Fx))) V) k u =
      shell p S ϖ V (k + m) (u * ν) := by
    intro k u
    unfold shell
    rw [kirillov_rT_dg, zpow_add, Subgroup.coe_mul, mul_mul_mul_comm]
  refine (mem_vzero_iff p S ϖ T _).mpr ⟨hstab V hVS _, ⟨N - m, fun k hk u => ?_⟩, fun k u => ?_⟩
  · rw [hsh, hN (k + m) (by omega) (u * ν)]
  · rw [hsh]
    exact hT _ _

include hstab hsm hirr hadm in
private theorem rT_zG_mem_of_le {W : Submodule ℂ (G → ℂ)} (hW : W ≤ S) (c : Fx) {V : G → ℂ} (hV : V ∈ W) :
    rT p (zG p c) V ∈ W := by
  rw [rT_zG_eq p S hstab hsm hirr hadm c (hW hV)]
  exact W.smul_mem _ hV

include hstab hsm hpsi hirr hadm hϖ in

private theorem shell_rT_wG_mem (T : Submodule ℂ QD)
    (hT : ∀ (δ : Γ) (n : ℤ) (τ : Ch p δ) (ξ : coinv p S), (ξ : QD) ∈ T → ((COP n τ ξ : coinv p S) : QD) ∈ T)
    {V : G → ℂ} (hV : V ∈ vzero p S ϖ T) (k : ℤ) (u : UF p) : shell p S ϖ (rT p (wG p) V) k u ∈ T := by
  obtain ⟨hVS, ⟨N, hN⟩, hTV⟩ := (mem_vzero_iff p S ϖ T V).mp hV
  obtain ⟨M, hM⟩ := exists_forall_shell_eq_zero_of_le p S hstab hsm ϖ hϖ hVS
  obtain ⟨δ, hδ⟩ := exists_forall_isLvl_shell p S hsm ϖ hVS
  have hwin : ∀ j : ℤ, j ∉ Finset.Ioo M N → ∀ v : UF p, shell p S ϖ V j v = 0 := by
    intro j hj v
    rw [Finset.mem_Ioo] at hj
    rcases le_or_gt j M with h | h
    · exact hM j h v
    · exact hN j (by omega) v
  rw [eq_sum_bump p S hstab hsm hpsi ϖ hϖ hVS (Finset.Ioo M N) hwin fun j _ => hδ δ le_rfl j]
  simp_rw [map_sum, shell_sum]
  refine T.sum_mem fun j _ => T.sum_mem fun σ _ => ?_
  rw [shell_rT_wG_bump p S hstab hsm hpsi hirr hadm ϖ hϖ]
  refine T.smul_mem _ (hT δ (j + k) (-σ) _ ?_)
  rw [coe_melC]
  exact comp_mem p T δ (fun v => hTV j v) σ

include hstab hsm hpsi hirr hadm hϖ in

private theorem rT_unipotent_rT_wG_sub_mem (T : Submodule ℂ QD)
    (hT : ∀ (δ : Γ) (n : ℤ) (τ : Ch p δ) (ξ : coinv p S), (ξ : QD) ∈ T → ((COP n τ ξ : coinv p S) : QD) ∈ T)
    (x : F) {V : G → ℂ} (hV : V ∈ vzero p S ϖ T) :
    rT p (unipotentGL2 x) (rT p (wG p) V) - rT p (wG p) V ∈ vzero p S ϖ T := by
  have hVS : V ∈ S := vzero_le p S ϖ T hV
  have hwS : rT p (wG p) V ∈ S := hstab V hVS _
  have hsh : ∀ (k : ℤ) (u : UF p), shell p S ϖ (rT p (unipotentGL2 x) (rT p (wG p) V) - rT p (wG p) V) k u =
      (NumberField.StandardAddChar.psiV p (((ϖ ^ k * (u : Fx) : Fx) : F) * x) - 1) •
        shell p S ϖ (rT p (wG p) V) k u := by
    intro k u
    rw [shell_sub, sub_smul, one_smul]
    congr 1
    exact kirillov_rT_unipotent p S hstab hwS x _

  obtain ⟨N, hN⟩ : ∃ N : ℤ, ∀ k : ℤ, N ≤ k → ∀ u : UF p,
      NumberField.StandardAddChar.psiV p (((ϖ ^ k * (u : Fx) : Fx) : F) * x) = 1 := by
    rcases eq_or_ne x 0 with rfl | hx
    · exact ⟨0, fun k _ u => by rw [mul_zero, AddChar.map_zero_eq_one]⟩
    · have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
      refine ⟨WithZero.log (Valued.v x), fun k hk u => ?_⟩
      apply NumberField.StandardAddChar.psiV_eq_one_of_mem_integers
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, Units.val_mul, map_mul, v_coe_UF, mul_one,
        v_pi_zpow p ϖ hϖ, ← WithZero.exp_log hvx, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
  refine (mem_vzero_iff p S ϖ T _).mpr ⟨S.sub_mem (hstab _ hwS _) hwS, ⟨N, fun k hk u => ?_⟩, fun k u => ?_⟩
  · rw [hsh, hN k hk u, sub_self, zero_smul]
  · rw [hsh]
    exact T.smul_mem _ (shell_rT_wG_mem p S hstab hsm hpsi hirr hadm ϖ hϖ T hT hV k u)

include hstab hsm hpsi hirr hadm hϖ in

private theorem rT_mem_wzero (T : Submodule ℂ QD)
    (hT : ∀ (δ : Γ) (n : ℤ) (τ : Ch p δ) (ξ : coinv p S), (ξ : QD) ∈ T → ((COP n τ ξ : coinv p S) : QD) ∈ T)
    (g : G) {V : G → ℂ} (hV : V ∈ wzero p S ϖ T) : rT p g V ∈ wzero p S ϖ T := by
  have hvw : ∀ V₁ ∈ vzero p S ϖ T, V₁ ∈ wzero p S ϖ T := fun V₁ h => Submodule.mem_sup_left h
  have hww : ∀ V₁ ∈ vzero p S ϖ T, rT p (wG p) V₁ ∈ wzero p S ϖ T := fun V₁ h =>
    Submodule.mem_sup_right (Submodule.mem_map_of_mem h)

  have hpair : ∀ k : G, (∀ V₁ ∈ vzero p S ϖ T, rT p k V₁ ∈ wzero p S ϖ T) →
      (∀ V₁ ∈ vzero p S ϖ T, rT p k (rT p (wG p) V₁) ∈ wzero p S ϖ T) →
      ∀ V ∈ wzero p S ϖ T, rT p k V ∈ wzero p S ϖ T := by
    intro k h₁ h₂ V hV
    obtain ⟨V₁, hV₁, V₂, hV₂, rfl⟩ := Submodule.mem_sup.mp hV
    obtain ⟨V₃, hV₃, rfl⟩ := Submodule.mem_map.mp hV₂
    rw [map_add]
    exact (wzero p S ϖ T).add_mem (h₁ V₁ hV₁) (h₂ V₃ hV₃)
  refine rT_mem_of_forall_gen p (wzero p S ϖ T) (fun x => hpair _ ?_ ?_) (fun t => hpair _ ?_ ?_)
    (fun c V hV => rT_zG_mem_of_le p S hstab hsm hirr hadm (wzero_le p S hstab ϖ T) c hV) (hpair _ ?_ ?_) g hV
  · exact fun V₁ h => hvw _ (rT_unipotent_mem_vzero p S hstab ϖ T x h)
  · intro V₁ h
    have e : rT p (unipotentGL2 x) (rT p (wG p) V₁) =
        rT p (wG p) V₁ + (rT p (unipotentGL2 x) (rT p (wG p) V₁) - rT p (wG p) V₁) := by abel
    rw [e]
    exact (wzero p S ϖ T).add_mem (hww _ h)
      (hvw _ (rT_unipotent_rT_wG_sub_mem p S hstab hsm hpsi hirr hadm ϖ hϖ T hT x h))
  · exact fun V₁ h => hvw _ (rT_dg_mem_vzero p S hstab ϖ hϖ T t h)
  · intro V₁ h
    rw [rT_rT, dg_mul_wG, ← rT_rT, ← rT_rT]
    exact hww _ (rT_zG_mem_of_le p S hstab hsm hirr hadm (vzero_le p S ϖ T) t (rT_dg_mem_vzero p S hstab ϖ hϖ T t⁻¹ h))
  · exact fun V₁ h => hww _ h
  · intro V₁ h
    rw [rT_rT, wG_mul_wG, rT_one]
    exact hvw _ h

include hstab hsm hpsi hirr hadm hϖ in

private theorem eq_top_of_ne_bot (W : Submodule ℂ (coinv p S))
    (hW : ∀ (δ : Γ) (n : ℤ) (τ : Ch p δ), ∀ ξ ∈ W, COP n τ ξ ∈ W) (hW0 : W ≠ ⊥) : W = ⊤ := by
  set T : Submodule ℂ QD := W.map (coinv p S).subtype
  have hmemT : ∀ ξ : coinv p S, (ξ : QD) ∈ T ↔ ξ ∈ W := by
    intro ξ
    constructor
    · intro h
      obtain ⟨η, hη, hηξ⟩ := Submodule.mem_map.mp h
      rwa [(coinv p S).injective_subtype hηξ] at hη
    · intro h
      exact Submodule.mem_map_of_mem h
  have hT : ∀ (δ : Γ) (n : ℤ) (τ : Ch p δ) (ξ : coinv p S), (ξ : QD) ∈ T → ((COP n τ ξ : coinv p S) : QD) ∈ T :=
    fun δ n τ ξ h => (hmemT _).mpr (hW δ n τ ξ ((hmemT ξ).mp h))

  obtain ⟨ξ, hξW, hξ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hE : BUMP 0 (0 : Ch p 1) ξ ∈ vzero p S ϖ T := by
    refine (mem_vzero_iff p S ϖ T _).mpr
      ⟨bump_mem p S hstab hsm ϖ hϖ 0 (0 : Ch p 1) ξ, ⟨1, fun k hk u => ?_⟩, fun k u => ?_⟩
    · rw [shell_bump, if_neg (show ¬ (k = 0) by omega)]
    · rw [shell_bump]
      split_ifs
      · rw [chv_zero, one_smul]
        exact (hmemT ξ).mpr hξW
      · exact T.zero_mem
  have hE0 : BUMP 0 (0 : Ch p 1) ξ ≠ 0 := by
    intro h
    have h1 := shell_bump p S hstab hsm ϖ hϖ 0 (0 : Ch p 1) ξ 0 1
    rw [h, shell_zero, if_pos rfl, chv_zero, one_smul] at h1
    exact hξ0 (Subtype.ext h1.symm)

  have hwz : wzero p S ϖ T = S := by
    refine (hirr _ (wzero_le p S hstab ϖ T) fun V hV k =>
      rT_mem_wzero p S hstab hsm hpsi hirr hadm ϖ hϖ T hT k hV).resolve_left ?_
    intro hbot
    have hmem : BUMP 0 (0 : Ch p 1) ξ ∈ wzero p S ϖ T := Submodule.mem_sup_left hE
    rw [hbot, Submodule.mem_bot] at hmem
    exact hE0 hmem

  refine eq_top_iff.mpr ?_
  intro η _
  obtain ⟨V, hVS, hVη⟩ := Submodule.mem_map.mp η.2
  rw [← hmemT, ← hVη]
  rw [← hwz] at hVS
  obtain ⟨V₁, hV₁, V₂, hV₂, rfl⟩ := Submodule.mem_sup.mp hVS
  obtain ⟨V₃, hV₃, rfl⟩ := Submodule.mem_map.mp hV₂
  rw [← shell_zero_one p S ϖ, shell_add]
  exact T.add_mem (((mem_vzero_iff p S ϖ T V₁).mp hV₁).2.2 0 1)
    (shell_rT_wG_mem p S hstab hsm hpsi hirr hadm ϖ hϖ T hT hV₃ 0 1)

end invariant

section countable

private theorem exists_lower_unipotent_mem_of_isOpen (K : Subgroup G) (hK : IsOpen (K : Set G)) :
    ∃ δ : Γ, ∀ y : F, Valued.v y < (δ : WithZero (Multiplicative ℤ)) → wG p * (unipotentGL2 y * wG p) ∈ K := by
  have hc : Continuous (fun y : F => wG p * (unipotentGL2 y * wG p)) :=
    continuous_const.mul ((continuous_unipotentGL2 p).mul continuous_const)
  have hU : ((fun y : F => wG p * (unipotentGL2 y * wG p)) ⁻¹' (K : Set G)) ∈ nhds (0 : F) := by
    apply (hK.preimage hc).mem_nhds
    show wG p * (unipotentGL2 (0 : F) * wG p) ∈ K
    rw [unipotentGL2_zero, one_mul, wG_mul_wG]
    exact K.one_mem
  exact exists_ball_subset_of_mem_nhds p hU

private def genSet (δ : Γ) : Set G :=
  {g | (∃ x : F, Valued.v x < (δ : WithZero (Multiplicative ℤ)) ∧ g = unipotentGL2 x) ∨
    (∃ y : F, Valued.v y < (δ : WithZero (Multiplicative ℤ)) ∧ g = wG p * (unipotentGL2 y * wG p)) ∨
    (∃ t : Fx, Valued.v ((t : F) - 1) < (δ : WithZero (Multiplicative ℤ)) ∧ g = dg p t) ∨
    ∃ c : Fx, Valued.v ((c : F) - 1) < (δ : WithZero (Multiplicative ℤ)) ∧ g = zG p c}

private def congSub (δ : Γ) : Subgroup G := Subgroup.closure (genSet p δ)

private theorem exists_lvl_neg_le (δ : Γ) : ∃ m : ℕ, lvl (-(m : ℤ)) ≤ δ := by
  refine ⟨(-WithZero.log (δ : WithZero (Multiplicative ℤ))).toNat, ?_⟩
  rw [← Units.val_le_val, lvl_val]
  conv_rhs => rw [← WithZero.exp_log δ.ne_zero]
  rw [WithZero.exp_le_exp]
  omega

private theorem exists_congSub_le (K : Subgroup G) (hK : IsOpen (K : Set G)) :
    ∃ m : ℕ, congSub p (lvl (-(m : ℤ))) ≤ K := by
  obtain ⟨δ₁, h₁⟩ := exists_unipotent_mem_of_isOpen p K hK
  obtain ⟨δ₂, h₂⟩ := exists_lower_unipotent_mem_of_isOpen p K hK
  obtain ⟨δ₃, h₃⟩ := exists_dg_mem_of_isOpen p K hK
  obtain ⟨δ₄, h₄⟩ := exists_zG_mem_of_isOpen p K hK
  obtain ⟨m, hm⟩ := exists_lvl_neg_le (min (min δ₁ δ₂) (min δ₃ δ₄))
  have hle : ∀ {z : F}, Valued.v z < ((lvl (-(m : ℤ)) : Γ) : WithZero (Multiplicative ℤ)) →
      ∀ {δ' : Γ}, min (min δ₁ δ₂) (min δ₃ δ₄) ≤ δ' → Valued.v z < (δ' : WithZero (Multiplicative ℤ)) :=
    fun {_} hz {_} hδ' => hz.trans_le (Units.val_le_val.mpr (hm.trans hδ'))
  refine ⟨m, (Subgroup.closure_le K).mpr fun g hg => ?_⟩
  simp only [genSet, Set.mem_setOf_eq] at hg
  rcases hg with ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨c, hc, rfl⟩
  · exact h₁ x (hle hx ((min_le_left _ _).trans (min_le_left _ _)))
  · exact h₂ y (hle hy ((min_le_left _ _).trans (min_le_right _ _)))
  · exact h₃ t (hle ht ((min_le_right _ _).trans (min_le_left _ _)))
  · exact h₄ c (hle hc ((min_le_right _ _).trans (min_le_right _ _)))

private theorem v_eq_one_of_close {δ : Γ} (hδ : δ ≤ 1) {x : F}
    (hx : Valued.v (x - 1) < (δ : WithZero (Multiplicative ℤ))) : Valued.v x = 1 := by
  have h1 : Valued.v (x - 1) < Valued.v (1 : F) := by
    rw [map_one]
    exact hx.trans_le (Units.val_le_val.mpr hδ)
  have h := Valued.v.map_add_eq_of_lt_right h1
  rwa [sub_add_cancel, map_one] at h

private theorem mem_congSub_of_close {δ : Γ} (hδ : δ ≤ 1) (g : G)
    (hg : ∀ i j : Fin 2, Valued.v ((g : Matrix (Fin 2) (Fin 2) F) i j - (1 : Matrix (Fin 2) (Fin 2) F) i j) <
      (δ : WithZero (Multiplicative ℤ))) : g ∈ congSub p δ := by
  obtain ⟨a, b, c, d, hm⟩ : ∃ a b c d : F, (g : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have ha : Valued.v (a - 1) < (δ : WithZero (Multiplicative ℤ)) := by simpa [hm] using hg 0 0
  have hb : Valued.v b < (δ : WithZero (Multiplicative ℤ)) := by simpa [hm] using hg 0 1
  have hc : Valued.v c < (δ : WithZero (Multiplicative ℤ)) := by simpa [hm] using hg 1 0
  have hd : Valued.v (d - 1) < (δ : WithZero (Multiplicative ℤ)) := by simpa [hm] using hg 1 1
  have hvd : Valued.v d = 1 := v_eq_one_of_close p hδ hd
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, map_zero] at hvd
    exact zero_ne_one hvd
  have he : a * d - b * c ≠ 0 := by
    rw [← Matrix.det_fin_two_of, ← hm]
    exact (Matrix.isUnits_det_units g).ne_zero
  have hδ1 : (δ : WithZero (Multiplicative ℤ)) ≤ 1 := Units.val_le_val.mpr hδ

  have hgen : ∀ {k : G}, k ∈ genSet p δ → k ∈ congSub p δ := fun hk => Subgroup.subset_closure hk
  have hN : unipotentGL2 (b / d) ∈ congSub p δ := by
    refine hgen (Or.inl ⟨b / d, ?_, rfl⟩)
    rwa [map_div₀, hvd, div_one]
  have hZ : zG p (Units.mk0 d hd0) ∈ congSub p δ := hgen (Or.inr (Or.inr (Or.inr ⟨_, by simpa using hd, rfl⟩)))
  have hW : wG p * (unipotentGL2 (c / d) * wG p) ∈ congSub p δ := by
    refine hgen (Or.inr (Or.inl ⟨c / d, ?_, rfl⟩))
    rwa [map_div₀, hvd, div_one]
  have hD : dg p (Units.mk0 (a * d - b * c) he * ((Units.mk0 d hd0)⁻¹ * (Units.mk0 d hd0)⁻¹)) ∈ congSub p δ := by
    refine hgen (Or.inr (Or.inr (Or.inl ⟨_, ?_, rfl⟩)))

    have hsmall : Valued.v (a * d - b * c - d * d) < (δ : WithZero (Multiplicative ℤ)) := by
      have hrw : a * d - b * c - d * d = d * (a - d) - b * c := by ring
      have had : Valued.v (a - d) < (δ : WithZero (Multiplicative ℤ)) := by
        have h' : a - d = (a - 1) - (d - 1) := by ring
        rw [h']
        exact (Valued.v.map_sub _ _).trans_lt (max_lt ha hd)
      have hbc : Valued.v (b * c) < (δ : WithZero (Multiplicative ℤ)) := by
        rw [map_mul]
        calc Valued.v b * Valued.v c ≤ Valued.v b * 1 := mul_le_mul_right (hc.le.trans hδ1) _
          _ < (δ : WithZero (Multiplicative ℤ)) := by rwa [mul_one]
      rw [hrw]
      refine (Valued.v.map_sub _ _).trans_lt (max_lt ?_ hbc)
      rwa [map_mul, hvd, one_mul]
    have hcoe : (((Units.mk0 (a * d - b * c) he * ((Units.mk0 d hd0)⁻¹ * (Units.mk0 d hd0)⁻¹) : Fx)) : F) - 1 =
        (a * d - b * c - d * d) * (d⁻¹ * d⁻¹) := by
      simp only [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val]
      have hdd : d * d * (d⁻¹ * d⁻¹) = 1 := by
        rw [mul_mul_mul_comm, mul_inv_cancel₀ hd0, one_mul]
      rw [sub_mul, sub_mul, sub_mul, hdd]
    rw [hcoe, map_mul, map_mul, map_inv₀, hvd, inv_one, mul_one, mul_one]
    exact hsmall
  rw [eq_mul_of_ne_zero p g hm hd0 he]
  exact (congSub p δ).mul_mem hN ((congSub p δ).mul_mem hZ ((congSub p δ).mul_mem hD hW))

private theorem isOpen_congSub {δ : Γ} (hδ : δ ≤ 1) : IsOpen ((congSub p δ : Subgroup G) : Set G) := by
  set U : Set G := {g | ∀ i j : Fin 2,
    Valued.v ((g : Matrix (Fin 2) (Fin 2) F) i j - (1 : Matrix (Fin 2) (Fin 2) F) i j) <
      (δ : WithZero (Multiplicative ℤ))} with hUdef
  have hUopen : IsOpen U := by
    have : U = ⋂ i : Fin 2, ⋂ j : Fin 2,
        (fun g : G => (g : Matrix (Fin 2) (Fin 2) F) i j - (1 : Matrix (Fin 2) (Fin 2) F) i j) ⁻¹'
          {x : F | Valued.v x < (δ : WithZero (Multiplicative ℤ))} := by
      ext g
      simp only [hUdef, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [this]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact (isOpen_radiusBall p δ).preimage ((Units.continuous_val.matrix_elem i j).sub continuous_const)
  have h1U : (1 : G) ∈ U := by
    intro i j
    rw [Units.val_one, sub_self, map_zero]
    exact Units.zero_lt δ
  exact Subgroup.isOpen_of_mem_nhds _
    (Filter.mem_of_superset (hUopen.mem_nhds h1U) fun g hg => mem_congSub_of_close p hδ g hg)

private theorem lvl_neg_le_one (m : ℕ) : lvl (-(m : ℤ)) ≤ 1 := by
  rw [← Units.val_le_val, lvl_val, Units.val_one, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

private def fixedSub (S : Submodule ℂ (G → ℂ)) (K : Subgroup G) : Submodule ℂ (G → ℂ) where
  carrier := {V | V ∈ S ∧ ∀ k ∈ K, (fun g => V (g * k)) = V}
  add_mem' := by
    rintro V V' ⟨hV, hVK⟩ ⟨hV', hV'K⟩
    refine ⟨S.add_mem hV hV', fun k hk => ?_⟩
    funext g
    simp only [Pi.add_apply]
    rw [congrFun (hVK k hk) g, congrFun (hV'K k hk) g]
  zero_mem' := ⟨S.zero_mem, fun _ _ => rfl⟩
  smul_mem' := by
    rintro c V ⟨hV, hVK⟩
    refine ⟨S.smul_mem c hV, fun k hk => ?_⟩
    funext g
    simp only [Pi.smul_apply]
    rw [congrFun (hVK k hk) g]

private theorem mem_fixedSub (S : Submodule ℂ (G → ℂ)) (K : Subgroup G) (V : G → ℂ) :
    V ∈ fixedSub p S K ↔ V ∈ S ∧ ∀ k ∈ K, (fun g => V (g * k)) = V := Iff.rfl

private theorem fixedSub_le (S : Submodule ℂ (G → ℂ)) (K : Subgroup G) : fixedSub p S K ≤ S :=
  fun _ hV => ((mem_fixedSub p S K _).mp hV).1

private theorem rank_coinv_le_aleph0 (S : Submodule ℂ (G → ℂ))
    (hsm : ∀ W ∈ S, ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ k ∈ K, (fun g => W (g * k)) = W)
    (hadm : ∀ K : Subgroup G, IsOpen (K : Set G) → ∀ T : Submodule ℂ (G → ℂ), T ≤ S →
      (∀ W ∈ T, ∀ k ∈ K, (fun g => W (g * k)) = W) → FiniteDimensional ℂ T) :
    Module.rank ℂ (coinv p S) ≤ Cardinal.aleph0 := by

  have hfin : ∀ m : ℕ, ∃ s : Set (G → ℂ), s.Finite ∧ Submodule.span ℂ s = fixedSub p S (congSub p (lvl (-(m : ℤ)))) :=
    fun m => Submodule.fg_def.mp (Module.Finite.iff_fg.mp
      (hadm _ (isOpen_congSub p (lvl_neg_le_one m)) _ (fixedSub_le p S _)
        fun _ hV => ((mem_fixedSub p S _ _).mp hV).2))
  choose sm hsm_fin hsm_span using hfin

  have hS : S = Submodule.span ℂ (⋃ m : ℕ, sm m) := by
    apply le_antisymm
    · intro V hV
      obtain ⟨K, hK, hfix⟩ := hsm V hV
      obtain ⟨m, hm⟩ := exists_congSub_le p K hK
      have hVm : V ∈ fixedSub p S (congSub p (lvl (-(m : ℤ)))) :=
        (mem_fixedSub p S _ V).mpr ⟨hV, fun k hk => hfix k (hm hk)⟩
      rw [← hsm_span m] at hVm
      exact Submodule.span_mono (Set.subset_iUnion sm m) hVm
    · refine Submodule.span_le.mpr (Set.iUnion_subset fun m => ?_)
      have h1 : Submodule.span ℂ (sm m) ≤ S := by
        rw [hsm_span m]
        exact fixedSub_le p S _
      exact Submodule.subset_span.trans (SetLike.coe_subset_coe.mpr h1)
  have hcoinv : coinv p S = Submodule.span ℂ ((defectSpan p S).mkQ '' ⋃ m : ℕ, sm m) :=
    (congrArg (fun T : Submodule ℂ (G → ℂ) => T.map (defectSpan p S).mkQ) hS).trans (Submodule.map_span _ _)
  rw [hcoinv]
  refine (rank_span_le _).trans ?_
  haveI : Countable ((defectSpan p S).mkQ '' ⋃ m : ℕ, sm m) :=
    ((Set.countable_iUnion fun m => (hsm_fin m).countable).image _).to_subtype
  exact Cardinal.mk_le_aleph0

end countable

private theorem eq_zero_of_forall_apply_one_eq_zero (S : Submodule ℂ (G → ℂ))
    (hstab : ∀ W ∈ S, ∀ k : G, (fun g => W (g * k)) ∈ S) (h0 : ∀ U ∈ S, U 1 = 0) {W : G → ℂ}
    (hW : W ∈ S) : W = 0 := by
  funext g
  have h := h0 _ (hstab W hW g)
  simpa using h

private theorem rank_coinv_le_one (S : Submodule ℂ (G → ℂ))
    (hstab : ∀ W ∈ S, ∀ k : G, (fun g => W (g * k)) ∈ S)
    (hsm : ∀ W ∈ S, ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ k ∈ K, (fun g => W (g * k)) = W)
    (hpsi : ∀ W ∈ S, ∀ (x : F) (g : G),
      W (unipotentGL2 x * g) = NumberField.StandardAddChar.psiV p x * W g)
    (hirr : ∀ T : Submodule ℂ (G → ℂ), T ≤ S → (∀ W ∈ T, ∀ k : G, (fun g => W (g * k)) ∈ T) → T = ⊥ ∨ T = S)
    (hadm : ∀ K : Subgroup G, IsOpen (K : Set G) → ∀ T : Submodule ℂ (G → ℂ), T ≤ S →
      (∀ W ∈ T, ∀ k ∈ K, (fun g => W (g * k)) = W) → FiniteDimensional ℂ T)
    (hS : S ≠ ⊥) : Module.rank ℂ (coinv p S) ≤ 1 := by

  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : Fx, Valued.v (ϖ : F) = WithZero.exp (-1 : ℤ) := by
    obtain ⟨c, hc⟩ := exists_valuation_eq p (lvl (-1))
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at hc
      exact (lvl (-1)).ne_zero hc.symm
    exact ⟨Units.mk0 c hc0, by rw [Units.val_mk0, hc, lvl_val]⟩

  set 𝒜 : Set (Module.End ℂ (coinv p S)) :=
    {A | ∃ (δ : Γ) (n : ℤ) (τ : Ch p δ), A = Cop p S hstab hsm hpsi ϖ hϖ n τ}
  have hcomm : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A * B = B * A := by
    rintro A ⟨δ₁, a, α, rfl⟩ B ⟨δ₂, b, τ, rfl⟩
    exact Cop_mul_comm p S hstab hsm hpsi hirr hadm hS ϖ hϖ τ α a b
  have hinv : ∀ W : Submodule ℂ (coinv p S), (∀ A ∈ 𝒜, ∀ x ∈ W, A x ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    by_cases hW0 : W = ⊥
    · exact Or.inl hW0
    · refine Or.inr (eq_top_of_ne_bot p S hstab hsm hpsi hirr hadm ϖ hϖ W (fun δ n τ ξ hξ => ?_) hW0)
      exact hW _ ⟨δ, n, τ, rfl⟩ ξ hξ
  exact Module.End.rank_le_one_of_countable_of_commute_of_forall_invariant_eq_bot_or_eq_top
    (rank_coinv_le_aleph0 p S hsm hadm) 𝒜 hcomm hinv

private theorem mem_defectSpan_of_rank_le_one (S : Submodule ℂ (G → ℂ))
    (hstab : ∀ W ∈ S, ∀ k : G, (fun g => W (g * k)) ∈ S)
    (hpsi : ∀ W ∈ S, ∀ (x : F) (g : G),
      W (unipotentGL2 x * g) = NumberField.StandardAddChar.psiV p x * W g)
    (hrank : Module.rank ℂ (coinv p S) ≤ 1) {W : G → ℂ} (hW : W ∈ S) (hW1 : W 1 = 0) :
    W ∈ defectSpan p S := by
  rw [← (Submodule.Quotient.mk_eq_zero (defectSpan p S))]
  by_contra hne
  haveI : Module.Free ℂ (coinv p S) := Module.Free.of_divisionRing ℂ (coinv p S)
  obtain ⟨v₀, hv₀⟩ := rank_le_one_iff.mp hrank

  have hWmem : (defectSpan p S).mkQ W ∈ coinv p S := Submodule.mem_map_of_mem hW
  obtain ⟨r, hr⟩ := hv₀ ⟨(defectSpan p S).mkQ W, hWmem⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hne
    have := congrArg Subtype.val hr
    simpa using this.symm

  have hv₀eval : evalQ p S hpsi v₀.1 = 0 := by
    have h1 : evalQ p S hpsi (r • v₀.1) = 0 := by
      have := congrArg Subtype.val hr
      simp only [Submodule.coe_smul] at this
      rw [this]
      first | exact hW1 | simpa using hW1 | simpa +zetaDelta using hW1
    rw [map_smul, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left hr0
  have h0 : ∀ U ∈ S, U 1 = 0 := by
    intro U hU
    obtain ⟨s, hs⟩ := hv₀ ⟨(defectSpan p S).mkQ U, Submodule.mem_map_of_mem hU⟩
    have := congrArg Subtype.val hs
    simp only [Submodule.coe_smul] at this
    have h := congrArg (evalQ p S hpsi) this
    rw [map_smul, hv₀eval, smul_zero, evalQ_mkQ] at h
    exact h.symm
  apply hne
  rw [eq_zero_of_forall_apply_one_eq_zero p S hstab h0 hW, Submodule.Quotient.mk_zero]

end TwistedCoinvariantsAux
p2m_reactivate "P2MW.S_AutomorphicForm_LocalFunctionSpace_mem_span_sub_of_apply_one_eq_zero_of_irreducible_of_admissible.TwistedCoinvariantsAux"

open AutomorphicForm IsDedekindDomain TwistedCoinvariantsAux in

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
    ∀ W ∈ S, W 1 = 0 → W ∈ Submodule.span ℂ
      {V : GL (Fin 2) (p.adicCompletion ℚ) → ℂ | ∃ U ∈ S, ∃ x : p.adicCompletion ℚ,
        V = (fun g => U (g * AutomorphicForm.unipotentGL2 x)) - NumberField.StandardAddChar.psiV p x • U} := by
  intro W hW hW1
  by_cases hS : S = ⊥
  · subst hS
    rw [(Submodule.mem_bot ℂ).mp hW]
    exact Submodule.zero_mem _
  · exact mem_defectSpan_of_rank_le_one p S hstab hpsi (rank_coinv_le_one p S hstab hsm hpsi hirr hadm hS) hW hW1

end
end S_AutomorphicForm_LocalFunctionSpace_mem_span_sub_of_apply_one_eq_zero_of_irreducible_of_admissible
end P2MW
export P2MW.S_AutomorphicForm_LocalFunctionSpace_mem_span_sub_of_apply_one_eq_zero_of_irreducible_of_admissible (solution)
