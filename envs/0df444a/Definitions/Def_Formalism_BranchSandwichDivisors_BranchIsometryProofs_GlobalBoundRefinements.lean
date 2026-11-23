-- Prove2me | Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_GlobalBoundRefinements
-- name    : Formalism_BranchSandwichDivisors_BranchIsometryProofs_GlobalBoundRefinements
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:45:52.58751+00:00
-- url     : https://prove2.me/theorems/654d7cc6-c710-4c95-afd6-ade90ea39c3e
-- title:
--   Global Bound Refinements
-- statement:
--   Definitions and structural lemmas for Global Bound Refinements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/GlobalBoundRefinements.lean

import Definitions.Def_Formalism_BranchSandwichDivisors_DualLevelType
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_StepDiii
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_OrthSum
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Numeric
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Interlace
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_GoodDual
import Theorems.Thm_Formalism_BranchingDeterminantCap_heightSumBound
import Theorems.Thm_Formalism_BranchingDeterminantCap_meanShiftAssembly
import Theorems.Thm_Formalism_DivisionValues_divisor_inequality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module NumberField IsDedekindDomain
noncomputable section
namespace Formalism.BranchingDeterminantCap
theorem division_inequality : DivRecord := by
  intro J Pl _ _ TT _ muC mu0 Fo hu mlam logT hK aT phν nν fa x eps L b a rd La B0 Nc xe m f k N S
    tt η w'' b' dC lam0 C0 C Eb e6 logOm eK pq w eE δ Sg _ rk nS dg nbar HH0 muP0 muPs r g Q
    p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 hCC hb'
    hB hC hDi hL6 hE1 hE2 hx heps hLdef hbdef hadef hrd hrdL hxL hLadef hB0 hNc hxe hcJ hcPl hm hf
    hk hN hS htt hη hdC hw hpq hOm q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 hEb heK he6 heE hδ
  have hf0 : 0 ≤ f := by linarith
  have hL1 : 1 ≤ L := by rw [hLdef]; exact Real.one_le_rpow hx heps.le
  have hx0 : 0 < x := by linarith
  have hb0 : 0 < b := by rw [hbdef]; exact Real.exp_pos _
  have ha0 : 0 < a := by rw [hadef]; positivity
  have hrd0 : 0 < rd := by linarith
  have hloga : Real.log a = Real.log x + L := by
    rw [hadef, Real.log_mul hx0.ne' hb0.ne', hbdef, Real.log_exp]
  have hLa : La = Real.log x + L + Real.log rd := by
    rw [hLadef, Real.log_mul ha0.ne' hrd0.ne', hloga]
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlrd : 0 ≤ Real.log rd := Real.log_nonneg hrd
  have hLa0 : 0 ≤ La := by linarith
  obtain ⟨hpass1, hpass2⟩ := meanShiftAssembly Sg rk nS dg nbar lam0 HH0 muP0 muPs mu0 muC f r g Q
    C0 p1 p2 p3 p4 hf0 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16
  have hpos : 0 ≤ ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La := by
    have hN0 : 0 ≤ N := by linarith
    have hm0 : 0 ≤ m := by linarith
    positivity
  have heP : C * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La ≤
      C0 * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La := by
    have := mul_le_mul_of_nonneg_right hCC hpos
    linarith
  exact Formalism.DivisionValues.divisor_inequality J Pl TT muC mu0 Fo hu _ mlam logT hK aT phν nν fa x eps L b a rd La
    B0 Nc xe m f k N S tt η w'' b' dC lam0 C0 _ Eb e6 _ logOm eK pq w eE δ
    hpass1 hB hC hDi hL6 le_rfl hE1 hE2 hx heps hLdef hbdef hadef hrd hrdL hxL hLadef hB0 hNc hxe hcJ hcPl
    hm hf hk hN hS htt hη hdC hw hpq hOm q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 (by linarith) hpass2 hEb heK he6
    heP heE hδ
theorem mul_sq_le_of_const_bound {C C0 CL nV N L' La : ℝ} (hC0 : 0 ≤ C) (hnV : 0 ≤ nV) (hnVN : nV ≤ N) (hL' : L' ≤ CL * La)
    (hCL : 0 ≤ CL) (hCCL : C * CL ≤ C0) (hLa0 : 0 ≤ La) : C * (nV ^ 2 * L') ≤ C0 * (N ^ 2 * La) := by
  have hsq : nV ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hnV hnVN 2
  have hnV2 : 0 ≤ nV ^ 2 := by positivity
  have hN2 : 0 ≤ N ^ 2 := by positivity
  have h1 : nV ^ 2 * L' ≤ nV ^ 2 * (CL * La) := mul_le_mul_of_nonneg_left hL' hnV2
  have h2 : nV ^ 2 * (CL * La) ≤ N ^ 2 * (CL * La) :=
    mul_le_mul_of_nonneg_right hsq (mul_nonneg hCL hLa0)
  have h3 : C * (nV ^ 2 * L') ≤ C * (N ^ 2 * (CL * La)) :=
    mul_le_mul_of_nonneg_left (le_trans h1 h2) hC0
  have h4 : (C * CL) * (N ^ 2 * La) ≤ C0 * (N ^ 2 * La) :=
    mul_le_mul_of_nonneg_right hCCL (mul_nonneg hN2 hLa0)
  have h5 : C * (N ^ 2 * (CL * La)) = (C * CL) * (N ^ 2 * La) := by ring
  linarith
theorem kernel_bound_split {C C0 f N La m L : ℝ} (hCC : C ≤ C0) (hC00 : 0 ≤ C0) (hf0 : 0 ≤ f) (hLa0 : 0 ≤ La)
    (hm0 : 0 ≤ m) (hL0 : 0 ≤ L) :
    C * f * N ^ 2 * (La + m ^ 3 * L) ≤ C0 * (f * N ^ 2 * (La + 1) + f * m ^ 3 * N ^ 2 * L) := by
  have hp : 0 ≤ f * N ^ 2 * (La + m ^ 3 * L) := by positivity
  have h1 : C * (f * N ^ 2 * (La + m ^ 3 * L)) ≤ C0 * (f * N ^ 2 * (La + m ^ 3 * L)) :=
    mul_le_mul_of_nonneg_right hCC hp
  have h2 : 0 ≤ C0 * (f * N ^ 2) := by positivity
  have e1 : C * f * N ^ 2 * (La + m ^ 3 * L) = C * (f * N ^ 2 * (La + m ^ 3 * L)) := by ring
  have e2 : C0 * (f * N ^ 2 * (La + 1) + f * m ^ 3 * N ^ 2 * L) =
      C0 * (f * N ^ 2 * (La + m ^ 3 * L)) + C0 * (f * N ^ 2) := by ring
  linarith
theorem mul_eigen_bound {C C0 f N La m nV L' : ℝ} (hb : C * (nV ^ 2 * L') ≤ C0 * (N ^ 2 * La)) (hf0 : 0 ≤ f)
    (hm0 : 0 ≤ m) : m * (C * f * nV ^ 2 * L') ≤ C0 * m * f * N ^ 2 * La := by
  have h1 : (m * f) * (C * (nV ^ 2 * L')) ≤ (m * f) * (C0 * (N ^ 2 * La)) :=
    mul_le_mul_of_nonneg_left hb (mul_nonneg hm0 hf0)
  have e1 : m * (C * f * nV ^ 2 * L') = (m * f) * (C * (nV ^ 2 * L')) := by ring
  have e2 : C0 * m * f * N ^ 2 * La = (m * f) * (C0 * (N ^ 2 * La)) := by ring
  linarith
theorem division_inequality_full : DivRecordFull := by
  intro J Pl _ _ TT _ nr muC mu0 Fo hu logT aT ν logH x eps L b a rd La B0 Nc xe m f k N S
    tt η w'' b' lam0 C0 C nV L' CL Eb logOm pq w eE δ Sg _ rk nS dg nbar HH0 muP0 muPs r g Q
    p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 hC0 hCC hb' hnV hnVN hL' hCL hCCL
    hB hC hE1 hE2 hx heps hLdef hbdef hadef hrd hrdL hxL hLadef hB0 hNc hxe hcJ hcPl hm hf
    hk hN hS htt hη hw hpq hOm q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 hEb heE hδ
  have hL1 : 1 ≤ L := by rw [hLdef]; exact Real.one_le_rpow hx heps.le
  have hx0 : 0 < x := by linarith
  have hb0 : 0 < b := by rw [hbdef]; exact Real.exp_pos _
  have ha0 : 0 < a := by rw [hadef]; positivity
  have hrd0 : 0 < rd := by linarith
  have hloga : Real.log a = Real.log x + L := by
    rw [hadef, Real.log_mul hx0.ne' hb0.ne', hbdef, Real.log_exp]
  have hLa : La = Real.log x + L + Real.log rd := by
    rw [hLadef, Real.log_mul ha0.ne' hrd0.ne', hloga]
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlrd : 0 ≤ Real.log rd := Real.log_nonneg hrd
  have hLa0 : 0 ≤ La := by linarith
  have hf0 : 0 ≤ f := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hC00 : 0 ≤ C0 := by linarith
  have hsum : (∑ j : J, ((∑ ρ, logH j ρ) - C * f * nV ^ 2 * L')) =
      (∑ j, ∑ ρ, logH j ρ) - m * (C * f * nV ^ 2 * L') := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcJ]
  have hbound : C * (nV ^ 2 * L') ≤ C0 * (N ^ 2 * La) := mul_sq_le_of_const_bound hC0 hnV hnVN hL' hCL hCCL hLa0
  refine division_inequality J Pl TT muC mu0 Fo hu
    (∑ j, ((∑ ρ, logH j ρ) - C * f * nV ^ 2 * L')) logT
    (fun j => (∑ ρ, ((∑ i, Formalism.LatticeIndexTer.ph (ν j ρ i)) - (∑ i, ν j ρ i) * logOm)) +
      C * f * N ^ 2 * (La + m ^ 3 * L)) aT
    (fun j ρ => ∑ i, Formalism.LatticeIndexTer.ph (ν j ρ i)) (fun j ρ => ∑ i, ν j ρ i) logH
    x eps L b a rd La B0 Nc xe m f k N S tt η w'' b' 1 lam0 C0 C Eb
    (m * (C * f * nV ^ 2 * L')) logOm (fun _ => C * f * N ^ 2 * (La + m ^ 3 * L)) pq w eE δ
    Sg rk nS dg nbar HH0 muP0 muPs r g Q
    p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 hCC hb'
    hB hC (fun j => le_rfl) (by rw [hsum]) hE1 hE2 hx heps hLdef hbdef hadef hrd hrdL hxL hLadef hB0 hNc hxe
    hcJ hcPl hm hf hk hN hS htt hη le_rfl hw hpq hOm q1 (by rw [mul_one]; exact q2) q3 q4 q5 q6 q7 q8 q9 q10 hEb ?_ ?_
    heE hδ
  · intro j
    exact kernel_bound_split hCC hC00 hf0 hLa0 hm0 hL0
  · exact mul_eigen_bound hbound hf0 hm0
theorem third_descent_inequality : StepDiiiRecord := by
  intro Pl _ TT _ hP logT ev aT bT nτ lam1 D0 D1 logc logxi a La L m f k N S η b' CT Cev C
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 hC
  have key := heightSumBound Pl TT hP logT ev aT bT nτ lam1 D0 D1 logc logxi a La L m f k N S η (2 * b') CT Cev
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 (by linarith) h23 h24 h25
  have hf : 0 ≤ f := le_trans (Nat.cast_nonneg _) h23
  have hN : 0 ≤ N := by linarith
  have hm : 0 ≤ m := by linarith
  have hc : (0 : ℝ) ≤ (TT.card : ℝ) := Nat.cast_nonneg _
  have x1 : 0 ≤ (TT.card : ℝ) * b' * N := by positivity
  have x2 : 0 ≤ f * (m * η + S) * N := by positivity
  have x3 : 0 ≤ f * N ^ 2 := by positivity
  have hC0 : 0 ≤ 16 + CT + Cev := by linarith
  have step : (16 + CT + Cev) * ((TT.card : ℝ) * (2 * b') * N + f * (m * η + S) * N + f * N ^ 2) * La
      ≤ C * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La := by
    apply mul_le_mul_of_nonneg_right _ h14
    calc (16 + CT + Cev) * ((TT.card : ℝ) * (2 * b') * N + f * (m * η + S) * N + f * N ^ 2)
        ≤ (16 + CT + Cev) * (2 * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ hC0; nlinarith
      _ = (2 * (16 + CT + Cev)) * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) := by ring
      _ ≤ C * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) := by
          apply mul_le_mul_of_nonneg_right hC; linarith
  linarith
theorem ntau_two_sided_bound : NtauTwoSided := by
  intro Pl _ TT _ aT bT nτ lam1 D0 m f k N S cS η b' h1 h2 h3 h4 h5 hkN hk hN hS hcS hme hb' hc
  have A : ∀ τ ∈ TT, aT τ - (N - k) / 2 - S - m * η - bT τ ≤ nτ τ ∧ nτ τ ≤ aT τ := by
    intro τ hτ
    have a1 := h1 τ; have a2 := h2 τ hτ; have a4 := h4 τ
    simp only [hτ, if_true] at a4
    constructor <;> linarith [a4.1, a4.2]
  have B : ∀ τ, τ ∉ TT → -((N - 1) / 2 + m * η) ≤ nτ τ ∧ nτ τ ≤ cS := by
    intro τ hτ
    have a1 := h1 τ; have a3 := h3 τ hτ; have a4 := h4 τ
    simp only [hτ, if_false] at a4
    constructor <;> linarith [a4.1, a4.2, a3.1, a3.2]
  refine ⟨A, B, ?_⟩
  have e1 : ∑ t ∈ TT, aT t = ∑ τ, (if τ ∈ TT then aT τ else 0) := by
    rw [← Finset.sum_filter]; congr 1; ext τ; simp
  have e2 : (TT.card : ℝ) * (2 * b') = ∑ τ, (if τ ∈ TT then 2 * b' else 0) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]; congr 2; congr 1; ext τ; simp
  rw [e1, ← Finset.sum_sub_distrib]
  calc |∑ τ, (nτ τ - if τ ∈ TT then aT τ else 0)|
      ≤ ∑ τ, |nτ τ - if τ ∈ TT then aT τ else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ τ, ((if τ ∈ TT then 2 * b' else 0) + (cS + m * η + N / 2)) := by
        apply Finset.sum_le_sum
        intro τ _
        by_cases hτ : τ ∈ TT
        · simp only [hτ, if_true]
          rw [abs_le]; constructor <;> linarith [(A τ hτ).1, (A τ hτ).2, h5 τ hτ]
        · simp only [hτ, if_false]
          rw [abs_le]; constructor <;> linarith [(B τ hτ).1, (B τ hτ).2]
    _ = (TT.card : ℝ) * (2 * b') + (Fintype.card Pl : ℝ) * (cS + m * η + N / 2) := by
        rw [Finset.sum_add_distrib, ← e2]; simp
        ring
    _ ≤ 2 * (TT.card : ℝ) * b' + f * (cS + m * η + N / 2) := by
        have : 0 ≤ cS + m * η + N / 2 := by linarith
        nlinarith [mul_le_mul_of_nonneg_right hc this]
theorem chain_move {F : Type} [Field F] {A B : Type} [AddCommGroup A] [Module F A] [AddCommGroup B]
    [Module F B] (K : A →ₗ[F] B) (U : A →ₗ[F] A) (U' : B →ₗ[F] B) (c : F) (hc : c ≠ 0)
    (h : U'.comp K = c • K.comp U) (n : ℕ) (x : A) :
    K ((U ^ n) x) = (c⁻¹) ^ n • (U' ^ n) (K x) := by
  have h1 : ∀ x, K (U x) = c⁻¹ • U' (K x) := by
    intro x
    have := LinearMap.congr_fun h x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at this
    rw [this, smul_smul, inv_mul_cancel₀ hc, one_smul]
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, h1, map_smul, smul_smul, pow_succ U', Module.End.mul_apply,
      ← pow_succ]
theorem chain_key' {F : Type} [Field F] {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
    (K : ∀ j, V j →ₗ[F] V (j + 1)) (U : ∀ j, V j →ₗ[F] V j) (c : ℕ → F) (n M : ℕ) (hnM : n ≤ M)
    (hc : ∀ j, j < n → c j ≠ 0)
    (h : ∀ j, j < n → (U (j + 1)).comp (K j) = c j • (K j).comp (U j)) (x : V 0) :
    ∀ j, j ≤ n → chainProd K j (((U 0) ^ M) x) =
      (∏ i ∈ range j, ((c i)⁻¹) ^ (M - i)) •
        ((U j) ^ (M - j)) (chainProd (fun j => (U (j + 1)).comp (K j)) j x) := by
  intro j
  induction j with
  | zero => intro _; simp [chainProd]
  | succ j ih =>
    intro hj
    have hj' : j < n := hj
    have e : M - j = (M - (j + 1)) + 1 := by omega
    show K j (chainProd K j (((U 0) ^ M) x)) = _
    rw [ih hj'.le, map_smul, chain_move (K j) (U j) (U (j + 1)) (c j) (hc j hj') (h j hj'), smul_smul,
      prod_range_succ]
    congr 1
    rw [e, pow_succ, Module.End.mul_apply]
    rfl
theorem matrix_commute : MatrixCommute := by
  intro F _ A A' W W' _ _ _ _ _ E u u' c h
  ext1 φ
  funext α
  have h' : ∀ β (w : W), u' (E α β w) = c • E α β (u w) := by
    intro β w
    have := LinearMap.congr_fun (h α β) w
    simpa using this
  simp [matOp, h', Finset.smul_sum]
theorem chain_coupled_key {F : Type} [Field F] {AA : ℕ → Type} [∀ j, Fintype (AA j)] {W : ℕ → Type}
    [∀ j, AddCommGroup (W j)] [∀ j, Module F (W j)]
    (E : ∀ j, AA (j + 1) → AA j → (W j →ₗ[F] W (j + 1))) (u : ∀ j, W j →ₗ[F] W j) (c : ℕ → F) (n : ℕ)
    {Vc Vl : Type} [AddCommGroup Vc] [Module F Vc] [AddCommGroup Vl] [Module F Vl]
    (A : (AA n → W n) →ₗ[F] Vc) (B : Vc →ₗ[F] Vl) (Uc : Vc →ₗ[F] Vc) (Ul : Vl →ₗ[F] Vl)
    (hc : ∀ j, j < n + 2 → c j ≠ 0)
    (h : ∀ j, j < n → ∀ α β, (u (j + 1)).comp (E j α β) = c j • (E j α β).comp (u j))
    (hA : Uc.comp A = c n • A.comp ((u n).compLeft (AA n)))
    (hB : Ul.comp B = c (n + 1) • B.comp Uc) (x : AA 0 → W 0) :
    B (A (chainProd (V := fun j => AA j → W j) (fun j => matOp (E j)) n
        ((((u 0).compLeft (AA 0)) ^ (n + 2)) x))) =
      (∏ j ∈ range (n + 2), ((c j)⁻¹) ^ (n + 2 - j)) •
        Ul (B (Uc (A (chainProd (V := fun j => AA j → W j)
          (fun j => ((u (j + 1)).compLeft (AA (j + 1))).comp (matOp (E j))) n x)))) := by
  have k := chain_key' (V := fun j => AA j → W j) (fun j => matOp (E j)) (fun j => (u j).compLeft (AA j)) c n (n + 2)
    (by omega) (fun j hj => hc j (by omega))
    (fun j hj => matrix_commute F (AA j) (AA (j + 1)) (W j) (W (j + 1)) (E j) (u j) (u (j + 1)) (c j)
      (h j hj)) x n le_rfl
  have e2 : n + 2 - n = 2 := by omega
  have e1 : n + 2 - (n + 1) = 1 := by omega
  rw [k, e2, map_smul, map_smul,
    chain_move A ((u n).compLeft (AA n)) Uc (c n) (hc n (by omega)) hA 2, map_smul,
    pow_succ Uc 1, Module.End.mul_apply,
    chain_move B Uc Ul (c (n + 1)) (hc (n + 1) (by omega)) hB 1, smul_smul, smul_smul,
    prod_range_succ, prod_range_succ, e2, e1, pow_one, pow_one, mul_assoc]
theorem chain_commute_coupled : ChainCommuteCoupled := by
  intro F _ AA _ W _ _ E u c n Vc Vl _ _ _ _ A B Uc Ul hc h hA hB
  ext1 x
  exact chain_coupled_key E u c n A B Uc Ul hc h hA hB x
theorem sum_range_top_sub (m : ℕ) : ∑ j ∈ range m, (m - j) = m * (m + 1) / 2 := by
  have h1 : ∑ j ∈ range m, (m - j) = ∑ j ∈ range m, ((m - 1 - j) + 1) := by
    apply sum_congr rfl
    intro j hj
    have := mem_range.1 hj
    omega
  rw [h1, sum_range_reflect (fun j => j + 1) m]
  have h2 := sum_range_succ' (fun i => i) m
  simp only [add_zero] at h2
  rw [← h2, sum_range_id]
  simp [Nat.mul_comm]
theorem chain_scalar {R F : Type} [CommRing R] [Field F] [Algebra R F] (T : R) {VV : Type} [Fintype VV]
    (cv : ℕ → VV → F) (gam : VV → ℕ) (m : ℕ)
    (h4 : ∀ j, j < m → ∀ v, ∃ r : R, algebraMap R F r = algebraMap R F T ^ gam v * (cv j v)⁻¹) :
    ∃ r : R, algebraMap R F r = algebraMap R F T ^ ((∑ v, gam v) * (m * (m + 1) / 2)) *
      ∏ j ∈ range m, ((∏ v, cv j v)⁻¹) ^ (m - j) := by
  have B : ∀ j, j < m → ∃ r : R, algebraMap R F r =
      algebraMap R F T ^ (∑ v, gam v) * (∏ v, cv j v)⁻¹ := by
    intro j hj
    choose r hr using h4 j hj
    refine ⟨∏ v, r v, ?_⟩
    rw [map_prod, prod_congr rfl (fun v _ => hr v), prod_mul_distrib, prod_pow_eq_pow_sum, prod_inv_distrib]
  have C : ∀ n, n ≤ m → ∃ r : R, algebraMap R F r =
      algebraMap R F T ^ ((∑ v, gam v) * ∑ j ∈ range n, (m - j)) *
        ∏ j ∈ range n, ((∏ v, cv j v)⁻¹) ^ (m - j) := by
    intro n
    induction n with
    | zero => intro _; exact ⟨1, by simp⟩
    | succ n ih =>
      intro hn
      obtain ⟨r, hr⟩ := ih (Nat.le_of_succ_le hn)
      obtain ⟨s, hs⟩ := B n hn
      refine ⟨r * s ^ (m - n), ?_⟩
      rw [map_mul, map_pow, hr, hs, sum_range_succ, prod_range_succ, mul_add, pow_add, mul_pow, ← pow_mul]
      ring
  obtain ⟨r, hr⟩ := C m le_rfl
  rw [sum_range_top_sub] at hr
  exact ⟨r, hr⟩
theorem chain_denominator_coupled : ChainDenominatorCoupled := by
  intro R F _ _ _ AA _ W _ _ _ _ E u n Vc Vl _ _ _ _ _ _ _ _ A B Uc Ul S Sc Sl T VV _ cv gam e1
    hc h hA hB h1 hAc hBc h4 x hx
  have hc' : ∀ j, j < n + 2 → (∏ v, cv j v) ≠ 0 := fun j hj => prod_ne_zero_iff.2 fun v _ => hc j hj v
  rw [chain_coupled_key E u (fun j => ∏ v, cv j v) n A B Uc Ul hc' h hA hB x]
  have A1 : ∀ j, j ≤ n → T ^ (j * e1) • chainProd (V := fun j => AA j → W j)
      (fun j => ((u (j + 1)).compLeft (AA (j + 1))).comp (matOp (E j))) j x ∈ S j := by
    intro j
    induction j with
    | zero => intro _; simpa [chainProd] using hx
    | succ j ih =>
      intro hj
      have := h1 j hj _ (ih (Nat.le_of_succ_le hj))
      rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, smul_smul, ← pow_add] at this
      have e : (j + 1) * e1 = e1 + j * e1 := by ring
      rw [e]; exact this
  have a3 := hBc _ (hAc _ (A1 n le_rfl))
  simp only [LinearMap.map_smul_of_tower, smul_smul, ← pow_add] at a3
  obtain ⟨r, hr⟩ := chain_scalar T cv gam (n + 2) h4
  set z := Ul (B (Uc (A (chainProd (V := fun j => AA j → W j)
    (fun j => ((u (j + 1)).compLeft (AA (j + 1))).comp (matOp (E j))) n x)))) with hz
  have e : T ^ ((n + 2) * e1 + (∑ v, gam v) * ((n + 2) * (n + 2 + 1) / 2)) •
      ((∏ i ∈ range (n + 2), ((∏ v, cv i v)⁻¹) ^ (n + 2 - i)) • z) =
      r • (T ^ (e1 + (e1 + n * e1)) • z) := by
    rw [← algebraMap_smul F (T ^ ((n + 2) * e1 + (∑ v, gam v) * ((n + 2) * (n + 2 + 1) / 2))), ← algebraMap_smul F r,
      ← algebraMap_smul F (T ^ (e1 + (e1 + n * e1))), smul_smul, smul_smul, hr, map_pow, map_pow, pow_add]
    congr 1
    have : (n + 2) * e1 = e1 + (e1 + n * e1) := by ring
    rw [this]; ring
  rw [e]
  exact Sl.smul_mem r a3
example : (∀ j, j < 3 → (fun _ : ℕ => (2 : ℚ)) j ≠ 0) ∧
    (∀ j, j < 3 → ((fun j : ℕ => ((2 : ℚ) ^ j) • (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) (j + 1)).comp
        ((fun _ : ℕ => (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) j) =
      (fun _ : ℕ => (2 : ℚ)) j • ((fun _ : ℕ => (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) j).comp
        ((fun j : ℕ => ((2 : ℚ) ^ j) • (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) j)) := by
  refine ⟨fun j _ => by norm_num, fun j _ => ?_⟩
  ext
  simp [pow_succ, mul_comm]
example : (∏ j ∈ range 3, (((2 : ℚ))⁻¹) ^ (3 - j)) * ((2 : ℚ) ^ 3 * (2 ^ 2 * 2 ^ 1)) = 1 := by
  norm_num [prod_range_succ]
example :
    (∀ j, j < 1 → ∀ v : Unit, (fun (_ : ℕ) (_ : Unit) => (2 : ℚ)) j v ≠ 0) ∧
    (∀ j, j < 1 → ((fun j : ℕ => ((2 : ℚ) ^ j / 2) • (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) (j + 1)).comp
        (LinearMap.id : ℚ →ₗ[ℚ] ℚ) =
      (∏ v : Unit, (fun (_ : ℕ) (_ : Unit) => (2 : ℚ)) j v) • (LinearMap.id : ℚ →ₗ[ℚ] ℚ).comp
        ((fun j : ℕ => ((2 : ℚ) ^ j / 2) • (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) j)) ∧
    (∀ j, j < 1 → ∀ x ∈ Submodule.span ℤ {(1 : ℚ)}, (2 : ℤ) ^ 0 •
      ((fun j : ℕ => ((2 : ℚ) ^ j / 2) • (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) (j + 1))
        ((LinearMap.id : ℚ →ₗ[ℚ] ℚ) x) ∈ Submodule.span ℤ {(1 : ℚ)}) ∧
    (∀ j, j < 1 → ∀ _v : Unit, ∃ r : ℤ, algebraMap ℤ ℚ r = algebraMap ℤ ℚ 2 ^ 1 * ((2 : ℚ))⁻¹) ∧
    ((1 : ℚ) / 2) ∉ Submodule.span ℤ {(1 : ℚ)} := by
  refine ⟨fun j _ _ => by norm_num, ?_, ?_, fun j _ _ => ⟨1, by norm_num⟩, ?_⟩
  · intro j hj
    obtain rfl : j = 0 := by omega
    ext
    simp
  · intro j hj x hx
    obtain rfl : j = 0 := by omega
    simpa using hx
  · intro h
    obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.1 h
    have h2 : (2 * z : ℚ) = 1 := by
      have : (z : ℚ) = 1 / 2 := by simpa using hz
      rw [this]; norm_num
    have h3 : (2 * z : ℤ) = 1 := by exact_mod_cast h2
    omega
example : Interlace ![5, 2, 0] ![3, 1] ∧ d0 ![5, 2, 0] ![3, 1] = 2 ∧
    (![5, 2, 0] : Fin 3 → ℤ) 1 + d0 ![5, 2, 0] ![3, 1] ≤ (![5, 2, 0] : Fin 3 → ℤ) 0 ∧
    cCap ![5, 2, 0] ![3, 1] = cCap ![9, 2, 0] ![3, 1] ∧
    cCap ![3, 2, 0] ![3, 1] ≠ cCap ![5, 2, 0] ![3, 1] := by
  refine ⟨by unfold Interlace; decide, by decide, by decide, by decide, by decide⟩
theorem mem_typeSpace {K V Γ : Type} [Field K] [AddCommGroup V] [Module K V] [Group Γ]
    (ρ : Γ →* Module.End K V) (chi : Γ → K) (v : V) :
    v ∈ typeSpace ρ chi ↔ ∀ γ, ρ γ v = chi γ • v := by
  simp [typeSpace, Submodule.mem_iInf]
theorem level_inclusion_type : LevelInclType := by
  intro O K V0 EE _ _ _ _ _ _ _ _ _ _ _ Γ _ _ ρ0 ρ1 chi io hio A hA
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ⟨haA, hat⟩, rfl⟩
    refine ⟨⟨a, haA, rfl⟩, ?_⟩
    have hat' := (mem_typeSpace _ _ _).1 hat
    refine (mem_typeSpace _ _ _).2 fun γ => ?_
    change ρ1 γ (io a) = _ • io a
    rw [← hio, hat' γ, map_smul]
  · rintro _ ⟨⟨a, haA, rfl⟩, hxt⟩
    have hx : ∀ γ, ρ1 γ (io a) = algebraMap O K (chi γ) • io a := (mem_typeSpace _ _ _).1 hxt
    refine ⟨∑ γ, ((chi γ⁻¹ : Oˣ) : O) • ρ0 γ a, ⟨?_, ?_⟩, ?_⟩
    · exact Submodule.sum_mem _ fun γ _ => Submodule.smul_mem _ _ (hA γ a haA)
    · refine (mem_typeSpace _ _ _).2 fun δ => ?_
      rw [map_sum, Finset.smul_sum]
      refine Fintype.sum_equiv (Equiv.mulLeft δ) _ _ fun γ => ?_
      rw [LinearMap.map_smul_of_tower, Equiv.coe_mulLeft, map_mul ρ0, Module.End.mul_apply,
        algebraMap_smul, smul_smul, ← Units.val_mul]
      have hχ : chi δ * chi (δ * γ)⁻¹ = chi γ⁻¹ := by
        rw [mul_inv_rev, map_mul, mul_comm (chi γ⁻¹), ← mul_assoc, ← map_mul, mul_inv_cancel,
          map_one, one_mul]
      rw [hχ]
    · change io (∑ γ, ((chi γ⁻¹ : Oˣ) : O) • ρ0 γ a) = ((Fintype.card Γ : ℕ) : O) • io a
      rw [map_sum]
      have : ∀ γ, io (((chi γ⁻¹ : Oˣ) : O) • ρ0 γ a) = io a := by
        intro γ
        rw [LinearMap.map_smul_of_tower, hio, hx γ, algebraMap_smul, smul_smul, ← Units.val_mul,
          ← map_mul]
        simp
      rw [Finset.sum_congr rfl fun γ _ => this γ]
      simp [Nat.cast_smul_eq_nsmul]
theorem local_global_inclusion : LocalGlobalIncl := by
  intro O V _ _ _ M N h x hx
  by_contra hxN
  have hI : N.comap (LinearMap.toSpanSingleton O V x) ≠ ⊤ := by
    intro hT
    apply hxN
    have : (1 : O) ∈ N.comap (LinearMap.toSpanSingleton O V x) := hT ▸ Submodule.mem_top
    simpa using this
  obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal (N.comap (LinearMap.toSpanSingleton O V x)) hI
  obtain ⟨s, hs, hsx⟩ := h p hp x hx
  exact hs (hIp (by simpa using hsx))
theorem level_inclusion_local : LevelInclLocal := by
  intro O K V0 EE _ _ _ _ _ _ _ _ _ _ _ Γ _ _ ρ0 ρ1 chi R R' H
  have one : ∀ p : Ideal O, p.IsMaximal → (1 : O) ∉ p := fun p hp => (Ideal.ne_top_iff_one p).1 hp.ne_top
  constructor
  · apply local_global_inclusion O EE R' R
    intro p hp x hx
    obtain ⟨io, A, hio, hA, hR, hR'⟩ := H p hp
    exact (hR x).2 ((level_inclusion_type O K V0 EE Γ ρ0 ρ1 chi io hio A hA).1
      ((hR' x).1 ⟨1, one p hp, by simpa using hx⟩))
  · intro x hx
    have key : R.map (LinearMap.lsmul O EE ((Fintype.card Γ : ℕ) : O)) ≤ R' := by
      apply local_global_inclusion O EE
      intro p hp y hy
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨io, A, hio, hA, hR, hR'⟩ := H p hp
      exact (hR' _).2 ((level_inclusion_type O K V0 EE Γ ρ0 ρ1 chi io hio A hA).2 x
        ((hR x).1 ⟨1, one p hp, by simpa using hx⟩))
    exact key ⟨x, hx, rfl⟩
def twistRep {K V Γ : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Group Γ]
    (ρ : Γ →* Module.End K V) (chi : Γ →* (𝓞 K)ˣ) : Γ →* Module.End K V where
  toFun γ := algebraMap (𝓞 K) K (chi γ⁻¹) • ρ γ
  map_one' := by simp
  map_mul' γ δ := by
    rw [smul_mul_smul_comm, ← map_mul, ← map_mul, ← Units.val_mul, ← map_mul, mul_inv_rev,
      map_mul chi δ⁻¹, map_mul chi γ⁻¹, mul_comm]
namespace VacLev
def io : ℚ × ℚ →ₗ[ℚ] ℚ := LinearMap.coprod LinearMap.id LinearMap.id
def e0 : ℚ × ℚ →ₗ[ℚ] ℚ × ℚ := ((1 / 2 : ℚ) • io).prod ((1 / 2 : ℚ) • io)
def A : Submodule ℤ (ℚ × ℚ) := Submodule.prod 1 1
end VacLev
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in

example : True := by
  have e2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have e3 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have := division_inequality_full (Fin 1) (Fin 1) univ 1
    (3 + Real.exp 1) (1 + Real.exp 1) 0 _ 0 (fun _ => 0) (fun _ _ _ => 4) (fun _ _ => Formalism.LatticeIndexTer.ph 4)
    1 (1 / 52) 1 (Real.exp 1) (Real.exp 1) 1 1 (Real.exp 1) 0 1 1 1 1 1 0 0 0 0 1 1 18 1 1 1 1
    (Real.exp 1) 1 (fun _ => 1) (fun _ _ => 1) (fun _ _ => 2) (fun _ _ => 3)
    (Fin 1) (fun _ => 1) (fun _ => 1) (fun _ => -3 - Real.exp 1) 1 0 (-(1 + Real.exp 1))
    (-(3 + Real.exp 1) + 1) 0 1 10
    (by norm_num) (by norm_num) (by intro; norm_num) (by simp) le_rfl (by norm_num) (by intro; norm_num)
    (by norm_num) (by norm_num) (by intro; norm_num; linarith) (by simp; linarith) (by simp; linarith)
    (by first | (norm_num; done) | (norm_num; linarith)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num)
    (by simp) rfl
    (fun _ ρ => by simp [Formalism.LatticeIndexTer.ph]) (fun _ ρ => by simp; norm_num)
    le_rfl (by norm_num) (by simp) rfl (by ring) le_rfl (by simp) (by simp) (by simp)
    (by simp) le_rfl (by simp) (by simp) (by simp) le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
    (fun _ _ => ⟨by norm_num, by linarith⟩) (fun _ => by simp) (by simp)
    (by linarith) (by first | (norm_num; done) | (norm_num; linarith)) (by first | (norm_num; done) | (norm_num; linarith)) (by first | (norm_num; done) | (norm_num; linarith))
    (by first | (norm_num; done) | (norm_num; linarith)) (by norm_num) (by norm_num) (by first | (norm_num; done) | (norm_num; linarith)) (by first | (norm_num; done) | (norm_num; linarith))
    (by first | (norm_num; done) | (norm_num; linarith)) (by first | (norm_num; done) | (norm_num; linarith))
    (fun _ _ => by norm_num) (fun _ ρ => by fin_cases ρ <;> simp <;> norm_num)
  trivial
namespace PlaceVacuity
example : True := by
  have hl : Real.log (2 * (Real.exp 1 / 2)) = 1 := by
    rw [mul_div_cancel₀ _ (two_ne_zero)]; exact Real.log_exp 1
  have := third_descent_inequality (Fin 1) univ 7299 1 0 (fun _ => 1000) (fun _ => 150) (fun _ => 846) (fun _ => 996)
    (fun _ => 150) (fun _ => 450) (fun _ => 4050) (fun _ => 45) (Real.exp 1 / 2) 1 1 1 1 2 10 0 0 100 1 0 34
    (by simp; norm_num) (by intro _; rw [hl]; norm_num) (by intro _; rw [hl]; norm_num) (by intro _; norm_num)
    (by intro _ _; norm_num) (by intro τ h; exact absurd (Finset.mem_univ τ) h) (by intro τ; rw [if_pos (Finset.mem_univ τ)]; norm_num) (by intro _; norm_num)
    (by intro _ _; norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [hl]; norm_num) (by rw [hl]; norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by simp) (by norm_num) (by norm_num) (by norm_num)
  trivial
example : True := by
  have h := ntau_two_sided_bound (Fin 2) {0} (fun _ => 100) (fun _ => 7)
    (fun τ => if τ = 0 then 100 - 3 - 12 else 2 - 9 / 2 - 5) (fun τ => if τ = 0 then 100 - 3 else 2 - 9 / 2)
    (fun τ => if τ = 0 then 12 else 5) 2 2 4 10 2 6 (3 / 2) 4
    (by intro τ; fin_cases τ <;> simp)
    (by intro τ hτ; simp at hτ; subst hτ; norm_num)
    (by intro τ hτ; simp at hτ; simp [hτ]; norm_num)
    (by intro τ; fin_cases τ <;> simp <;> norm_num)
    (by intro τ _; norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by simp)
  trivial
def swapL : ℚ × ℚ →ₗ[ℚ] ℚ × ℚ := (LinearEquiv.prodComm ℚ ℚ ℚ).toLinearMap
def Pc : Submodule ℚ (Fin 2 → ℚ × ℚ) :=
  LinearMap.eqLocus (LinearMap.proj 1) (swapL.comp (LinearMap.proj 0))
theorem mem_Pc (φ : Fin 2 → ℚ × ℚ) : φ ∈ Pc ↔ φ 1 = (φ 0).swap := Iff.rfl
def Uc : Pc →ₗ[ℚ] Pc := (swapL.compLeft (Fin 2)).restrict (by
  intro φ hφ
  rw [mem_Pc] at hφ ⊢
  show (φ 1).swap = ((φ 0).swap).swap
  rw [hφ])
def Ac : (Unit → ℚ) →ₗ[ℚ] Pc :=
  LinearMap.codRestrict Pc (LinearMap.pi fun _ => (LinearMap.id.prod LinearMap.id).comp (LinearMap.proj ())) (by
    intro φ; rw [mem_Pc]; rfl)
def Bc : Pc →ₗ[ℚ] ℚ :=
  ((LinearMap.fst ℚ ℚ ℚ).comp (LinearMap.proj (R := ℚ) (φ := fun _ : Fin 2 => ℚ × ℚ) 0) +
    (LinearMap.fst ℚ ℚ ℚ).comp (LinearMap.proj (R := ℚ) (φ := fun _ : Fin 2 => ℚ × ℚ) 1)).comp Pc.subtype
example : (Bc.comp (Ac.comp LinearMap.id)).comp ((((2 : ℚ) • LinearMap.id : ℚ →ₗ[ℚ] ℚ).compLeft Unit) ^ 2) =
    (∏ j ∈ range 2, (((fun j : ℕ => if j = 0 then (1 / 2 : ℚ) else 3) j)⁻¹) ^ (2 - j)) •
      ((((3 : ℚ) • LinearMap.id : ℚ →ₗ[ℚ] ℚ)).comp Bc).comp ((Uc.comp Ac).comp LinearMap.id) := by
  have := chain_commute_coupled ℚ (fun _ => Unit) (fun _ => ℚ) (fun _ _ _ => LinearMap.id)
    (fun _ => (2 : ℚ) • LinearMap.id) (fun j => if j = 0 then (1 / 2 : ℚ) else 3) 0 Pc ℚ Ac Bc Uc ((3 : ℚ) • LinearMap.id)
    (by intro j _; by_cases h : j = 0 <;> simp [h])
    (by intro j hj; omega)
    (by
      ext φ i <;> fin_cases i <;> simp [Uc, Ac, swapL, LinearMap.restrict_apply])
    (by
      ext ⟨φ, hφ⟩
      rw [mem_Pc] at hφ
      simp [Uc, Bc, swapL, LinearMap.restrict_apply, hφ]
      ring)
  exact this
example : ¬ ∃ (c : ℚ) (Ul : ℚ →ₗ[ℚ] ℚ), c ≠ 0 ∧
    Ul.comp (LinearMap.fst ℚ ℚ ℚ) = c • (LinearMap.fst ℚ ℚ ℚ).comp swapL := by
  rintro ⟨c, Ul, hc, h⟩
  have := LinearMap.congr_fun h (0, 1)
  simp [swapL] at this
  exact hc this.symm
example : (2 : ℤ) ^ ((1 + 2) * 0 + (∑ _v : Unit, 1) * ((1 + 2) * (1 + 2 + 1) / 2)) •
    ((LinearMap.proj () : (Unit → ℚ) →ₗ[ℚ] ℚ) (chainProd (V := fun _ => Unit → ℚ)
      (fun _ => matOp (fun _ _ => (LinearMap.id : ℚ →ₗ[ℚ] ℚ))) 1
      (((((2 : ℚ) ^ 0 / 2) • (LinearMap.id : ℚ →ₗ[ℚ] ℚ)).compLeft Unit ^ (1 + 2)) (fun _ => 1)))) ∈
      Submodule.span ℤ {(1 : ℚ)} := by
  have := chain_denominator_coupled ℤ ℚ (fun _ => Unit) (fun _ => ℚ) (fun _ _ _ => LinearMap.id)
    (fun j : ℕ => ((2 : ℚ) ^ j / 2) • (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) 1 ℚ ℚ (LinearMap.proj ()) LinearMap.id
    ((2 : ℚ) • LinearMap.id) ((4 : ℚ) • LinearMap.id)
    (fun _ => Submodule.pi Set.univ fun _ => Submodule.span ℤ {(1 : ℚ)}) (Submodule.span ℤ {(1 : ℚ)})
    (Submodule.span ℤ {(1 : ℚ)}) 2 Unit (fun _ _ => 2) (fun _ => 1) 0
    (fun _ _ _ => by norm_num)
    (by intro j hj α β; obtain rfl : j = 0 := by omega
        ext; simp)
    (by ext; simp)
    (by ext; simp; norm_num)
    (by intro j hj x hx; obtain rfl : j = 0 := by omega
        intro i _
        simpa [matOp] using hx () trivial)
    (by intro x hx
        have := (Submodule.span ℤ {(1 : ℚ)}).smul_mem (2 : ℤ) (hx () trivial)
        simpa using this)
    (by intro x hx
        have := (Submodule.span ℤ {(1 : ℚ)}).smul_mem (4 : ℤ) hx
        simpa using this)
    (fun _ _ _ => ⟨1, by norm_num⟩)
    (fun _ => 1) (by intro i _; exact Submodule.subset_span rfl)
  exact this
example (O K EE : Type) [CommRing O] [Field K] [Algebra O K] [AddCommGroup EE] [Module K EE] [Module O EE]
    [IsScalarTower O K EE] (R : Submodule O EE) : True := by
  have := level_inclusion_local O K EE EE Unit 1 1 1 R R (by
    intro p hp
    have := hp.isPrime
    refine ⟨LinearMap.id, Formalism.HermitianLatticesTheory.localization₂ p R, fun _ _ => rfl, fun _ a ha => ha, ?_, ?_⟩
    · intro x
      have ht : x ∈ (typeSpace (1 : Unit →* Module.End K EE) fun γ => algebraMap O K ((1 : Unit →* Oˣ) γ)) := by
        rw [mem_typeSpace]; intro γ; simp
      constructor
      · rintro ⟨s, hs, hx⟩
        exact ⟨⟨x, ⟨s, hs, hx⟩, rfl⟩, ht⟩
      · rintro ⟨⟨y, ⟨s, hs, hy⟩, rfl⟩, _⟩
        exact ⟨s, hs, hy⟩
    · intro x
      have ht : x ∈ (typeSpace (1 : Unit →* Module.End K EE) fun γ => algebraMap O K ((1 : Unit →* Oˣ) γ)) := by
        rw [mem_typeSpace]; intro γ; simp
      constructor
      · rintro ⟨s, hs, hx⟩
        exact ⟨x, ⟨⟨s, hs, hx⟩, ht⟩, rfl⟩
      · rintro ⟨y, ⟨⟨s, hs, hy⟩, _⟩, rfl⟩
        exact ⟨s, hs, hy⟩)
  trivial
example (O K V0 EE : Type) [CommRing O] [Field K] [Algebra O K] [AddCommGroup V0] [Module K V0] [Module O V0]
    [IsScalarTower O K V0] [AddCommGroup EE] [Module K EE] [Module O EE] [IsScalarTower O K EE]
    (hinj : Function.Injective (algebraMap O K))
    (Γ : Type) [Group Γ] [Fintype Γ] (ρ0 : Γ →* Module.End K V0) (ρ1 : Γ →* Module.End K EE)
    (chi : Γ →* Oˣ) (io : V0 →ₗ[K] EE) (hio : ∀ γ x, io (ρ0 γ x) = ρ1 γ (io x))
    (A0 : Submodule O V0) (hA : ∀ γ, ∀ a ∈ A0, ρ0 γ a ∈ A0) :
    ∀ p : Ideal O, p.IsMaximal → ∃ (io' : V0 →ₗ[K] EE) (A : Submodule O V0),
      (∀ γ x, io' (ρ0 γ x) = ρ1 γ (io' x)) ∧ (∀ γ, ∀ a ∈ A, ρ0 γ a ∈ A) ∧
      (∀ x, (∃ s : O, s ∉ p ∧ s • x ∈ (A0.map (io.restrictScalars O) ⊓
          (typeSpace ρ1 fun γ => algebraMap O K (chi γ)).restrictScalars O)) ↔
        x ∈ A.map (io'.restrictScalars O) ⊓ (typeSpace ρ1 fun γ => algebraMap O K (chi γ)).restrictScalars O) ∧
      (∀ x, (∃ s : O, s ∉ p ∧ s • x ∈ ((A0 ⊓ (typeSpace ρ0 fun γ => algebraMap O K (chi γ)).restrictScalars O).map
          (io.restrictScalars O))) ↔
        x ∈ (A ⊓ (typeSpace ρ0 fun γ => algebraMap O K (chi γ)).restrictScalars O).map (io'.restrictScalars O)) := by
  intro p hp
  have := hp.isPrime
  have hne : ∀ s : O, s ∉ p → algebraMap O K s ≠ 0 := by
    intro s hs h
    apply hs
    have : s = 0 := hinj (by rw [h, map_zero])
    rw [this]; exact p.zero_mem
  refine ⟨io, Formalism.HermitianLatticesTheory.localization₂ p A0, hio, ?_, ?_, ?_⟩
  · rintro γ a ⟨s, hs, ha⟩
    refine ⟨s, hs, ?_⟩
    have h1 : s • ρ0 γ a = ρ0 γ (s • a) := by
      rw [← algebraMap_smul K s a, map_smul, algebraMap_smul]
    rw [h1]; exact hA γ _ ha
  · intro x
    constructor
    · rintro ⟨s, hs, ⟨a, ha, hax⟩, ht⟩
      have hs0 := hne s hs
      have hx : (algebraMap O K s)⁻¹ • (s • x) = x := by
        rw [← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ hs0, one_smul]
      refine ⟨⟨(algebraMap O K s)⁻¹ • a, ⟨s, hs, ?_⟩, ?_⟩, ?_⟩
      · rw [← algebraMap_smul K s, smul_smul, mul_inv_cancel₀ hs0, one_smul]; exact ha
      · show io _ = x
        rw [map_smul, ← hx]; exact congrArg _ hax
      · rw [← hx]; exact (typeSpace ρ1 _).smul_mem _ ht
    · rintro ⟨⟨y, ⟨s, hs, hy⟩, rfl⟩, ht⟩
      exact ⟨s, hs, ⟨s • y, hy, by simp⟩, Submodule.smul_mem _ s ht⟩
  · intro x
    constructor
    · rintro ⟨s, hs, a, ⟨ha, hta⟩, hax⟩
      have hs0 := hne s hs
      have hx : (algebraMap O K s)⁻¹ • (s • x) = x := by
        rw [← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ hs0, one_smul]
      refine ⟨(algebraMap O K s)⁻¹ • a, ⟨⟨s, hs, ?_⟩, (typeSpace ρ0 _).smul_mem _ hta⟩, ?_⟩
      · rw [← algebraMap_smul K s, smul_smul, mul_inv_cancel₀ hs0, one_smul]; exact ha
      · show io _ = x
        rw [map_smul, ← hx]; exact congrArg _ hax
    · rintro ⟨y, ⟨⟨s, hs, hy⟩, hty⟩, rfl⟩
      exact ⟨s, hs, s • y, ⟨hy, Submodule.smul_mem _ s hty⟩, by simp⟩
end PlaceVacuity
end Formalism.BranchingDeterminantCap


