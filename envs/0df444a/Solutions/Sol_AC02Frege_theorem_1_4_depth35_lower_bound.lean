-- Prove2me | solution 1 for AC02Frege.theorem_1_4_depth35_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-18T05:42:40.278204+00:00
-- url     : https://prove2.me/submissions/1bc3d612-60e5-4e39-a783-00341d0244f6

import Definitions.Def_AC02Frege_lift
import Definitions.Def_AC02Frege_PC
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib
import Definitions.Def_AC02Frege_D35Refutation
import Theorems.Thm_AC02Frege_corollary_5_3_rank_criterion
import Definitions.Def_AC02Frege_rankCounts
import Theorems.Thm_AC02Frege_lemma_4_19_two_counts
import Theorems.Thm_AC02Frege_lemma_C_1_cumulative_counts
import Definitions.Def_SemAC02_multiplierSpace
import Definitions.Def_AC02Frege_ML
import Definitions.Def_SemAC02_Ble

open _root_.SemAC02
open _root_.AC02Frege _root_.LiftSAParity
namespace P2MSyntacticRootProof
section
-- Inlined Solutions.P2MMajorityLiftCounts

set_option maxHeartbeats 2000000

namespace AC02Frege.P2MMajorityLiftCounts

open LiftSAParity

theorem clause_card {n ℓ : ℕ} (J : Clause (Fin n)) (C : Clause (Fin n × Fin ℓ))
    (hC : C ∈ liftClause ℓ J) : C.card ≤ J.card*(ℓ/2+1) := by
  classical
  obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hC
  calc
    _ ≤ ∑ l ∈ J.attach, ((A l.1 l.2).image (fun a => ((l.1.1,a),l.1.2))).card := Finset.card_biUnion_le
    _ ≤ ∑ _l ∈ J.attach, (ℓ/2+1) := by
      apply Finset.sum_le_sum
      intro l hl
      have hc : (A l.1 l.2).card = ℓ/2+1 :=
        (Finset.mem_powersetCard.mp (Finset.mem_pi.mp hA l.1 l.2)).2
      exact Finset.card_image_le.trans_eq hc
    _ = _ := by simp

theorem width_le {n ℓ w : ℕ} (F : CNF (Fin n)) (hw : ∀ J ∈ F, J.card ≤ w) :
    width (lift F ℓ) ≤ w*(ℓ/2+1) := by
  apply Finset.sup_le
  intro C hC
  obtain ⟨J,hJ,hCJ⟩ := Finset.mem_biUnion.mp hC
  exact (clause_card J C hCJ).trans (Nat.mul_le_mul_right _ (hw J hJ))

theorem odd_width_le {n ℓ w : ℕ} (F : CNF (Fin n)) (hℓ : Odd ℓ)
    (hw : ∀ J ∈ F, J.card ≤ w) : 2*width (lift F ℓ) ≤ w*(ℓ+1) := by
  have h := width_le F hw (ℓ := ℓ)
  obtain ⟨k,hk⟩ := hℓ
  have he : 2*(ℓ/2+1) = ℓ+1 := by omega
  nlinarith

theorem clause_family_card {n : ℕ} (ℓ : ℕ) (J : Clause (Fin n)) :
    (liftClause ℓ J).card ≤ (2^ℓ)^J.card := by
  classical
  apply Finset.card_image_le.trans
  rw [Finset.card_pi]
  calc
    _ ≤ ∏ _l ∈ J, 2^ℓ := by
      apply Finset.prod_le_prod
      · intro l hl
        exact Nat.zero_le _
      · intro l hl
        simp only [Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]
        exact Nat.choose_le_two_pow _ _
    _ = _ := by simp

theorem lift_card {n ℓ w : ℕ} (F : CNF (Fin n)) (hw : ∀ J ∈ F, J.card ≤ w) :
    (lift F ℓ).card ≤ F.card*(2^ℓ)^w := by
  calc
    _ ≤ ∑ J ∈ F, (liftClause ℓ J).card := Finset.card_biUnion_le
    _ ≤ ∑ _J ∈ F, (2^ℓ)^w := by
      apply Finset.sum_le_sum
      intro J hJ
      exact (clause_family_card ℓ J).trans (Nat.pow_le_pow_right (by positivity) (hw J hJ))
    _ = _ := by simp

theorem encoding_length_le {n ℓ w : ℕ} (F : CNF (Fin n)) (hw : ∀ J ∈ F, J.card ≤ w) :
    encLength (lift F ℓ) ≤ F.card*(2^ℓ)^w*(w*(ℓ/2+1)+1) := by
  have hwidth := width_le F hw (ℓ := ℓ)
  have he : encLength (lift F ℓ) ≤ (lift F ℓ).card*(w*(ℓ/2+1)+1) := by
    calc
      _ ≤ ∑ _C ∈ lift F ℓ, (w*(ℓ/2+1)+1) := by
        apply Finset.sum_le_sum
        intro C hC
        exact Nat.add_le_add_right ((Finset.le_sup (f := Finset.card) hC).trans hwidth) _
      _ = _ := by simp
  exact he.trans (Nat.mul_le_mul_right _ (lift_card F hw))

end AC02Frege.P2MMajorityLiftCounts
end

section
-- Inlined Solutions.P2MFiniteCNFCounts

namespace P2MProofComplexity.P2MFiniteCNFCounts

open LiftSAParity

theorem width_card {n w : ℕ} (hn : 1 ≤ n) (F : CNF (Fin n))
    (hw : ∀ C ∈ F, C.card ≤ w) : F.card ≤ (w+1)*(2*n)^w := by
  classical
  let B : Finset (Clause (Fin n)) :=
    (Finset.range (w+1)).biUnion (fun j => (Finset.univ : Finset (Fin n × Bool)).powersetCard j)
  have hF : F ⊆ B := by
    intro C hC
    refine Finset.mem_biUnion.mpr ⟨C.card,Finset.mem_range.mpr (by have h := hw C hC; omega),?_⟩
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,rfl⟩
  calc
    _ ≤ B.card := Finset.card_le_card hF
    _ ≤ ∑ j ∈ Finset.range (w+1), ((Finset.univ : Finset (Fin n × Bool)).powersetCard j).card := Finset.card_biUnion_le
    _ = ∑ j ∈ Finset.range (w+1), (2*n).choose j := by simp [Nat.mul_comm]
    _ ≤ ∑ _j ∈ Finset.range (w+1), (2*n)^w := by
      apply Finset.sum_le_sum
      intro j hj
      exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_right (by omega)
        (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
    _ = _ := by simp

theorem card_le_encoding {V : Type} (F : CNF V) : F.card ≤ AC02Frege.encLength F := by
  calc
    _ = ∑ _C ∈ F, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun C hC => by omega)

end P2MProofComplexity.P2MFiniteCNFCounts
end

section
-- Inlined Solutions.P2MLogGrowth

open Filter Topology

namespace P2MProofComplexity.P2MLogGrowth

theorem eventually_log_large (b : ℝ) : ∀ᶠ n : ℕ in atTop, b ≤ Real.log (n : ℝ) :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop b

theorem eventually_log_power_le (A : ℝ) (k : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, A*(Real.log (n : ℝ))^k ≤ (n : ℝ)^C := by
  have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hC).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hb := (h.const_mul_left A).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb] with n hn
  have he : |A*(Real.log (n : ℝ))^k| ≤ (n : ℝ)^C := by
    simpa only [Function.comp_apply,Real.rpow_natCast,Real.norm_eq_abs,one_mul,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) C)] using hn
  exact (le_abs_self _).trans he

theorem eventually_scaled_power_le (A p q : ℝ) (hpq : p < q) :
    ∀ᶠ n : ℕ in atTop, A*(n : ℝ)^p ≤ (n : ℝ)^q := by
  have hlarge := ((tendsto_rpow_atTop (by linarith : 0 < q-p)).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).eventually_ge_atTop A
  filter_upwards [hlarge,eventually_ge_atTop 1] with n hn hn1
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  calc
    _ ≤ (n : ℝ)^(q-p)*(n : ℝ)^p := mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hnp.le _)
    _ = (n : ℝ)^((q-p)+p) := (Real.rpow_add hnp _ _).symm
    _ = _ := by congr 1; ring

end P2MProofComplexity.P2MLogGrowth
end

section
-- Inlined Solutions.P2MMajorityLiftSize

set_option maxHeartbeats 2000000

namespace AC02Frege.P2MMajorityLiftSize

open LiftSAParity Filter P2MProofComplexity

theorem exponential_factor {n ℓ w a : ℕ} (hn : 1 ≤ n) (lam : ℝ)
    (hℓ : (ℓ : ℝ) ≤ lam*Real.log n) (ha : lam*w*Real.log 2 ≤ (a : ℝ)) :
    (2^ℓ)^w ≤ n^a := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hexp : (ℓ : ℝ)*w*Real.log 2 ≤ Real.log n*(a : ℝ) := by
    calc
      _ = (ℓ : ℝ)*((w : ℝ)*Real.log 2) := by ring
      _ ≤ (lam*Real.log n)*((w : ℝ)*Real.log 2) :=
        mul_le_mul_of_nonneg_right hℓ (mul_nonneg (Nat.cast_nonneg _) hlog2)
      _ = Real.log n*(lam*w*Real.log 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ha hlog
  have heq2 : (((2^ℓ)^w : ℕ) : ℝ) = Real.exp ((ℓ : ℝ)*w*Real.log 2) := by
    norm_num only [Nat.cast_pow,Nat.cast_ofNat]
    rw [← pow_mul,← Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : 0 < (2 : ℝ))]
    congr 1
    push_cast
    ring
  have heqn : (n : ℝ)^a = Real.exp (Real.log n*(a : ℝ)) := by
    rw [← Real.rpow_natCast,Real.rpow_def_of_pos hnp]
  have hr : (((2^ℓ)^w : ℕ) : ℝ) ≤ ((n^a : ℕ) : ℝ) := by
    calc
      _ = _ := heq2
      _ ≤ _ := Real.exp_le_exp.mpr hexp
      _ = (n : ℝ)^a := heqn.symm
      _ = _ := (Nat.cast_pow n a).symm
  exact_mod_cast hr

theorem polynomial_bound {n ℓ w a : ℕ} (hn : 1 ≤ n) (lam : ℝ)
    (hℓ : (ℓ : ℝ) ≤ lam*Real.log n) (ha : lam*w*Real.log 2 ≤ (a : ℝ))
    (hℓn : ℓ ≤ n) (hconst : (w+1)*2^w ≤ n) (hwidth : 2*w+1 ≤ n)
    (F : CNF (Fin n)) (hw : ∀ C ∈ F, C.card ≤ w) :
    encLength (lift F ℓ) ≤ n^(w+a+3) := by
  have hF : F.card ≤ n^(w+1) := by
    calc
      _ ≤ (w+1)*(2*n)^w := P2MFiniteCNFCounts.width_card hn F hw
      _ = ((w+1)*2^w)*n^w := by rw [Nat.mul_pow]; ring
      _ ≤ n*n^w := Nat.mul_le_mul_right _ hconst
      _ = _ := by rw [pow_succ]; ring
  have hfactor := exponential_factor hn lam hℓ ha
  have hlast : w*(ℓ/2+1)+1 ≤ n^2 := by
    have hhalf : ℓ/2+1 ≤ n+1 := by omega
    have hfirst : w*(ℓ/2+1)+1 ≤ (2*w+1)*n := by nlinarith
    exact hfirst.trans (by nlinarith)
  calc
    _ ≤ F.card*(2^ℓ)^w*(w*(ℓ/2+1)+1) := P2MMajorityLiftCounts.encoding_length_le F hw
    _ ≤ (n^(w+1)*n^a)*n^2 := Nat.mul_le_mul (Nat.mul_le_mul hF hfactor) hlast
    _ = _ := by rw [← pow_add,← pow_add]; congr 1; omega

theorem eventually_polynomial_size (lam : ℝ) (w : ℕ) :
    ∃ k : ℕ, ∀ᶠ n : ℕ in atTop, ∀ ℓ : ℕ, (ℓ : ℝ) ≤ lam*Real.log n →
      ∀ F : CNF (Fin n), (∀ C ∈ F, C.card ≤ w) → encLength (lift F ℓ) ≤ n^k := by
  let a := ⌈lam*w*Real.log 2⌉₊
  refine ⟨w+a+3,?_⟩
  filter_upwards [eventually_ge_atTop (max 1 (max ((w+1)*2^w) (2*w+1))),
    P2MLogGrowth.eventually_log_power_le lam 1 (C := 1) (by norm_num)] with n hn hlog
  intro ℓ hℓ F hw
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hc : (w+1)*2^w ≤ n := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hn
  have hw' : 2*w+1 ≤ n := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hn
  have hℓn : ℓ ≤ n := by
    have hh : (ℓ : ℝ) ≤ (n : ℝ) := hℓ.trans (by simpa only [pow_one,Real.rpow_one] using hlog)
    exact_mod_cast hh
  exact polynomial_bound hn1 lam hℓ (Nat.le_ceil _) hℓn hc hw' F hw

end AC02Frege.P2MMajorityLiftSize
end

section
-- Inlined Solutions.P2MDepth35Constants

set_option maxHeartbeats 2000000

namespace AC02Frege.P2MDepth35Constants

theorem choose_offset (c : ℝ) (hc : 0 < c) :
    ∃ a : ℝ, 1 ≤ a ∧ 2*Real.log 2+12 ≤ c*a^2/8 := by
  let d := 8*(2*Real.log 2+12)/c
  have hd : 0 ≤ d := by
    have hh : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    dsimp [d]
    positivity
  let a := max 1 (Real.sqrt d)
  have ha : 1 ≤ a := le_max_left _ _
  have hroot : Real.sqrt d ≤ a := le_max_right _ _
  have hsq : d ≤ a^2 := by have hs := Real.sq_sqrt hd; nlinarith [Real.sqrt_nonneg d]
  have hm := mul_le_mul_of_nonneg_left hsq hc.le
  have he : c*d = 8*(2*Real.log 2+12) := by dsimp [d]; field_simp
  exact ⟨a,ha,by nlinarith⟩

theorem choose_alpha (A lam₁ : ℝ) (hA : 0 < A) (hlam₁ : 0 < lam₁) :
    ∃ α : ℝ, 0 < α ∧ 16*A*(2*Real.exp A+1)*α ≤ Real.sqrt lam₁ := by
  let C := 2*Real.exp A+1
  have hC : 0 < C := by dsimp [C]; positivity
  let α := Real.sqrt lam₁/(32*A*C)
  have hα : 0 < α := by dsimp [α]; positivity
  have he : 16*A*C*α = Real.sqrt lam₁/2 := by
    dsimp [α]
    field_simp
    ring
  exact ⟨α,hα,by change 16*A*C*α ≤ Real.sqrt lam₁; rw [he]; nlinarith [Real.sqrt_nonneg lam₁]⟩

lemma rpow_three_halves {z : ℝ} (hz : 0 < z) : z^((3 : ℝ)/2) = z*Real.sqrt z := by
  rw [show (3 : ℝ)/2 = 1+1/2 by norm_num,Real.rpow_add hz,Real.rpow_one,Real.sqrt_eq_rpow]

lemma pc_degree_mono {n D E : ℕ} {F : LiftSAParity.CNF (Fin n)}
    {p : MvPolynomial (Fin n) (ZMod 2)} (hD : D ≤ E) (hp : PCDerivable F D p) :
    PCDerivable F E p := by
  rcases hp with hp | ⟨π,hπ,hdeg,hmem⟩
  · exact Or.inl hp
  · exact Or.inr ⟨π,hπ,fun q hq => (hdeg q hq).trans hD,hmem⟩

end AC02Frege.P2MDepth35Constants
end

section
-- Inlined Solutions.P2MDepth35AsymptoticGrowth

set_option maxHeartbeats 2000000

namespace AC02Frege.P2MDepth35AsymptoticGrowth

open Filter P2MProofComplexity.P2MLogGrowth

structure Ready (n ℓ w : ℕ) (c A α lam₁ : ℝ) : Prop where
  n_large : 2 ≤ n
  log_large : 1 ≤ Real.log (n : ℝ)
  block_le_n : ℓ ≤ n
  block_large : 2*A ≤ Real.sqrt (ℓ : ℝ)
  root_lower : Real.sqrt lam₁*Real.sqrt (Real.log (n : ℝ)) ≤ Real.sqrt (ℓ : ℝ)
  absorb : ∀ b : ℕ, b^2 ≤ ℓ →
    (b : ℝ)*(1+Real.log 64) ≤ α*Real.log n*Real.sqrt (Real.log (n : ℝ))
  inner_dom : (2*(2*Real.exp A+1)*α)*(Real.log (n : ℝ))^2 ≤ (n : ℝ)
  outer_dom : (6*(2*(2*Real.exp A+1)*α)*α)*(Real.log (n : ℝ))^4 ≤ Real.exp (Real.log (n : ℝ)/8)
  degree_dom : Real.exp (Real.log (n : ℝ)/4) ≤ c*n/128
  width_dom : ((w*(ℓ/2+1) : ℕ) : ℝ) ≤ c*n/16
  base_width_dom : ((2*w : ℕ) : ℝ) ≤ c*n/16
  degree_large : 16 ≤ c*(n : ℝ)
  size_dom : α*(Real.log (n : ℝ))^2 ≤ (n : ℝ)
  inverse_dom : 2*Real.exp A+2*Real.exp (Real.log (n : ℝ)/8) ≤ Real.exp (n : ℝ)

theorem eventually_ready (c A α lam₁ lam₂ : ℝ) (hc : 0 < c) (hA : 0 < A)
    (hα : 0 < α) (hlam₁ : 0 < lam₁) (hlam : lam₁ ≤ lam₂) (w : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ ℓ : ℕ, lam₁*Real.log n ≤ (ℓ : ℝ) →
      (ℓ : ℝ) ≤ lam₂*Real.log n → Ready n ℓ w c A α lam₁ := by
  let H := 2*(2*Real.exp A+1)*α
  let C₀ := 1+Real.log (64 : ℝ)
  have hlam₂ : 0 ≤ lam₂ := hlam₁.le.trans hlam
  have hC₀ : 0 ≤ C₀ := by
    have hh : 0 ≤ Real.log (64 : ℝ) := Real.log_nonneg (by norm_num)
    dsimp [C₀]
    linarith
  filter_upwards [eventually_ge_atTop 2,
    eventually_log_large (max 1 (max ((2*A)^2/lam₁) (Real.sqrt lam₂*C₀/α))),
    eventually_log_power_le lam₂ 1 (C := 1) (by norm_num),
    eventually_log_power_le H 2 (C := 1) (by norm_num),
    eventually_log_power_le (6*H*α) 4 (C := 1/8) (by norm_num),
    eventually_scaled_power_le (128/c) (1/4) 1 (by norm_num),
    eventually_log_power_le (16*(w : ℝ)*(lam₂+1)/c) 1 (C := 1) (by norm_num),
    eventually_log_power_le (32*(w : ℝ)/c) 0 (C := 1) (by norm_num),
    eventually_log_power_le (16/c) 0 (C := 1) (by norm_num),
    eventually_log_power_le α 2 (C := 1) (by norm_num),
    eventually_log_power_le (4*Real.exp A) 0 (C := 1) (by norm_num),
    eventually_scaled_power_le 4 (1/8) 1 (by norm_num)]
    with n hn hzall helln hR hS hquarter hwidth hbase hcn hsize hconst hinv
  intro ℓ hlow hupp
  let z := Real.log (n : ℝ)
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hz : 1 ≤ z := (le_max_left _ _).trans hzall
  have hzcut : (2*A)^2/lam₁ ≤ z :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans hzall
  have hzabs : Real.sqrt lam₂*C₀/α ≤ z :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans hzall
  have hpow (p : ℝ) : (n : ℝ)^p = Real.exp (z*p) := by rw [Real.rpow_def_of_pos hnp]
  have he8 : (n : ℝ)^(1/8 : ℝ) = Real.exp (z/8) := by rw [hpow]; congr 1; ring
  have he4 : (n : ℝ)^(1/4 : ℝ) = Real.exp (z/4) := by rw [hpow]; congr 1; ring
  simp only [pow_zero,pow_one,mul_one,Real.rpow_one] at helln hR hwidth hbase hcn hsize hconst hquarter hinv
  have hℓn : ℓ ≤ n := by exact_mod_cast hupp.trans helln
  have hlarge : 2*A ≤ Real.sqrt (ℓ : ℝ) := by
    have hh := (div_le_iff₀ hlam₁).mp hzcut
    exact Real.le_sqrt_of_sq_le (by nlinarith)
  have hroot : Real.sqrt lam₁*Real.sqrt z ≤ Real.sqrt (ℓ : ℝ) := by
    have hh := Real.sqrt_le_sqrt hlow
    rw [Real.sqrt_mul hlam₁.le] at hh
    exact hh
  have hQuarter : Real.exp (z/4) ≤ c*n/128 := by
    have hh : (128*(n : ℝ)^(1/4 : ℝ))/c ≤ (n : ℝ) := by convert hquarter using 1 <;> ring
    have hm := (div_le_iff₀ hc).mp hh
    rw [he4] at hm
    nlinarith
  have hWidth : ((w*(ℓ/2+1) : ℕ) : ℝ) ≤ c*n/16 := by
    have hh : (16*(w : ℝ)*(lam₂+1)*z)/c ≤ (n : ℝ) := by convert hwidth using 1 <;> ring
    have hm := (div_le_iff₀ hc).mp hh
    have hhalf : ((ℓ/2+1 : ℕ) : ℝ) ≤ (ℓ : ℝ)+1 := by exact_mod_cast (show ℓ/2+1 ≤ ℓ+1 by omega)
    have hwhole : ((ℓ/2+1 : ℕ) : ℝ) ≤ (lam₂+1)*z := by nlinarith
    have hw' := mul_le_mul_of_nonneg_left hwhole (Nat.cast_nonneg w : (0 : ℝ) ≤ _)
    push_cast at hw' ⊢
    nlinarith
  have hBase : ((2*w : ℕ) : ℝ) ≤ c*n/16 := by
    have hm := (div_le_iff₀ hc).mp hbase
    push_cast
    nlinarith
  have hCn : 16 ≤ c*(n : ℝ) := by have hm := (div_le_iff₀ hc).mp hcn; nlinarith
  have hInv : 2*Real.exp A+2*Real.exp (z/8) ≤ Real.exp (n : ℝ) := by
    rw [he8] at hinv
    have hh : 2*Real.exp A+2*Real.exp (z/8) ≤ (n : ℝ) := by nlinarith
    exact hh.trans ((by linarith : (n : ℝ) ≤ n+1).trans (Real.add_one_le_exp _))
  refine ⟨hn,hz,hℓn,hlarge,hroot,?_,hR,?_,hQuarter,hWidth,hBase,hCn,hsize,hInv⟩
  · intro b hb
    have hb' : (b : ℝ)^2 ≤ (ℓ : ℝ) := by exact_mod_cast hb
    have hbsqrt : (b : ℝ) ≤ Real.sqrt (ℓ : ℝ) := Real.le_sqrt_of_sq_le hb'
    have hsqrt := Real.sqrt_le_sqrt hupp
    rw [Real.sqrt_mul hlam₂] at hsqrt
    have hprod := mul_le_mul_of_nonneg_right (hbsqrt.trans hsqrt) hC₀
    have habs := (div_le_iff₀ hα).mp hzabs
    have hm := mul_le_mul_of_nonneg_right habs (Real.sqrt_nonneg z)
    dsimp [C₀] at hprod hm
    nlinarith
  · rw [he8] at hS
    exact hS

end AC02Frege.P2MDepth35AsymptoticGrowth
end

section
-- Inlined Solutions.P2MApproximationFactorChoice

set_option maxHeartbeats 2000000

namespace AC02Frege.P2MApproximationFactorChoice

theorem choose_factors {η L : ℝ} (hη : 0 < η) (hL : 0 < L) :
    ∃ t : ℕ, 1 ≤ t ∧ L ≤ η*(t : ℝ) ∧ (t : ℝ) ≤ L/η+1 := by
  refine ⟨⌈L/η⌉₊,Nat.one_le_ceil_iff.mpr (div_pos hL hη),?_,?_⟩
  · simpa only [mul_comm] using (div_le_iff₀ hη).mp (Nat.le_ceil (L/η))
  · exact (Nat.ceil_lt_add_one (div_nonneg hL.le hη.le)).le

theorem principal_error {T η L : ℝ} {t : ℕ} (hT : 0 < T)
    (hL : L = Real.log (64*T)) (hdecay : L ≤ η*(t : ℝ)) :
    T*Real.exp (-(η*t)) ≤ 1/64 := by
  have hpos : 0 < 64*T := by positivity
  calc
    _ ≤ T*Real.exp (-L) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hT.le
    _ = 1/64 := by
      rw [hL,Real.exp_neg,Real.exp_log hpos]
      field_simp

theorem choose_bounded {η L C : ℝ} (hη : 0 < η) (hL : 1 ≤ L) (hC : η⁻¹ ≤ C) :
    ∃ t : ℕ, 1 ≤ t ∧ L ≤ η*(t : ℝ) ∧ (t : ℝ) ≤ (C+1)*L := by
  obtain ⟨t,ht,hdecay,hub⟩ := choose_factors hη (by linarith : 0 < L)
  refine ⟨t,ht,hdecay,?_⟩
  have hm := mul_le_mul_of_nonneg_left hC (by linarith : 0 ≤ L)
  rw [div_eq_mul_inv] at hub
  nlinarith

theorem logarithmic_target {T : ℝ} (hT : 1 ≤ T) :
    1 ≤ 1+Real.log (64*T) ∧ 1+Real.log (64*T) = 1+Real.log 64+Real.log T := by
  have hTp : 0 < T := by linarith
  constructor
  · have hh : 0 ≤ Real.log (64*T) := Real.log_nonneg (by nlinarith)
    linarith
  · rw [Real.log_mul (by norm_num : (64 : ℝ) ≠ 0) hTp.ne']
    ring

end AC02Frege.P2MApproximationFactorChoice
end

section
-- Inlined Solutions.P2MDepth35FactorBounds

set_option maxHeartbeats 2000000

namespace AC02Frege.P2MDepth35FactorBounds

open P2MApproximationFactorChoice

theorem factor_parameters {n b : ℕ} {z x A α v T : ℝ} (η : ℕ → ℝ)
    (hz : 1 ≤ z) (hx : 0 < x) (hA : 0 < A) (hα : 0 < α) (hv : 0 < v)
    (hb : 1 ≤ b) (hbn : b ≤ n) (hbx : (b : ℝ) ≤ x) (hT : 1 ≤ T)
    (hsmooth : 16*A*(2*Real.exp A+1)*α ≤ v) (hroot : v*Real.sqrt z ≤ x)
    (hsmall : (b : ℝ)*Real.log T ≤ α*z*Real.sqrt z)
    (habsorb : (b : ℝ)*(1+Real.log 64) ≤ α*z*Real.sqrt z)
    (hRdom : (2*(2*Real.exp A+1)*α)*z^2 ≤ (n : ℝ))
    (hSdom : (6*(2*(2*Real.exp A+1)*α)*α)*z^4 ≤ Real.exp (z/8))
    (heta : ∀ d : ℕ, 1 ≤ d → d ≤ n → 0 < η d ∧ (η d)⁻¹ ≤ 2*Real.exp (A*d/x)) :
    ∃ tin tout : ℕ, 1 ≤ tin ∧ 1 ≤ tout ∧ b*tin ≤ n ∧
      ((b*tin : ℕ) : ℝ) ≤ (2*(2*Real.exp A+1)*α)*z*Real.sqrt z ∧
      ((b*tin*tout : ℕ) : ℝ) ≤ Real.exp (z/4) ∧
      T*Real.exp (-(η b*tin)) ≤ 1/64 ∧
      T*Real.exp (-(η (b*tin)*tout)) ≤ 1/64 ∧
      (η b)⁻¹+(η (b*tin))⁻¹ ≤ 2*Real.exp A+2*Real.exp (z/8) ∧
      Real.log T ≤ α*z^2 := by
  let C := 2*Real.exp A
  let H := 2*(C+1)*α
  let L := 1+Real.log (64*T)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hz0 : 0 ≤ z := by linarith
  have hu0 : 0 ≤ Real.sqrt z := Real.sqrt_nonneg _
  have hu2 : (Real.sqrt z)^2 = z := Real.sq_sqrt hz0
  have huz : Real.sqrt z ≤ z := by nlinarith
  have hq : z*Real.sqrt z ≤ z^2 := by nlinarith
  have hL : 1 ≤ L := (logarithmic_target hT).1
  have hLeq : L = 1+Real.log 64+Real.log T := (logarithmic_target hT).2
  have hbL : (b : ℝ)*L ≤ 2*α*z*Real.sqrt z := by rw [hLeq]; nlinarith
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : 0 ≤ (b : ℝ) := Nat.cast_nonneg _
  have hLq : L ≤ 2*α*z*Real.sqrt z := by nlinarith
  have hLz : L ≤ 2*α*z^2 := by nlinarith
  obtain ⟨hηb,hib⟩ := heta b hb hbn
  have hAb : A*(b : ℝ)/x ≤ A := (div_le_iff₀ hx).mpr (by nlinarith)
  have hibC : (η b)⁻¹ ≤ C := hib.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hAb) (by norm_num))
  obtain ⟨tin,htin,hdecayIn,htinBound⟩ := choose_bounded hηb hL hibC
  let R := b*tin
  have hR1 : 1 ≤ R := by dsimp [R]; nlinarith
  have hR0 : 0 ≤ (R : ℝ) := Nat.cast_nonneg _
  have hRq : (R : ℝ) ≤ H*z*Real.sqrt z := by
    have hm := mul_le_mul_of_nonneg_left htinBound hb0
    have hn := mul_le_mul_of_nonneg_left hbL (by linarith : 0 ≤ C+1)
    dsimp [R,H]
    push_cast
    nlinarith
  have hRz : (R : ℝ) ≤ H*z^2 := hRq.trans (by nlinarith)
  have hRn : R ≤ n := by exact_mod_cast hRz.trans hRdom
  have hAH : A*H ≤ v/8 := by dsimp [H,C]; nlinarith
  have hAR : A*(R : ℝ)/x ≤ z/8 := by
    apply (div_le_iff₀ hx).mpr
    calc
      _ ≤ A*(H*z*Real.sqrt z) := mul_le_mul_of_nonneg_left hRq hA.le
      _ = (A*H)*(z*Real.sqrt z) := by ring
      _ ≤ (v/8)*(z*Real.sqrt z) := mul_le_mul_of_nonneg_right hAH (by positivity)
      _ = (v*Real.sqrt z)*(z/8) := by ring
      _ ≤ x*(z/8) := mul_le_mul_of_nonneg_right hroot (by positivity)
      _ = _ := by ring
  obtain ⟨hηR,hiR⟩ := heta R hR1 hRn
  have hiRe : (η R)⁻¹ ≤ 2*Real.exp (z/8) :=
    hiR.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hAR) (by norm_num))
  obtain ⟨tout,htout,hdecayOut,htoutBound⟩ := choose_bounded hηR hL hiRe
  have he1 : 1 ≤ Real.exp (z/8) := Real.one_le_exp_iff.mpr (by positivity)
  have hout : (tout : ℝ) ≤ 3*Real.exp (z/8)*L := by nlinarith
  have hS : ((R*tout : ℕ) : ℝ) ≤ Real.exp (z/4) := by
    calc
      _ = (R : ℝ)*(tout : ℝ) := by norm_cast
      _ ≤ (H*z^2)*(3*Real.exp (z/8)*L) := mul_le_mul hRz hout (Nat.cast_nonneg _) (by positivity)
      _ ≤ (H*z^2)*(3*Real.exp (z/8)*(2*α*z^2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLz (by positivity)) (by positivity)
      _ = (6*H*α*z^4)*Real.exp (z/8) := by ring
      _ ≤ Real.exp (z/8)*Real.exp (z/8) := mul_le_mul_of_nonneg_right hSdom (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hTp : 0 < T := by linarith
  have hpin := principal_error hTp rfl (show Real.log (64*T) ≤ η b*(tin : ℝ) by dsimp [L] at hdecayIn; linarith)
  have hpout := principal_error hTp rfl (show Real.log (64*T) ≤ η R*(tout : ℝ) by dsimp [L] at hdecayOut; linarith)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlog : Real.log T ≤ α*z^2 := by nlinarith
  exact ⟨tin,tout,htin,htout,hRn,hRq,hS,hpin,hpout,add_le_add hibC hiRe,hlog⟩

end AC02Frege.P2MDepth35FactorBounds
end

section
-- Inlined Solutions.P2MDepth35DegreeBudgets

set_option maxHeartbeats 2000000

namespace AC02Frege.P2MDepth35DegreeBudgets

theorem budgets {n R tout W w : ℕ} {c : ℝ} (hcn : 16 ≤ c*(n : ℝ)) (htout : 1 ≤ tout)
    (hS : ((R*tout : ℕ) : ℝ) ≤ c*n/128) (hW : (W : ℝ) ≤ c*n/16)
    (hw : ((2*w : ℕ) : ℝ) ≤ c*n/16) :
    ⌊c*n/16⌋₊+max (2*R*tout+2*R) (R*tout+W) ≤ ⌊c*n⌋₊ ∧
      ⌊c*n/16⌋₊+2*w ≤ ⌊c*n⌋₊ := by
  have hcn0 : 0 ≤ c*(n : ℝ) := by linarith
  have hQ : (⌊c*n/16⌋₊ : ℝ) ≤ c*n/16 := Nat.floor_le (by positivity)
  have hD : c*(n : ℝ)-1 < (⌊c*n⌋₊ : ℝ) := Nat.sub_one_lt_floor _
  have hRS : R ≤ R*tout := by nlinarith
  have hRS' : (R : ℝ) ≤ (R : ℝ)*(tout : ℝ) := by exact_mod_cast hRS
  have h₁ : ⌊c*n/16⌋₊+(2*R*tout+2*R) ≤ ⌊c*n⌋₊ := by
    have hh : (⌊c*n/16⌋₊ : ℝ)+(2*(R : ℝ)*tout+2*R) ≤ (⌊c*n⌋₊ : ℝ) := by
      push_cast at hS
      nlinarith
    exact_mod_cast hh
  have h₂ : ⌊c*n/16⌋₊+(R*tout+W) ≤ ⌊c*n⌋₊ := by
    have hh : (⌊c*n/16⌋₊ : ℝ)+((R : ℝ)*tout+W) ≤ (⌊c*n⌋₊ : ℝ) := by
      push_cast at hS
      nlinarith
    exact_mod_cast hh
  have h₃ : ⌊c*n/16⌋₊+2*w ≤ ⌊c*n⌋₊ := by
    have hh : (⌊c*n/16⌋₊ : ℝ)+2*(w : ℝ) ≤ (⌊c*n⌋₊ : ℝ) := by
      push_cast at hw
      nlinarith
    exact_mod_cast hh
  exact ⟨by omega,h₃⟩

end AC02Frege.P2MDepth35DegreeBudgets
end

section
-- Inlined Solutions.PCOperations

open MvPolynomial

namespace AC02Frege.P2MSupport

theorem derivation_append {σ K : Type*} [Field K]
    (red : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (P : Set (MvPolynomial σ K))
    {π ρ : List (MvPolynomial σ K)}
    (hπ : PCNonBool.IsDerivation red P π)
    (hρ : PCNonBool.IsDerivation red P ρ) :
    PCNonBool.IsDerivation red P (π ++ ρ) := by
  intro k hk
  by_cases h : k < π.length
  · rcases hπ k h with ha | hc | hm
    · left
      simpa only [List.getElem_append_left h] using ha
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨i, j, hi, hj, a, b, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h),
        List.getElem_append_left (hj.trans h)] using hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨i, hi, v, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h)] using hiv
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt h)
    have hk' : k < ρ.length := by simp only [List.length_append] at hk; omega
    have hget (t : ℕ) (ht : t < ρ.length) :
        (π ++ ρ)[π.length + t]'(by simp only [List.length_append]; omega) = ρ[t] := by
      rw [List.getElem_append_right (Nat.le_add_right π.length t)]
      simp only [Nat.add_sub_cancel_left]
    rcases hρ k hk' with ha | hc | hm
    · left
      obtain ⟨a, ha, c, hac⟩ := ha
      exact ⟨a, ha, c, (hget k hk').trans hac⟩
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨π.length + i, π.length + j, by omega, by omega, a, b, ?_⟩
      rw [hget k hk', hget i (hi.trans hk'), hget j (hj.trans hk')]
      exact hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨π.length + i, by omega, v, ?_⟩
      rw [hget k hk', hget i (hi.trans hk')]
      exact hiv

theorem derivation_snoc {σ K : Type*} [Field K]
    (red : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (P : Set (MvPolynomial σ K)) {π : List (MvPolynomial σ K)}
    (hπ : PCNonBool.IsDerivation red P π) (p : MvPolynomial σ K)
    (hp :
      (∃ a ∈ P, ∃ c : K, p = c • red a) ∨
      (∃ (i j : ℕ) (hi : i < π.length) (hj : j < π.length) (a b : K),
        p = a • π[i] + b • π[j]) ∨
      (∃ (i : ℕ) (hi : i < π.length) (v : σ), p = red (X v * π[i]))) :
    PCNonBool.IsDerivation red P (π ++ [p]) := by
  intro k hk
  by_cases h : k < π.length
  · rcases hπ k h with ha | hc | hm
    · left; simpa only [List.getElem_append_left h] using ha
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨i, j, hi, hj, a, b, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h),
        List.getElem_append_left (hj.trans h)] using hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨i, hi, v, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h)] using hiv
  · have heq : k = π.length := by simp only [List.length_append, List.length_singleton] at hk; omega
    subst k
    have hlast : (π ++ [p])[π.length] = p := by
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero]
    rcases hp with ha | hc | hm
    · left; simpa only [hlast] using ha
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨i, j, hi, hj, a, b, ?_⟩
      simpa only [hlast, List.getElem_append_left hi, List.getElem_append_left hj] using hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨i, hi, v, ?_⟩
      simpa only [hlast, List.getElem_append_left hi] using hiv

theorem pc_zero {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ) :
    PCDerivable F D 0 := Or.inl rfl

theorem pc_degree {n : ℕ} {F : LiftSAParity.CNF (Fin n)} {D : ℕ}
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : PCDerivable F D p) : p.totalDegree ≤ D := by
  rcases hp with rfl | ⟨π, _, hdeg, hp⟩
  · simp
  · exact hdeg p hp

theorem pc_smul {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : PCDerivable F D p) (c : ZMod 2) :
    PCDerivable F D (c • p) := by
  rcases hp with rfl | ⟨π, hπ, hdeg, hp⟩
  · simp only [smul_zero]; exact pc_zero F D
  · obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
    refine Or.inr ⟨π ++ [c • p], ?_, ?_, by simp⟩
    · apply derivation_snoc _ _ hπ
      right; left
      exact ⟨i, i, hi, hi, c, 0, by simp only [hpi, zero_smul, add_zero]⟩
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hdeg q hq
      · have heq : q = c • p := List.mem_singleton.mp hq
        subst q
        exact (totalDegree_smul_le c p).trans (hdeg p hp)

theorem pc_add {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    {p q : MvPolynomial (Fin n) (ZMod 2)}
    (hp : PCDerivable F D p) (hq : PCDerivable F D q) :
    PCDerivable F D (p + q) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simpa only [zero_add] using hq
  rcases hq with rfl | ⟨ρ, hρ, hρdeg, hq⟩
  · simpa only [add_zero] using (show PCDerivable F D p from Or.inr ⟨π, hπ, hπdeg, hp⟩)
  have hboth := derivation_append _ _ hπ hρ
  have hp' : p ∈ π ++ ρ := List.mem_append_left _ hp
  have hq' : q ∈ π ++ ρ := List.mem_append_right _ hq
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp'
  obtain ⟨j, hj, hqj⟩ := List.mem_iff_getElem.mp hq'
  refine Or.inr ⟨(π ++ ρ) ++ [p + q], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hboth
    right; left
    exact ⟨i, j, hi, hj, 1, 1, by simp only [hpi, hqj, one_smul]⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact hπdeg r hr
      · exact hρdeg r hr
    · have heq : r = p + q := List.mem_singleton.mp hr
      subst r
      exact (totalDegree_add p q).trans (max_le (hπdeg p hp) (hρdeg q hq))

theorem pc_mul_X {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : PCDerivable F D p)
    (v : Fin n) (hdeg : p.totalDegree + 1 ≤ D) :
    PCDerivable F D (p * X v) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simp only [zero_mul]; exact pc_zero F D
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [p * X v], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; right
    exact ⟨i, hi, v, by simp only [hpi, LinearMap.id_apply, mul_comm]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hπdeg q hq
    · have heq : q = p * X v := List.mem_singleton.mp hq
      subst q
      exact (totalDegree_mul p (X v)).trans (by simpa only [totalDegree_X] using hdeg)

theorem pc_axiom {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : p ∈ pcAxioms F)
    (hdeg : p.totalDegree ≤ D) : PCDerivable F D p := by
  refine Or.inr ⟨[p], ?_, by simpa using hdeg, by simp⟩
  intro k hk
  have heq : k = 0 := by simpa using hk
  subst k
  left
  exact ⟨p, hp, 1, by simp⟩

end AC02Frege.P2MSupport
end

section
-- Inlined Solutions.P2MDepth35ProofSize

set_option maxHeartbeats 2000000

namespace AC02Frege.P2MDepth35ProofSize

open LiftSAParity MvPolynomial

lemma no_empty_base {n D : ℕ} (F : CNF (Fin n)) (hF : ¬ PCDerivable F D 1) :
    (∅ : Clause (Fin n)) ∉ F := by
  intro h
  apply hF
  have hh := P2MSupport.pc_axiom F D (clauseCompl ∅) (Or.inl ⟨∅,h,rfl⟩) (by simp [clauseCompl])
  simpa only [clauseCompl,Finset.prod_empty] using hh

lemma no_empty_lift {n : ℕ} (F : CNF (Fin n)) (ℓ : ℕ) (hF : (∅ : Clause (Fin n)) ∉ F) :
    (∅ : Clause (Fin n × Fin ℓ)) ∉ lift F ℓ := by
  classical
  intro h
  obtain ⟨J,hJ,hCJ⟩ := Finset.mem_biUnion.mp h
  obtain ⟨A,hA,heq⟩ := Finset.mem_image.mp hCJ
  have hJne : J.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by intro he; subst J; exact hF hJ)
  obtain ⟨l,hl⟩ := hJne
  have hc : (A l hl).card = ℓ/2+1 := (Finset.mem_powersetCard.mp (Finset.mem_pi.mp hA l hl)).2
  have hne : (A l hl).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a,ha⟩ := hne
  have hm : ((l.1,a),l.2) ∈ J.attach.biUnion
      (fun l => (A l.1 l.2).image (fun a : Fin ℓ => ((l.1.1,a),l.1.2))) := by
    apply Finset.mem_biUnion.mpr
    refine ⟨⟨l,hl⟩,Finset.mem_attach _ _,?_⟩
    exact Finset.mem_image.mpr ⟨a,ha,rfl⟩
  rw [heq] at hm
  exact Finset.notMem_empty _ hm

lemma initial_nonempty {V : Type} [DecidableEq V] (Γ : CNF V)
    (E : Line V → Prop) (hΓ : (∅ : Clause V) ∉ Γ) (hE : ∀ L, ¬ E L)
    {L : Line V} (hi : Infers Γ E L) : L.Nonempty := by
  classical
  cases hi with
  | axOne => simp
  | axTop => simp
  | axEM u => simp
  | input C hC =>
    have hCne : C.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by intro he; subst C; exact hΓ hC)
    exact hCne.image (fun l => ({litPoly l} : Term V))
  | weaken _ _ h _ => exact (hE _ h).elim
  | proj _ _ _ h _ => exact (hE _ h).elim
  | conj _ _ _ _ h _ => exact (hE _ h).elim
  | cut _ _ _ h _ => exact (hE _ h).elim
  | lin _ _ _ _ h _ => exact (hE _ h).elim
  | mul _ _ _ h => exact (hE _ h).elim
  | del _ h => exact (hE _ h).elim

theorem total_size_pos {V : Type} [DecidableEq V] {b : ℕ} (Γ : CNF V)
    (hΓ : (∅ : Clause V) ∉ Γ) (π : List (Line V)) (hπ : IsRefutation b Γ π) :
    1 ≤ totalSize π := by
  classical
  cases π with
  | nil => simpa [IsRefutation] using hπ
  | cons L π =>
    have hi := hπ.2.2.1 0 (by simp)
    have hL : L.Nonempty := initial_nonempty Γ _ hΓ (by
      intro L h
      obtain ⟨j,hj,_⟩ := h
      omega) hi
    obtain ⟨T,hT⟩ := hL
    have ht : 1 ≤ 1+∑ u ∈ T, u.support.card := by omega
    have hsum : (1+∑ u ∈ T, u.support.card) ≤ ∑ T ∈ L, (1+∑ u ∈ T, u.support.card) :=
      Finset.single_le_sum (f := fun W : Term V => 1+∑ u ∈ W, u.support.card)
        (fun _ _ => Nat.zero_le _) hT
    have hh : 1 ≤ ∑ T ∈ L, (1+∑ u ∈ T, u.support.card) := ht.trans hsum
    simp only [totalSize,List.map_cons,List.sum_cons]
    exact hh.trans (Nat.le_add_right _ _)

end AC02Frege.P2MDepth35ProofSize
end

section
-- Inlined Solutions.P2MDepth35Numerics

set_option maxHeartbeats 2000000

namespace AC02Frege.P2MDepth35Numerics

lemma small_noise {n N : ℝ} (hn : 1 ≤ n) (hN : 0 ≤ N) (hNn : N ≤ n^2) :
    2*N^2*Real.exp (2*n)*Real.exp (-12*n) ≤ 2/7 := by
  have hn0 : 0 ≤ n := by linarith
  have hnexp : n ≤ Real.exp n := (by linarith : n ≤ n+1).trans (Real.add_one_le_exp n)
  have hfour : n^4 ≤ Real.exp (4*n) := by
    have h := pow_le_pow_left₀ hn0 hnexp 4
    rw [← Real.exp_nat_mul] at h
    convert h using 1 <;> congr 1 <;> ring
  have hN2 : N^2 ≤ n^4 := by nlinarith [sq_nonneg (N-n^2)]
  have hlast : Real.exp (-6 : ℝ) ≤ 1/7 := by
    rw [Real.exp_neg,one_div]
    apply (inv_le_inv₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 7)).mpr
    have h := Real.add_one_le_exp (6 : ℝ)
    linarith
  calc
    _ = 2*N^2*Real.exp (-10*n) := by rw [mul_assoc (2*N^2),← Real.exp_add]; congr 2; ring
    _ ≤ 2*n^4*Real.exp (-10*n) := mul_le_mul_of_nonneg_right (by nlinarith) (Real.exp_nonneg _)
    _ ≤ 2*Real.exp (4*n)*Real.exp (-10*n) := mul_le_mul_of_nonneg_right (by nlinarith) (Real.exp_nonneg _)
    _ = 2*Real.exp (-6*n) := by rw [mul_assoc,← Real.exp_add]; congr 1; ring
    _ ≤ 2*Real.exp (-6 : ℝ) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
    _ ≤ _ := by linarith

lemma tiny_fraction {n : ℝ} (hn : 1 ≤ n) : Real.exp (-12*n) ≤ 1/2 := by
  rw [show -12*n = -(12*n) by ring,Real.exp_neg,one_div]
  apply (inv_le_inv₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 2)).mpr
  have h := Real.add_one_le_exp (12*n)
  linarith

/-- Numerical contradiction underlying the depth-3.5 lower bound after both factor counts
have made the principal errors at most `1/(64T)`. -/
theorem rank_bound_lt {n N T h e E ei eo ib iR : ℝ}
    (hn : 1 ≤ n) (hN : 0 ≤ N) (hNn : N ≤ n^2) (hh : 0 < h) (he0 : 0 ≤ e)
    (he : e ≤ Real.exp (-12*n)*h) (hE : E ≤ Real.exp (-12*n)*h)
    (hi : T*ei ≤ 1/64) (ho : T*eo ≤ 1/64)
    (hrank : T*(ib+iR) ≤ Real.exp (2*n)) :
    T*(ei+eo)*(h+e)+2*T*N^2*e*(ib+iR)+E < h := by
  have hsmall := tiny_fraction hn
  have heh : e ≤ h/2 := he.trans (by nlinarith)
  have hEh : E ≤ h/2 := hE.trans (by nlinarith)
  have hT : T*(ei+eo) ≤ 1/32 := by rw [mul_add]; linarith
  have hfirst : T*(ei+eo)*(h+e) ≤ (3/64)*h := by
    have hh0 : 0 ≤ h+e := by linarith
    have hm := mul_le_mul_of_nonneg_right hT hh0
    nlinarith
  have herror : 2*T*N^2*e*(ib+iR) ≤ (2/7)*h := by
    calc
      _ = (2*N^2*e)*(T*(ib+iR)) := by ring
      _ ≤ (2*N^2*e)*Real.exp (2*n) := mul_le_mul_of_nonneg_left hrank (by positivity)
      _ ≤ (2*N^2*(Real.exp (-12*n)*h))*Real.exp (2*n) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity)) (Real.exp_nonneg _)
      _ = (2*N^2*Real.exp (2*n)*Real.exp (-12*n))*h := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (small_noise hn hN hNn) hh.le
  linarith

end AC02Frege.P2MDepth35Numerics
end

section
-- Inlined Solutions.P2MExcludedCumulativeCounts

set_option maxHeartbeats 2000000

namespace AC02Frege.P2MExcludedCumulativeCounts

open Finset

def badLayer (n ℓ Q j : ℕ) : ℕ :=
  ((univ : Finset (Finset (Fin n × Fin ℓ))).filter
    (fun T => T.card = j ∧ Q < (heavyBlocks T).card)).card

lemma excluded_sum (n ℓ Q j : ℕ) : Eexcl n ℓ Q j = ∑ i ∈ range (j+1), badLayer n ℓ Q i := by
  let A := (univ : Finset (Finset (Fin n × Fin ℓ))).filter (fun T => Q < (heavyBlocks T).card)
  have h := sum_card_fiberwise_eq_card_filter A (range (j+1)) (fun T => T.card)
  simpa only [A,Eexcl,badLayer,filter_filter,mem_range,Nat.lt_succ_iff,and_comm] using h.symm

lemma layer_fraction_le (n ℓ Q K j : ℕ) (hj : j ≤ K) :
    (badLayer n ℓ Q j : ℝ)/((n*ℓ).choose j : ℝ) ≤ epsExcl n ℓ Q K := by
  exact Finset.le_sup' (fun i : ℕ => (badLayer n ℓ Q i : ℝ)/((n*ℓ).choose i : ℝ))
    (show j ∈ range (K+1) by simpa using hj)

lemma eps_nonneg (n ℓ Q K : ℕ) : 0 ≤ epsExcl n ℓ Q K := by
  exact (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans (layer_fraction_le n ℓ Q K 0 (by omega))

lemma excluded_bound (n ℓ Q K j : ℕ) (hj : j ≤ K) (hKN : K ≤ n*ℓ) :
    (Eexcl n ℓ Q j : ℝ) ≤ epsExcl n ℓ Q K*(monoCount (n*ℓ) j : ℝ) := by
  rw [excluded_sum,Nat.cast_sum,monoCount,Nat.cast_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hij : i ≤ j := by have := mem_range.mp hi; omega
  have hp : (0 : ℝ) < ((n*ℓ).choose i : ℝ) := by
    exact_mod_cast Nat.choose_pos (hij.trans (hj.trans hKN))
  exact (div_le_iff₀ hp).mp (layer_fraction_le n ℓ Q K i (hij.trans hj))

lemma cumulative_choose_le (N j : ℕ) (hj : j ≤ N/2) :
    monoCount N j ≤ (j+1)*N.choose j := by
  have hchoose : ∀ i ≤ j, N.choose i ≤ N.choose j := by
    intro i hij
    have hh : ∀ t, i ≤ t → t ≤ j → N.choose i ≤ N.choose t := by
      intro t hit
      induction t,hit using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ t hit ih =>
        intro htj
        exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))
    exact hh j hij le_rfl
  unfold monoCount
  calc
    _ ≤ ∑ _i ∈ range (j+1), N.choose j := by
      apply Finset.sum_le_sum
      intro i hi
      exact hchoose i (by have := mem_range.mp hi; omega)
    _ = _ := by simp

end AC02Frege.P2MExcludedCumulativeCounts
end

section
-- Inlined Solutions.P2MDepth35FiniteContradiction

set_option maxHeartbeats 2000000

namespace AC02Frege.P2MDepth35FiniteContradiction

open MvPolynomial LiftSAParity

theorem no_small_refutation {n ℓ : ℕ} (hℓ : Odd ℓ) (F : CNF (Fin n))
    (b D Q K tin tout : ℕ) (htin : 1 ≤ tin) (htout : 1 ≤ tout)
    (π : List (Line (Fin n × Fin ℓ))) (hπ : IsRefutation b (lift F ℓ) π)
    (hRK : b*tin ≤ K) (hKN : 2*K < n*ℓ)
    (h41a : Q+max (2*(b*tin)*tout+2*(b*tin)) (b*tin*tout+width (lift F ℓ)) ≤ D)
    (h41b : Q+2*width F ≤ D)
    (hn : 1 ≤ (n : ℝ)) (hN : ((n*ℓ : ℕ) : ℝ) ≤ (n : ℝ)^2)
    (hh : 0 < (hThresh F ℓ D K : ℝ))
    (he : epsExcl n ℓ Q K*(monoCount (n*ℓ) K : ℝ) ≤ Real.exp (-12*(n : ℝ))*(hThresh F ℓ D K : ℝ))
    (hE : (Eexcl n ℓ Q K : ℝ) ≤ Real.exp (-12*(n : ℝ))*(hThresh F ℓ D K : ℝ))
    (hi : (totalSize π : ℝ)*Real.exp (-(etaFrac (n*ℓ) K b*tin)) ≤ 1/64)
    (ho : (totalSize π : ℝ)*Real.exp (-(etaFrac (n*ℓ) K (b*tin)*tout)) ≤ 1/64)
    (hrank : (totalSize π : ℝ)*((etaFrac (n*ℓ) K b)⁻¹+(etaFrac (n*ℓ) K (b*tin))⁻¹) ≤
      Real.exp (2*(n : ℝ))) : False := by
  have hc := (_root_.AC02Frege.corollary_5_3_rank_criterion hℓ F b D Q K tin tout htin htout π hπ hRK hKN h41a h41b).2
  have he0 : 0 ≤ epsExcl n ℓ Q K*(monoCount (n*ℓ) K : ℝ) :=
    mul_nonneg (P2MExcludedCumulativeCounts.eps_nonneg _ _ _ _) (Nat.cast_nonneg _)
  have hnum := P2MDepth35Numerics.rank_bound_lt hn (Nat.cast_nonneg (n*ℓ)) hN hh he0 he hE hi ho hrank
  apply (not_le_of_gt hnum)
  simpa only [mul_assoc] using hc

end AC02Frege.P2MDepth35FiniteContradiction
end

section
-- Inlined Solutions.P2MMajorityCutoff

set_option maxHeartbeats 2000000

namespace AC02Frege.P2MMajorityCutoff

theorem offset_bounds (n ℓ : ℕ) (a : ℝ) (hn : 1 ≤ n) (ha : 1 ≤ a)
    (hℓ : 128*(a+2) ≤ Real.sqrt ℓ) :
    0 ≤ ((n*ℓ : ℕ) : ℝ)/2-a*n*Real.sqrt ℓ ∧
    n ≤ ⌊((n*ℓ : ℕ) : ℝ)/2-a*n*Real.sqrt ℓ⌋₊ ∧
    2*⌊((n*ℓ : ℕ) : ℝ)/2-a*n*Real.sqrt ℓ⌋₊ < n*ℓ := by
  let x := Real.sqrt (ℓ : ℝ)
  have hx : 1 ≤ x := by dsimp [x]; linarith
  have hxa : 1 ≤ x/2-a := by dsimp [x]; linarith
  have hx2 : x^2 = (ℓ : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hprod : (1 : ℝ) ≤ x*(x/2-a) := by
    have h := mul_le_mul hx hxa (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ x)
    simpa only [one_mul] using h
  have hfactor : 1 ≤ (ℓ : ℝ)/2-a*x := by nlinarith
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have harg : (n : ℝ) ≤ ((n*ℓ : ℕ) : ℝ)/2-a*n*Real.sqrt ℓ := by
    have h := mul_le_mul_of_nonneg_left hfactor hn0.le
    dsimp [x] at h
    push_cast
    nlinarith
  have harg0 : 0 ≤ ((n*ℓ : ℕ) : ℝ)/2-a*n*Real.sqrt ℓ := hn0.le.trans harg
  refine ⟨harg0,?_,?_⟩
  · calc
      _ = ⌊(n : ℝ)⌋₊ := (Nat.floor_natCast n).symm
      _ ≤ _ := Nat.floor_mono harg
  · have hf := Nat.floor_le harg0
    have hp : 0 < a*n*Real.sqrt ℓ := by
      have ha0 : 0 < a := by linarith
      have hx0 : 0 < Real.sqrt (ℓ : ℝ) := by dsimp [x] at hx; linarith
      positivity
    have hh : (2 : ℝ)*⌊((n*ℓ : ℕ) : ℝ)/2-a*n*Real.sqrt ℓ⌋₊ < (n*ℓ : ℕ) := by linarith
    exact_mod_cast hh

end AC02Frege.P2MMajorityCutoff
end

section
-- Inlined Solutions.P2MBooleanAlgebra

open MvPolynomial AC02Frege
namespace AC02Frege.P2MBooleanAlgebra

theorem ml_monomial {V : Type*} (s : V →₀ ℕ) (c : ZMod 2) :
    ML (monomial s c) = monomial (sqfree s) c := by
  have h := (basisMonomials V (ZMod 2)).constr_basis (ZMod 2)
    (fun t => monomial (sqfree t) (1 : ZMod 2)) s
  have hc : monomial s c = c • monomial s (1 : ZMod 2) := by
    simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hc, map_smul]
  change c • ((basisMonomials V (ZMod 2)).constr (ZMod 2)
    (fun t => monomial (sqfree t) (1 : ZMod 2)) (monomial s 1)) = _
  rw [show monomial s (1 : ZMod 2) = basisMonomials V (ZMod 2) s by rfl]
  rw [h]
  simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

theorem ml_multilinear {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    IsMultilinear (ML p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [ml_monomial]
    intro t ht v
    have ht' : t = sqfree s := (Finset.mem_singleton.mp (support_monomial_subset ht))
    subst t
    simp [sqfree, Finsupp.mapRange_apply]
  | add p q hp hq =>
    rw [map_add]
    intro s hs v
    rcases Finset.mem_union.mp (support_add hs) with hs | hs
    · exact hp s hs v
    · exact hq s hs v


theorem sqfree_support {V : Type*} (s : V →₀ ℕ) : (sqfree s).support = s.support := by
  classical
  ext i
  simp only [Finsupp.mem_support_iff, sqfree, Finsupp.mapRange_apply]
  omega

theorem sqfree_eq_self {V : Type*} (s : V →₀ ℕ) (hs : ∀ i, s i ≤ 1) : sqfree s = s := by
  ext i
  simp only [sqfree, Finsupp.mapRange_apply, min_eq_left (hs i)]

theorem ml_of_multilinear {V : Type*} (p : MvPolynomial V (ZMod 2))
    (hp : IsMultilinear p) : ML p = p := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, ml_monomial]
  conv_rhs => rw [p.as_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [sqfree_eq_self s (hp s hs)]

theorem ml_idempotent {V : Type*} (p : MvPolynomial V (ZMod 2)) : ML (ML p) = ML p :=
  ml_of_multilinear _ (ml_multilinear p)

theorem eval_ml {V : Type*} (p : MvPolynomial V (ZMod 2)) (x : V → ZMod 2) :
    eval x (ML p) = eval x p := by
  classical
  have hpow (a : ZMod 2) (k : ℕ) : a ^ min k 1 = a ^ k := by
    fin_cases a
    · change (0 : ZMod 2) ^ min k 1 = (0 : ZMod 2) ^ k
      cases k <;> simp
    · change (1 : ZMod 2) ^ min k 1 = (1 : ZMod 2) ^ k
      simp
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [ml_monomial, eval_monomial, eval_monomial]
    congr 1
    simp only [Finsupp.prod, sqfree_support]
    apply Finset.prod_congr rfl
    intro i _
    simpa only [sqfree, Finsupp.mapRange_apply] using hpow (x i) (s i)
  | add p q hp hq => simp only [map_add, hp, hq]

theorem multilinear_ext {V : Type} [Finite V]
    {p q : MvPolynomial V (ZMod 2)}
    (hp : IsMultilinear p) (hq : IsMultilinear q)
    (h : ∀ x : V → ZMod 2, eval x p = eval x q) : p = q := by
  apply sub_eq_zero.mp
  apply MvPolynomial.eq_zero_of_eval_eq_zero V (ZMod 2) (p - q)
  · intro x; simp only [map_sub, h x, sub_self]
  · have hp' : p ∈ restrictDegree V (ZMod 2) 1 := (mem_restrictDegree V p 1).mpr hp
    have hq' : q ∈ restrictDegree V (ZMod 2) 1 := (mem_restrictDegree V q 1).mpr hq
    simpa only [ZMod.card, Nat.reduceSub] using (restrictDegree V (ZMod 2) 1).sub_mem hp' hq'

theorem ml_mul_left {V : Type} [Finite V] (p q : MvPolynomial V (ZMod 2)) :
    ML (ML p * q) = ML (p * q) := by
  apply multilinear_ext (ml_multilinear _) (ml_multilinear _)
  intro x
  simp only [eval_ml, map_mul]

theorem ml_mul_right {V : Type} [Finite V] (p q : MvPolynomial V (ZMod 2)) :
    ML (p * ML q) = ML (p * q) := by
  rw [mul_comm p (ML q), ml_mul_left, mul_comm]

theorem xMon_eq_monomial {V : Type*} (S : Finset V) :
    xMon S = monomial (Finsupp.indicator S (fun _ _ => 1)) (1 : ZMod 2) := by
  classical
  simpa only [xMon, pow_one] using (prod_X_pow (R := ZMod 2) (fun _ : V => 1) S)

theorem indicator_support {V : Type*} (S : Finset V) :
    (Finsupp.indicator S (fun _ _ => (1 : ℕ))).support = S := by
  classical
  ext i
  simp only [Finsupp.mem_support_iff, Finsupp.indicator_apply]
  split_ifs <;> simp_all

theorem xMon_multilinear {V : Type*} (S : Finset V) : IsMultilinear (xMon S) := by
  classical
  rw [xMon_eq_monomial]
  intro s hs i
  have heq := Finset.mem_singleton.mp (support_monomial_subset hs)
  subst s
  simp only [Finsupp.indicator_apply]
  split_ifs <;> omega

theorem xMon_eval {V : Type*} (S : Finset V) (x : V → ZMod 2) :
    eval x (xMon S) = ∏ i ∈ S, x i := by
  simp only [xMon, map_prod, eval_X]

theorem xMon_totalDegree {V : Type*} (S : Finset V) : (xMon S).totalDegree = S.card := by
  classical
  rw [xMon_eq_monomial, totalDegree_monomial _ (one_ne_zero : (1 : ZMod 2) ≠ 0)]
  simp only [Finsupp.sum, indicator_support]
  have heq : (∑ i ∈ S, (Finsupp.indicator S (fun _ _ => (1 : ℕ))) i) = ∑ _i ∈ S, 1 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finsupp.indicator_apply, hi]
  rw [heq]
  simp

theorem xMon_linearIndependent {V : Type*} :
    LinearIndependent (ZMod 2) (fun S : Finset V => xMon S) := by
  classical
  have hinj : Function.Injective (fun S : Finset V => Finsupp.indicator S (fun _ _ => (1 : ℕ))) := by
    intro S T h
    have := congrArg Finsupp.support h
    simpa only [indicator_support] using this
  have h := (basisMonomials V (ZMod 2)).linearIndependent.comp
    (fun S : Finset V => Finsupp.indicator S (fun _ _ => (1 : ℕ))) hinj
  simpa only [Function.comp_def, coe_basisMonomials, xMon_eq_monomial] using h

end AC02Frege.P2MBooleanAlgebra
end

section
-- Inlined Solutions.P2MMajorityFoundation

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra

namespace AC02Frege.P2MMajorityFoundation

open Classical

noncomputable def pointPoly {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) : MvPolynomial V (ZMod 2) :=
  ∏ i : V, if i ∈ S then X i else 1 + X i

theorem pointPoly_indicator {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    pointPoly S = MvPolynomial.indicator (fun i : V => if i ∈ S then (1 : ZMod 2) else 0) := by
  classical
  unfold pointPoly MvPolynomial.indicator
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp only [hi, ↓reduceIte, ZMod.card, Nat.reduceSub, pow_one]
  · simp only [map_one, CharTwo.sub_eq_add]
    calc
      X i = X i + (1 + 1) := by rw [CharTwo.add_self_eq_zero, add_zero]
      _ = 1 + (X i + 1) := by abel
  · simp [CharTwo.sub_eq_add]

theorem pointPoly_multilinear {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    IsMultilinear (pointPoly S) := by
  rw [pointPoly_indicator]
  apply (mem_restrictDegree V _ 1).mp
  simpa only [ZMod.card, Nat.reduceSub] using indicator_mem_restrictDegree
    (fun i : V => if i ∈ S then (1 : ZMod 2) else 0)

theorem pointPoly_eval {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) (x : V → ZMod 2) :
    eval x (pointPoly S) =
      if x = (fun i => if i ∈ S then (1 : ZMod 2) else 0) then 1 else 0 := by
  classical
  rw [pointPoly_indicator]
  split_ifs with h
  · subst x; exact eval_indicator_apply_eq_one _
  · exact eval_indicator_apply_eq_zero _ _ h

theorem multilinear_sum {V ι : Type} (S : Finset ι) (f : ι → MvPolynomial V (ZMod 2))
    (hf : ∀ i ∈ S, IsMultilinear (f i)) : IsMultilinear (∑ i ∈ S, f i) := by
  apply (mem_restrictDegree V _ 1).mp
  exact Submodule.sum_mem _ (fun i hi => (mem_restrictDegree V (f i) 1).mpr (hf i hi))

theorem majOne_multilinear (ℓ : ℕ) : IsMultilinear (majOne ℓ) := by
  unfold majOne
  apply multilinear_sum
  intro S _
  simpa only [pointPoly] using pointPoly_multilinear S

theorem eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

theorem point_of_ones {V : Type} [Fintype V] [DecidableEq V] (x : V → ZMod 2) :
    (fun i => if i ∈ Finset.univ.filter (fun i => x i = 1) then (1 : ZMod 2) else 0) = x := by
  classical
  funext i
  rcases eq_zero_or_one (x i) with hi | hi <;> simp [hi]

theorem ones_of_point {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    Finset.univ.filter (fun i => (if i ∈ S then (1 : ZMod 2) else 0) = 1) = S := by
  classical
  ext i
  simp

theorem majOne_eval (ℓ : ℕ) (x : Fin ℓ → ZMod 2) :
    eval x (majOne ℓ) = if ℓ / 2 < (Finset.univ.filter (fun i => x i = 1)).card
      then 1 else 0 := by
  classical
  unfold majOne
  simp only [map_sum]
  have hev (S : Finset (Fin ℓ)) := pointPoly_eval S x
  simp only [pointPoly] at hev
  simp only [hev]
  have heq (S : Finset (Fin ℓ)) :
      x = (fun i => if i ∈ S then (1 : ZMod 2) else 0) ↔
        S = Finset.univ.filter (fun i => x i = 1) := by
    constructor
    · intro hx; rw [hx, ones_of_point]
    · intro hS; subst S; exact (point_of_ones x).symm
  simp only [heq]
  simp

theorem heavy_monomial_absorbs_majority (ℓ : ℕ) (S : Finset (Fin ℓ))
    (hS : ℓ / 2 < S.card) : ML (xMon S * majOne ℓ) = xMon S := by
  apply multilinear_ext (ml_multilinear _) (xMon_multilinear S)
  intro x
  simp only [eval_ml, map_mul]
  by_cases hx : eval x (xMon S) = 0
  · rw [hx, zero_mul]
  · have hsub : S ⊆ Finset.univ.filter (fun i => x i = 1) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hxi : x i ≠ 0 := by
        intro hz
        apply hx
        rw [xMon_eval]
        exact Finset.prod_eq_zero hi hz
      rcases eq_zero_or_one (x i) with hz | ho
      · exact False.elim (hxi hz)
      · exact ho
    have hcard := Finset.card_le_card hsub
    rw [majOne_eval, if_pos (by omega), mul_one]

theorem pointPoly_factor {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    pointPoly S = xMon S * ∏ i ∈ Finset.univ.filter (fun i : V => i ∉ S),
      (1 + X i : MvPolynomial V (ZMod 2)) := by
  simp only [pointPoly, Finset.prod_ite]
  congr 1
  rw [xMon]
  apply Finset.prod_congr
  · ext i; simp
  · intro i _; rfl

theorem support_mul_xMon_degree {V : Type} [Fintype V] [DecidableEq V]
    (S : Finset V) (p : MvPolynomial V (ZMod 2))
    (s : V →₀ ℕ) (hs : s ∈ (xMon S * p).support) : S.card ≤ s.sum (fun _ e => e) := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp (support_mul (xMon S) p hs)
  have haeq : a = Finsupp.indicator S (fun _ _ => (1 : ℕ)) := by
    rw [xMon_eq_monomial] at ha
    exact Finset.mem_singleton.mp (support_monomial_subset ha)
  subst a
  have hsum : (Finsupp.indicator S (fun _ _ => (1 : ℕ))).sum (fun _ e => e) = S.card := by
    simp only [Finsupp.sum, indicator_support]
    have heq : (∑ i ∈ S, (Finsupp.indicator S (fun _ _ => (1 : ℕ))) i) = ∑ _i ∈ S, 1 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finsupp.indicator_apply, hi]
    rw [heq]; simp
  rw [← hab]
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), hsum]
  omega

theorem majOne_support_heavy (ℓ : ℕ) (s : Fin ℓ →₀ ℕ)
    (hs : s ∈ (majOne ℓ).support) : ℓ / 2 < s.sum (fun _ e => e) := by
  classical
  unfold majOne at hs
  obtain ⟨S, hS, hsS⟩ := Finset.mem_biUnion.mp (support_sum hs)
  have hheavy := (Finset.mem_filter.mp hS).2
  change s ∈ (pointPoly S).support at hsS
  rw [pointPoly_factor] at hsS
  exact lt_of_lt_of_le hheavy (support_mul_xMon_degree S _ s hsS)

end AC02Frege.P2MMajorityFoundation
end

section
-- Inlined Solutions.P2MBooleanBasis

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MMajorityFoundation

namespace AC02Frege.P2MBooleanBasis

theorem squarefree_eq_indicator {V : Type*} (s : V →₀ ℕ) (hs : ∀ i, s i ≤ 1) :
    s = Finsupp.indicator s.support (fun _ _ => 1) := by
  classical
  ext i
  by_cases hi : i ∈ s.support
  · simp only [Finsupp.indicator_apply, dif_pos hi]
    have hpos := Finsupp.mem_support_iff.mp hi
    exact Nat.le_antisymm (hs i) (by omega)
  · simpa only [Finsupp.indicator_apply, dif_neg hi] using (by simpa only [Finsupp.mem_support_iff, not_not] using hi : s i = 0)

theorem squarefree_monomial {V : Type*} (s : V →₀ ℕ) (c : ZMod 2)
    (hs : ∀ i, s i ≤ 1) : monomial s c = c • xMon s.support := by
  rw [xMon_eq_monomial, smul_monomial, smul_eq_mul, mul_one,
    ← squarefree_eq_indicator s hs]

theorem squarefree_sum {V : Type*} (s : V →₀ ℕ) (hs : ∀ i, s i ≤ 1) :
    s.sum (fun _ e => e) = s.support.card := by
  have heq := squarefree_monomial s (1 : ZMod 2) hs
  have hd := congrArg MvPolynomial.totalDegree heq
  simpa only [totalDegree_monomial _ one_ne_zero, one_smul, xMon_totalDegree] using hd

noncomputable def monomialSpan {V : Type*} (P : Finset V → Prop) :
    Submodule (ZMod 2) (MvPolynomial V (ZMod 2)) :=
  Submodule.span (ZMod 2) {p | ∃ S : Finset V, P S ∧ p = xMon S}

theorem mem_monomialSpan_iff {V : Type*} (P : Finset V → Prop)
    (p : MvPolynomial V (ZMod 2)) : p ∈ monomialSpan P ↔
      IsMultilinear p ∧ ∀ s ∈ p.support, P s.support := by
  classical
  let M := restrictSupport (ZMod 2) {s : V →₀ ℕ | (∀ i, s i ≤ 1) ∧ P s.support}
  have heq : monomialSpan P = M := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro q ⟨S, hS, rfl⟩
      rw [xMon_eq_monomial]
      apply (monomial_mem_restrictSupport (ZMod 2)).mpr
      left
      refine ⟨?_, ?_⟩
      · intro i
        simp only [Finsupp.indicator_apply]
        split_ifs <;> omega
      · simpa only [indicator_support] using hS
    · intro q hq
      have hq' : ∀ s ∈ q.support, (∀ i, s i ≤ 1) ∧ P s.support := hq
      rw [q.as_sum]
      apply Submodule.sum_mem
      intro s hs
      obtain ⟨hml, hP⟩ := hq' s hs
      rw [squarefree_monomial s _ hml]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s.support, hP, rfl⟩)
  rw [heq, mem_restrictSupport_iff (ZMod 2)]
  constructor
  · intro hp
    exact ⟨fun s hs i => (hp hs).1 i, fun s hs => (hp hs).2⟩
  · rintro ⟨hml, hP⟩ s hs
    exact ⟨hml s hs, hP s hs⟩

theorem mem_light_iff {V : Type*} (m : ℕ) (p : MvPolynomial V (ZMod 2)) :
    p ∈ monomialSpan (fun S : Finset V => S.card ≤ m) ↔
      IsMultilinear p ∧ p.totalDegree ≤ m := by
  rw [mem_monomialSpan_iff]
  constructor
  · rintro ⟨hp, hP⟩
    refine ⟨hp, Finset.sup_le fun s hs => ?_⟩
    rw [squarefree_sum s (hp s hs)]
    exact hP s hs
  · rintro ⟨hp, hd⟩
    refine ⟨hp, fun s hs => ?_⟩
    rw [← squarefree_sum s (hp s hs)]
    exact (le_totalDegree hs).trans hd

theorem point_interpolation {V : Type} [Fintype V] [DecidableEq V]
    (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p) :
    p = ∑ S : Finset V, eval (fun i => if i ∈ S then (1 : ZMod 2) else 0) p • pointPoly S := by
  apply multilinear_ext hp
    (multilinear_sum _ _ (fun S _ =>
      (mem_restrictDegree V _ 1).mp ((restrictDegree V (ZMod 2) 1).smul_mem _
        ((mem_restrictDegree V _ 1).mpr (pointPoly_multilinear S)))))
  intro x
  simp only [map_sum, smul_eval, pointPoly_eval]
  have heq (S : Finset V) :
      x = (fun i => if i ∈ S then (1 : ZMod 2) else 0) ↔
        S = Finset.univ.filter (fun i => x i = 1) := by
    constructor
    · intro h; rw [h, ones_of_point]
    · intro h; subst S; exact (point_of_ones x).symm
  simp only [heq]
  simp
  have hx : (fun i => if x i = 1 then (1 : ZMod 2) else 0) = x := by
    funext i
    rcases eq_zero_or_one (x i) with hi | hi <;> simp [hi]
  rw [hx]

end AC02Frege.P2MBooleanBasis
end

section
-- Inlined Solutions.P2MBooleanFlip

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MMajorityFoundation AC02Frege.P2MBooleanBasis

namespace AC02Frege.P2MBooleanFlip

theorem ml_totalDegree_le {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    (ML p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, ml_monomial]
  apply totalDegree_finsetSum_le
  intro s hs
  apply (totalDegree_monomial_le _ _).trans
  apply le_trans ?_ (le_totalDegree hs)
  simp only [Finsupp.sum, sqfree_support]
  apply Finset.sum_le_sum
  intro i _
  simp only [sqfree, Finsupp.mapRange_apply]
  exact min_le_left _ _

theorem bind_linear_totalDegree_le {V W : Type*} (f : V → MvPolynomial W (ZMod 2))
    (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial V (ZMod 2)) :
    (bind₁ f p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, bind₁_monomial]
  apply totalDegree_finsetSum_le
  intro s hs
  apply le_trans (totalDegree_mul _ _)
  simp only [totalDegree_C, zero_add]
  apply (totalDegree_finsetProd _ _).trans
  apply le_trans ?_ (le_totalDegree hs)
  apply Finset.sum_le_sum
  intro i _
  exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (s i) (hf i))

noncomputable def flip {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    MvPolynomial V (ZMod 2) := ML (bind₁ (fun i => 1 + X i) p)

theorem flip_multilinear {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    IsMultilinear (flip p) := ml_multilinear _

theorem flip_degree_le {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    (flip p).totalDegree ≤ p.totalDegree := by
  apply (ml_totalDegree_le _).trans
  apply bind_linear_totalDegree_le
  intro i
  exact (totalDegree_add _ _).trans (by simp)

theorem flip_eval {V : Type*} (p : MvPolynomial V (ZMod 2)) (x : V → ZMod 2) :
    eval x (flip p) = eval (fun i => 1 + x i) p := by
  rw [flip, eval_ml]
  simp only [eval, eval₂Hom_bind₁, map_add, map_one, eval₂Hom_X']

theorem flip_involution {V : Type} [Finite V] (p : MvPolynomial V (ZMod 2))
    (hp : IsMultilinear p) : flip (flip p) = p := by
  apply multilinear_ext (flip_multilinear _) hp
  intro x
  simp only [flip_eval, CharTwo.add_cancel_left]

end AC02Frege.P2MBooleanFlip
end

section
-- Inlined Solutions.P2MBooleanPC

open MvPolynomial AC02Frege
open AC02Frege.P2MSupport AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip

namespace SemAC02.P2MBooleanPC

def Derivable {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) : Prop :=
  p = 0 ∨ ∃ π : List (MvPolynomial (Fin n) (ZMod 2)),
    PCNonBool.IsDerivation ML P π ∧ (∀ q ∈ π, q.totalDegree ≤ D) ∧ p ∈ π

theorem pc_zero {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ) :
    Derivable P D 0 := Or.inl rfl

theorem pc_degree {n : ℕ} {P : Set (MvPolynomial (Fin n) (ZMod 2))} {D : ℕ}
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p) : p.totalDegree ≤ D := by
  rcases hp with rfl | ⟨π, _, hdeg, hp⟩
  · simp
  · exact hdeg p hp

theorem pc_smul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p) (c : ZMod 2) :
    Derivable P D (c • p) := by
  rcases hp with rfl | ⟨π, hπ, hdeg, hp⟩
  · simp only [smul_zero]; exact pc_zero P D
  · obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
    refine Or.inr ⟨π ++ [c • p], ?_, ?_, by simp⟩
    · apply derivation_snoc _ _ hπ
      right; left
      exact ⟨i, i, hi, hi, c, 0, by simp only [hpi, zero_smul, add_zero]⟩
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hdeg q hq
      · have heq : q = c • p := List.mem_singleton.mp hq
        subst q
        exact (totalDegree_smul_le c p).trans (hdeg p hp)

theorem pc_add {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    {p q : MvPolynomial (Fin n) (ZMod 2)}
    (hp : Derivable P D p) (hq : Derivable P D q) :
    Derivable P D (p + q) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simpa only [zero_add] using hq
  rcases hq with rfl | ⟨ρ, hρ, hρdeg, hq⟩
  · simpa only [add_zero] using (show Derivable P D p from Or.inr ⟨π, hπ, hπdeg, hp⟩)
  have hboth := derivation_append _ _ hπ hρ
  have hp' : p ∈ π ++ ρ := List.mem_append_left _ hp
  have hq' : q ∈ π ++ ρ := List.mem_append_right _ hq
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp'
  obtain ⟨j, hj, hqj⟩ := List.mem_iff_getElem.mp hq'
  refine Or.inr ⟨(π ++ ρ) ++ [p + q], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hboth
    right; left
    exact ⟨i, j, hi, hj, 1, 1, by simp only [hpi, hqj, one_smul]⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact hπdeg r hr
      · exact hρdeg r hr
    · have heq : r = p + q := List.mem_singleton.mp hr
      subst r
      exact (totalDegree_add p q).trans (max_le (hπdeg p hp) (hρdeg q hq))

theorem pc_mul_X {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p)
    (v : Fin n) (hdeg : p.totalDegree + 1 ≤ D) :
    Derivable P D (ML (X v * p)) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simp only [mul_zero, map_zero]; exact pc_zero P D
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [ML (X v * p)], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; right
    exact ⟨i, hi, v, by rw [hpi]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hπdeg q hq
    · have heq : q = ML (X v * p) := List.mem_singleton.mp hq
      subst q
      exact (ml_totalDegree_le _).trans ((totalDegree_mul (X v) p).trans (by simpa only [totalDegree_X, Nat.add_comm] using hdeg))

theorem pc_axiom {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : p ∈ P)
    (hdeg : (ML p).totalDegree ≤ D) : Derivable P D (ML p) := by
  refine Or.inr ⟨[ML p], ?_, by simpa using hdeg, by simp⟩
  intro k hk
  have heq : k = 0 := by simpa using hk
  subst k
  left
  exact ⟨p, hp, 1, by simp⟩

theorem pc_mono {n : ℕ} {P : Set (MvPolynomial (Fin n) (ZMod 2))} {D E : ℕ}
    (hDE : D ≤ E) {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P D p) :
    Derivable P E p := by
  rcases hp with h | ⟨π, hπ, hdeg, hp⟩
  · exact Or.inl h
  · exact Or.inr ⟨π, hπ, fun q hq => (hdeg q hq).trans hDE, hp⟩

noncomputable def consequenceSpace {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (D : ℕ) :
    Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)) where
  carrier := {p | Derivable P D p}
  zero_mem' := pc_zero P D
  add_mem' := pc_add P D
  smul_mem' := fun a _ hp => pc_smul P D hp a

end SemAC02.P2MBooleanPC
end

section
-- Inlined Solutions.P2MRelativePC

open MvPolynomial AC02Frege SemAC02
open AC02Frege.P2MSupport AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip

namespace SemAC02.P2MRelativePC

def Derivable {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (p : MvPolynomial (Fin n) (ZMod 2)) : Prop :=
  p = 0 ∨ ∃ π : List (MvPolynomial (Fin n) (ZMod 2)),
    PCNonBool.IsDerivation ML P π ∧ (∀ q ∈ π, q ∈ U) ∧ p ∈ π

theorem pc_zero {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))) : Derivable P U 0 := Or.inl rfl

theorem pc_mem {n : ℕ} {P : Set (MvPolynomial (Fin n) (ZMod 2))}
    {U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))}
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) : p ∈ U := by
  rcases hp with rfl | ⟨π,_,hmem,hp⟩
  · exact U.zero_mem
  · exact hmem p hp

theorem pc_smul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) (c : ZMod 2) :
    Derivable P U (c • p) := by
  rcases hp with rfl | ⟨π,hπ,hmem,hp⟩
  · simp only [smul_zero]; exact pc_zero P U
  obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [c • p], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; left
    exact ⟨i,i,hi,hi,c,0,by simp only [hpi,zero_smul,add_zero]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hmem q hq
    · have he : q = c • p := List.mem_singleton.mp hq
      rw [he]
      exact U.smul_mem c (hmem p hp)

theorem pc_add {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    {p q : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) (hq : Derivable P U q) :
    Derivable P U (p+q) := by
  rcases hp with rfl | ⟨π,hπ,hπmem,hp⟩
  · simpa only [zero_add] using hq
  rcases hq with rfl | ⟨ρ,hρ,hρmem,hq⟩
  · simpa only [add_zero] using (show Derivable P U p from Or.inr ⟨π,hπ,hπmem,hp⟩)
  have hboth := derivation_append _ _ hπ hρ
  have hp' : p ∈ π ++ ρ := List.mem_append_left _ hp
  have hq' : q ∈ π ++ ρ := List.mem_append_right _ hq
  obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp'
  obtain ⟨j,hj,hqj⟩ := List.mem_iff_getElem.mp hq'
  refine Or.inr ⟨(π ++ ρ) ++ [p+q], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hboth
    right; left
    exact ⟨i,j,hi,hj,1,1,by simp only [hpi,hqj,one_smul]⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact hπmem r hr
      · exact hρmem r hr
    · have he : r = p+q := List.mem_singleton.mp hr
      rw [he]
      exact U.add_mem (hπmem p hp) (hρmem q hq)

theorem pc_mul_X {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : Derivable P U p) (v : Fin n)
    (hmem : ML (X v * p) ∈ U) : Derivable P U (ML (X v * p)) := by
  rcases hp with rfl | ⟨π,hπ,hπmem,hp⟩
  · simp only [mul_zero,map_zero]; exact pc_zero P U
  obtain ⟨i,hi,hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [ML (X v * p)], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; right
    exact ⟨i,hi,v,by rw [hpi]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hπmem q hq
    · rwa [List.mem_singleton.mp hq]

theorem pc_axiom {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : p ∈ P) (hmem : ML p ∈ U) :
    Derivable P U (ML p) := by
  refine Or.inr ⟨[ML p], ?_, by simpa using hmem, by simp⟩
  intro k hk
  have he : k = 0 := by simpa using hk
  subst k
  left
  exact ⟨p,hp,1,by simp⟩

end SemAC02.P2MRelativePC
end

section
-- Inlined Solutions.RelativePCPolynomialMultiplication

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip

namespace SemAC02.P2MRelativePC

theorem pc_polynomial_mul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (U : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (u v : MvPolynomial (Fin n) (ZMod 2)) (hu : Derivable P U u) (huml : IsMultilinear u)
    (hmem : ∀ w : MvPolynomial (Fin n) (ZMod 2), w.totalDegree ≤ v.totalDegree → ML (u*w) ∈ U) :
    Derivable P U (ML (u*v)) := by
  classical
  induction v using MvPolynomial.induction_on'' with
  | C c =>
    have he : u * C c = c • u := by rw [smul_eq_C_mul, mul_comm]
    rw [he, map_smul, ml_of_multilinear u huml]
    exact pc_smul P U hu c
  | monomial_add s c p hnot hc ihp ihm =>
    have hdis : Disjoint (monomial s c).support p.support := by
      apply disjoint_support_monomial
      · exact hnot
      · exact hc
    have hsupp : (monomial s c + p).support = (monomial s c).support ∪ p.support := by
      exact Finsupp.support_add_eq hdis
    have hdm : (monomial s c).totalDegree ≤ (monomial s c + p).totalDegree := by
      apply totalDegree_le_of_support_subset
      rw [hsupp]
      exact Finset.subset_union_left
    have hdp : p.totalDegree ≤ (monomial s c + p).totalDegree := by
      apply totalDegree_le_of_support_subset
      rw [hsupp]
      exact Finset.subset_union_right
    rw [mul_add, map_add]
    exact pc_add P U (ihm (fun w hw => hmem w (hw.trans hdm)))
      (ihp (fun w hw => hmem w (hw.trans hdp)))
  | mul_X p i ih =>
    have hle : p.totalDegree ≤ (p * X i).totalDegree := by
      by_cases hp : p = 0
      · simp [hp]
      · rw [totalDegree_mul_of_isDomain hp (X_ne_zero i), totalDegree_X]
        omega
    have hi := ih (fun w hw => hmem w (hw.trans hle))
    have he : ML (u * (p * X i)) = ML (X i * ML (u*p)) := by
      rw [ml_mul_right]
      congr 1
      ring
    rw [he]
    apply pc_mul_X P U hi i
    rw [← he]
    exact hmem _ le_rfl

end SemAC02.P2MRelativePC
end

section
-- Inlined Solutions.P2MBooleanLocality

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis

namespace SemAC02.P2MBooleanLocality

theorem multilinear_degree_le_card {V : Type} [Fintype V]
    (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p) : p.totalDegree ≤ Fintype.card V := by
  classical
  apply Finset.sup_le
  intro s hs
  rw [squarefree_sum s (hp s hs)]
  exact Finset.card_le_univ _

noncomputable def extendAssignment {V : Type} (J : Finset V) (x : J → ZMod 2) : V → Bool := by
  classical
  exact fun i => if hi : i ∈ J then decide (x ⟨i, hi⟩ = 1) else false

theorem represents_local_function {V : Type} [Fintype V] (J : Finset V)
    (f : (V → Bool) → ZMod 2)
    (hf : ∀ z z' : V → Bool, (∀ i ∈ J, z i = z' i) → f z = f z') :
    ∃ r : MvPolynomial V (ZMod 2), r.totalDegree ≤ J.card ∧
      ∀ z : V → Bool, eval (toF2 z) r = f z := by
  classical
  let η : (J → ZMod 2) → ZMod 2 := fun x => f (extendAssignment J x)
  obtain ⟨p, hp⟩ := LinearMap.range_eq_top.mp (MvPolynomial.range_evalᵢ J (ZMod 2)) η
  let p' : restrictDegree J (ZMod 2) (Fintype.card (ZMod 2) - 1) := p
  have hml : IsMultilinear p'.1 := by
    apply (mem_restrictDegree J _ 1).mp
    simpa only [ZMod.card, Nat.reduceSub] using p'.2
  refine ⟨rename Subtype.val p'.1, ?_, ?_⟩
  · apply (totalDegree_rename_le _ _).trans
    simpa only [Fintype.card_coe] using multilinear_degree_le_card p'.1 hml
  · intro z
    rw [eval_rename]
    have he := congrFun hp (fun j : J => toF2 z j.1)
    change eval (fun j : J => toF2 z j.1) p'.1 = f (extendAssignment J (fun j : J => toF2 z j.1)) at he
    change eval (fun j : J => toF2 z j.1) p'.1 = f z
    rw [he]
    apply hf
    intro i hi
    simp only [extendAssignment, dif_pos hi]
    cases h : z i <;> simp [toF2, h]

end SemAC02.P2MBooleanLocality
end

section
-- Inlined Solutions.P2MBooleanRestrictions

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MMajorityFoundation
open AC02Frege.P2MBooleanBasis AC02Frege.P2MBooleanFlip

namespace AC02Frege.P2MBooleanRestrictions

theorem xMon_eval_point {V : Type*} [DecidableEq V] (S T : Finset V) :
    eval (fun i => if i ∈ T then (1 : ZMod 2) else 0) (xMon S) =
      if S ⊆ T then 1 else 0 := by
  classical
  rw [xMon_eval]
  by_cases h : S ⊆ T
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    simp [h hi]
  · rw [if_neg h]
    obtain ⟨i, hi, hit⟩ := Finset.not_subset.mp h
    exact Finset.prod_eq_zero hi (by simp [hit])

theorem multilinear_exponent_ext {V : Type*} (s t : V →₀ ℕ)
    (hs : ∀ i, s i ≤ 1) (ht : ∀ i, t i ≤ 1) (hst : s.support = t.support) : s = t := by
  rw [squarefree_eq_indicator s hs, squarefree_eq_indicator t ht, hst]

theorem eq_zero_of_support_point_eval_zero {V : Type} [DecidableEq V]
    (p : MvPolynomial V (ZMod 2)) (hp : IsMultilinear p)
    (hv : ∀ s ∈ p.support,
      eval (fun i => if i ∈ s.support then (1 : ZMod 2) else 0) p = 0) : p = 0 := by
  classical
  by_contra hne
  obtain ⟨s, hs, hmin⟩ := p.support.exists_min_image
    (fun t => t.support.card) (support_nonempty.mpr hne)
  have heval : eval (fun i => if i ∈ s.support then (1 : ZMod 2) else 0) p = p.coeff s := by
    have hsum : eval (fun i => if i ∈ s.support then (1 : ZMod 2) else 0) p =
        ∑ t ∈ p.support, p.coeff t * (if t.support ⊆ s.support then (1 : ZMod 2) else 0) := by
      conv_lhs => rw [p.as_sum]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [squarefree_monomial t _ (hp t ht), smul_eval, xMon_eval_point]
    rw [hsum, Finset.sum_eq_single s]
    · simp
    · intro t ht hts
      have hnot : ¬ t.support ⊆ s.support := by
        intro hsub
        have heq : t.support = s.support := Finset.eq_of_subset_of_card_le hsub (hmin t ht)
        exact hts (multilinear_exponent_ext t s (hp t ht) (hp s hs) heq)
      rw [if_neg hnot, mul_zero]
    · intro hnot
      exact False.elim (hnot hs)
  have hz := hv s hs
  rw [heval] at hz
  exact (mem_support_iff.mp hs) hz

theorem eval_injective_on_monomialSpan {V : Type} [DecidableEq V]
    (P : Finset V → Prop) (p : MvPolynomial V (ZMod 2))
    (hp : p ∈ monomialSpan P)
    (hv : ∀ S : Finset V, P S →
      eval (fun i => if i ∈ S then (1 : ZMod 2) else 0) p = 0) : p = 0 := by
  obtain ⟨hml, hP⟩ := (mem_monomialSpan_iff P p).mp hp
  exact eq_zero_of_support_point_eval_zero p hml (fun s hs => hv s.support (hP s hs))

theorem ml_vars_subset {V : Type} (p : MvPolynomial V (ZMod 2)) :
    (ML p).vars ⊆ p.vars := by
  classical
  intro i hi
  obtain ⟨s, hs, his⟩ := (mem_vars_iff_mem_support i).mp hi
  have hexp : ML p = ∑ t ∈ p.support, monomial (sqfree t) (p.coeff t) := by
    conv_lhs => rw [p.as_sum]
    simp only [map_sum, ml_monomial]
  rw [hexp] at hs
  obtain ⟨t, ht, hst⟩ := Finset.mem_biUnion.mp (support_sum hs)
  have heq := Finset.mem_singleton.mp (support_monomial_subset hst)
  subst s
  rw [sqfree_support] at his
  exact (mem_vars_iff_mem_support i).mpr ⟨t, ht, his⟩

theorem flip_vars_subset {V : Type} (p : MvPolynomial V (ZMod 2)) :
    (P2MBooleanFlip.flip p).vars ⊆ p.vars := by
  classical
  intro i hi
  obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp
    (vars_bind₁ (fun j => 1 + X j) p (ml_vars_subset _ hi))
  have hsub : (1 + X j : MvPolynomial V (ZMod 2)).vars ⊆ {j} := by
    simpa using vars_add_subset (1 : MvPolynomial V (ZMod 2)) (X j)
  have heq := Finset.mem_singleton.mp (hsub hij)
  simpa only [heq] using hj

noncomputable def complementMap {V : Type} :
    MvPolynomial V (ZMod 2) →ₗ[ZMod 2] MvPolynomial V (ZMod 2) where
  toFun := P2MBooleanFlip.flip
  map_add' p q := by simp only [P2MBooleanFlip.flip, map_add]
  map_smul' c p := by simp only [P2MBooleanFlip.flip, map_smul, RingHom.id_apply]

theorem flip_mem_monomialSpan {V : Type} (P : Finset V → Prop)
    (hP : ∀ S T, T ⊆ S → P S → P T)
    (p : MvPolynomial V (ZMod 2)) (hp : p ∈ monomialSpan P) :
    P2MBooleanFlip.flip p ∈ monomialSpan P := by
  classical
  have hle : monomialSpan P ≤ (monomialSpan P).comap complementMap := by
    apply Submodule.span_le.mpr
    rintro q ⟨S, hS, rfl⟩
    apply (mem_monomialSpan_iff P _).mpr
    refine ⟨flip_multilinear _, ?_⟩
    intro s hs
    have hsub : s.support ⊆ S := by
      apply (support_subset_vars_of_mem_support hs).trans
      apply (flip_vars_subset _).trans
      rw [xMon_eq_monomial, vars_monomial one_ne_zero, indicator_support]
    exact hP S s.support hsub hS
  exact hle hp

theorem monomialSpan_span_range {V : Type} (P : Finset V → Prop) :
    monomialSpan P = Submodule.span (ZMod 2)
      (Set.range (fun S : {S : Finset V // P S} => xMon S.1)) := by
  apply congrArg (Submodule.span (ZMod 2))
  ext p
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact ⟨⟨S, hS⟩, rfl⟩
  · rintro ⟨S, rfl⟩
    exact ⟨S.1, S.2, rfl⟩

end AC02Frege.P2MBooleanRestrictions
end

section
-- Inlined Solutions.P2MCommonBasis

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MMajorityFoundation
open AC02Frege.P2MBooleanBasis AC02Frege.P2MBooleanFlip AC02Frege.P2MBooleanRestrictions

namespace SemAC02.P2MCommonBasis

def ones {m : ℕ} (X : Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter (fun i => X i = true)

theorem indicator_ones {m : ℕ} (X : Fin m → Bool) : indicatorVec (ones X) = X := by
  funext i
  cases h : X i <;> simp [indicatorVec, ones, h]

theorem ones_indicator {m : ℕ} (S : Finset (Fin m)) : ones (indicatorVec S) = S := by
  ext i
  simp [indicatorVec, ones]

theorem toF2_indicator {m : ℕ} (S : Finset (Fin m)) :
    toF2 (indicatorVec S) = fun i => if i ∈ S then (1 : ZMod 2) else 0 := by
  funext i
  simp [toF2, indicatorVec]

theorem flip_eval_bool {m : ℕ} (p : MvPolynomial (Fin m) (ZMod 2)) (X : Fin m → Bool) :
    eval (toF2 X) (P2MBooleanFlip.flip p) = eval (toF2 (fun i => !X i)) p := by
  rw [flip_eval]
  have heq : (fun i => 1 + toF2 X i) = toF2 (fun i => !X i) := by
    funext i
    cases h : X i <;> simp [toF2, h, CharTwo.add_self_eq_zero]
  rw [heq]

noncomputable def supportEquiv (m : ℕ) (g : (Fin m → Bool) → Bool) :
    {S : Finset (Fin m) // g (indicatorVec S) = true} ≃
      {X : Fin m → Bool // g X = true} where
  toFun S := ⟨indicatorVec S.1, S.2⟩
  invFun X := ⟨ones X.1, by simpa only [indicator_ones] using X.2⟩
  left_inv S := Subtype.ext (ones_indicator S.1)
  right_inv X := Subtype.ext (indicator_ones X.1)

def complementEquiv (m : ℕ) (g : (Fin m → Bool) → Bool) :
    {X : Fin m → Bool // g X = true} ≃
      {X : Fin m → Bool // g (fun i => !X i) = true} where
  toFun X := ⟨fun i => !X.1 i, by simpa only [Bool.not_not] using X.2⟩
  invFun X := ⟨fun i => !X.1 i, X.2⟩
  left_inv X := Subtype.ext (by funext i; simp)
  right_inv X := Subtype.ext (by funext i; simp)

noncomputable def restriction {m : ℕ} (Ω : Set (Fin m → Bool)) :
    MvPolynomial (Fin m) (ZMod 2) →ₗ[ZMod 2] (Ω → ZMod 2) where
  toFun p X := eval (toF2 X.1) p
  map_add' p q := by ext X; simp
  map_smul' c p := by ext X; simp

theorem downclosed {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g) :
    ∀ S T : Finset (Fin m), T ⊆ S → g (indicatorVec S) = true →
      g (indicatorVec T) = true := by
  intro S T hTS hS
  have hle : indicatorVec T ≤ indicatorVec S := by
    intro i
    by_cases hi : i ∈ T
    · simp [indicatorVec, hi, hTS hi]
    · simp [indicatorVec, hi]
  have h := hg hle
  rw [hS] at h
  exact Bool.eq_true_of_true_le h

theorem restriction_zero (m : ℕ) (g : (Fin m → Bool) → Bool)
    (p : MvPolynomial (Fin m) (ZMod 2))
    (hp : p ∈ monomialSpan (fun S : Finset (Fin m) => g (indicatorVec S) = true))
    (hv : restriction {X : Fin m → Bool | g X = true} p = 0) : p = 0 := by
  apply eval_injective_on_monomialSpan _ p hp
  intro S hS
  have h := congrFun hv ⟨indicatorVec S, hS⟩
  change eval (toF2 (indicatorVec S)) p = 0 at h
  simpa only [toF2_indicator] using h

theorem restriction_complement_zero (m : ℕ) (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p : MvPolynomial (Fin m) (ZMod 2))
    (hp : p ∈ monomialSpan (fun S : Finset (Fin m) => g (indicatorVec S) = true))
    (hv : restriction {X : Fin m → Bool | g (fun i => !X i) = true} p = 0) : p = 0 := by
  have hf : P2MBooleanFlip.flip p ∈ monomialSpan (fun S : Finset (Fin m) => g (indicatorVec S) = true) :=
    flip_mem_monomialSpan _ (downclosed g hg) p hp
  have hvan : restriction {X : Fin m → Bool | g X = true} (P2MBooleanFlip.flip p) = 0 := by
    funext X
    change eval (toF2 X.1) (P2MBooleanFlip.flip p) = 0
    rw [flip_eval_bool]
    have h := congrFun hv ⟨fun i => !X.1 i, by simpa only [Set.mem_ofPred_eq, Bool.not_not] using X.2⟩
    exact h
  have hz := restriction_zero m g _ hf hvan
  have hml := ((mem_monomialSpan_iff _ _).mp hp).1
  calc
    p = P2MBooleanFlip.flip (P2MBooleanFlip.flip p) := (flip_involution p hml).symm
    _ = P2MBooleanFlip.flip 0 := congrArg (P2MBooleanFlip.flip (V := Fin m)) hz
    _ = 0 := by simp [P2MBooleanFlip.flip]

theorem restriction_independent (m : ℕ) (P : Finset (Fin m) → Prop) (Ω : Set (Fin m → Bool))
    (hinj : ∀ p : MvPolynomial (Fin m) (ZMod 2), p ∈ monomialSpan P → restriction Ω p = 0 → p = 0) :
    LinearIndependent (ZMod 2) (fun S : {S : Finset (Fin m) // P S} => restriction Ω (xMon S.1)) := by
  apply (xMon_linearIndependent.comp Subtype.val Subtype.val_injective).map_injOn
  intro v hv w hw heq
  have hv' : v ∈ monomialSpan P := by rwa [monomialSpan_span_range]
  have hw' : w ∈ monomialSpan P := by rwa [monomialSpan_span_range]
  apply sub_eq_zero.mp
  apply hinj (v - w) (Submodule.sub_mem _ hv' hw')
  rw [map_sub, heq, sub_self]

end SemAC02.P2MCommonBasis
end

section
-- Inlined Theorems.Thm_SemAC02_lemma_8_5_common_basis


open MvPolynomial AC02Frege SemAC02 SemAC02.P2MCommonBasis


/-- **Lemma 8.5 (Common monomial basis)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission), Lemma 8.5, p.64): with
`L = {S ⊆ [m] : g₀(1_S) = 1}`, `Ω₀ = {X : g₀(X) = 1}` and `Ω₁ = {X : g₁(X) = 1}`,
`g₁(X) = g₀(X̄)`, the monomials `x_S = ∏_{j∈S} x_j`, `S ∈ L`, give a basis of both `𝔽₂^{Ω₀}`
and `𝔽₂^{Ω₁}`.

**Formalization Note** Stated for every antitone Boolean function `g₀` on `{0,1}^m` (the
paper's `g₀ = g` from §8.1 is one). "Basis" is linear independence of the restrictions of the
`x_S` to `Ω_b` together with spanning all functions `Ω_b → 𝔽₂`. -/
theorem SemAC02.lemma_8_5_common_basis {m : ℕ} (g₀ : (Fin m → Bool) → Bool) (hg₀ : Antitone g₀) :
    (LinearIndependent (ZMod 2)
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ X = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1)) ∧
      Submodule.span (ZMod 2) (Set.range
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ X = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1))) = ⊤) ∧
    (LinearIndependent (ZMod 2)
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ (fun j => !X j) = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1)) ∧
      Submodule.span (ZMod 2) (Set.range
        (fun S : {S : Finset (Fin m) // g₀ (indicatorVec S) = true} =>
          fun X : {X : Fin m → Bool // g₀ (fun j => !X j) = true} =>
            MvPolynomial.eval (toF2 X.1) (AC02Frege.xMon S.1))) = ⊤) := by
  classical
  let P : Finset (Fin m) → Prop := fun S => g₀ (indicatorVec S) = true
  let Ω₀ : Set (Fin m → Bool) := {X | g₀ X = true}
  let Ω₁ : Set (Fin m → Bool) := {X | g₀ (fun i => !X i) = true}
  have hli0 : LinearIndependent (ZMod 2)
      (fun S : {S : Finset (Fin m) // P S} => restriction Ω₀ (xMon S.1)) :=
    restriction_independent m P Ω₀ (restriction_zero m g₀)
  have hli1 : LinearIndependent (ZMod 2)
      (fun S : {S : Finset (Fin m) // P S} => restriction Ω₁ (xMon S.1)) :=
    restriction_independent m P Ω₁ (restriction_complement_zero m g₀ hg₀)
  have hspan0 := hli0.span_eq_top_of_card_eq_finrank' (by
    rw [Module.finrank_fintype_fun_eq_card]
    exact Fintype.card_congr (supportEquiv m g₀))
  have hspan1 := hli1.span_eq_top_of_card_eq_finrank' (by
    rw [Module.finrank_fintype_fun_eq_card]
    exact Fintype.card_congr ((supportEquiv m g₀).trans (complementEquiv m g₀)))
  exact ⟨⟨hli0, hspan0⟩, ⟨hli1, hspan1⟩⟩

end

section
-- Inlined Solutions.ProductFunctionBasis

open Module
open scoped TensorProduct

namespace P2MProofComplexity

open PiTensorProduct

noncomputable def functionTensorEquiv
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (X : ι → Type*) [∀ i, Fintype (X i)] :
    (⨂[R] i, (X i → R)) ≃ₗ[R] (((i : ι) → X i) → R) := by
  classical
  exact (PiTensorProduct.congr (fun i => (Finsupp.linearEquivFunOnFinite R R (X i)).symm)) ≪≫ₗ
    (PiTensorProduct.ofFinsuppEquiv' (R := R) (κ := X)) ≪≫ₗ
    Finsupp.linearEquivFunOnFinite R R ((i : ι) → X i)

@[simp] theorem functionTensorEquiv_tprod
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (X : ι → Type*) [∀ i, Fintype (X i)] (f : (i : ι) → X i → R) (x : (i : ι) → X i) :
    functionTensorEquiv X (⨂ₜ[R] i, f i) x = ∏ i, f i (x i) := by
  classical
  simp [functionTensorEquiv]

noncomputable def productFunctionBasis
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] {κ : ι → Type*}
    (b : (i : ι) → Basis (κ i) R (X i → R)) :
    Basis ((i : ι) → κ i) R (((i : ι) → X i) → R) :=
  (Basis.piTensorProduct b).map (functionTensorEquiv X)

@[simp] theorem productFunctionBasis_apply
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] {κ : ι → Type*}
    (b : (i : ι) → Basis (κ i) R (X i → R)) (k : (i : ι) → κ i) (x : (i : ι) → X i) :
    productFunctionBasis b k x = ∏ i, b i (k i) (x i) := by
  classical
  simp [productFunctionBasis]

theorem productFunctionBasis_repr
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] {κ : ι → Type*}
    (b : (i : ι) → Basis (κ i) R (X i → R)) (f : (i : ι) → X i → R)
    (k : (i : ι) → κ i) :
    (productFunctionBasis b).repr (fun x => ∏ i, f i (x i)) k =
      ∏ i, (b i).repr (f i) (k i) := by
  classical
  have hfun : (fun x => ∏ i, f i (x i)) = functionTensorEquiv X (⨂ₜ[R] i, f i) := by
    funext x
    exact (functionTensorEquiv_tprod X f x).symm
  rw [hfun]
  change (Basis.piTensorProduct b).repr
    ((functionTensorEquiv X).symm (functionTensorEquiv X (⨂ₜ[R] i, f i))) k = _
  rw [LinearEquiv.symm_apply_apply]
  exact Basis.piTensorProduct_repr_tprod_apply b f k

end P2MProofComplexity
end

section
-- Inlined Solutions.SemanticFibreBasis

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra

namespace SemAC02.P2MFibreBasis

abbrev BlockIndex {m : ℕ} (g : (Fin m → Bool) → Bool) :=
  {S : Finset (Fin m) // g (indicatorVec S) = true}

abbrev BlockFibre {m : ℕ} (g : (Fin m → Bool) → Bool) (b : Bool) :=
  {X : Fin m → Bool // if b then g (fun j => !X j) = true else g X = true}

noncomputable def blockBasis {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g) (b : Bool) :
    Basis (BlockIndex g) (ZMod 2) (BlockFibre g b → ZMod 2) := by
  have h := lemma_8_5_common_basis g hg
  cases b with
  | false => exact Basis.mk h.1.1 h.1.2.ge
  | true => exact Basis.mk h.2.1 h.2.2.ge

@[simp] theorem blockBasis_apply {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (b : Bool) (S : BlockIndex g) (X : BlockFibre g b) :
    blockBasis g hg b S X = eval (toF2 X.1) (xMon S.1) := by
  cases b <;> simp [blockBasis, Basis.mk_apply]

abbrev GlobalIndex {m : ℕ} (g : (Fin m → Bool) → Bool) (n : ℕ) :=
  {A : Finset (Fin n × Fin m) // IsLnSupport g A}

def assemble {n m : ℕ} {g : (Fin m → Bool) → Bool} (S : Fin n → BlockIndex g) :
    Finset (Fin n × Fin m) := Finset.univ.filter (fun v => v.2 ∈ (S v.1).1)

@[simp] theorem section_assemble {n m : ℕ} {g : (Fin m → Bool) → Bool}
    (S : Fin n → BlockIndex g) (i : Fin n) : blockSection (assemble S) i = (S i).1 := by
  ext j
  simp [blockSection, assemble]

def sections {n m : ℕ} {g : (Fin m → Bool) → Bool} (A : GlobalIndex g n) (i : Fin n) :
    BlockIndex g := ⟨blockSection A.1 i, A.2 i⟩

@[simp] theorem assemble_sections {n m : ℕ} {g : (Fin m → Bool) → Bool}
    (A : GlobalIndex g n) : assemble (sections A) = A.1 := by
  ext v
  simp [assemble, sections, blockSection]

def indexEquiv (n : ℕ) {m : ℕ} (g : (Fin m → Bool) → Bool) :
    (Fin n → BlockIndex g) ≃ GlobalIndex g n where
  toFun S := ⟨assemble S, by
    intro i
    rw [section_assemble]
    exact (S i).2⟩
  invFun A := sections A
  left_inv S := by funext i; apply Subtype.ext; exact section_assemble S i
  right_inv A := Subtype.ext (assemble_sections A)

abbrev Fibre {n m : ℕ} (g : (Fin m → Bool) → Bool) (z : Fin n → Bool) :=
  {X : Fin n × Fin m → Bool // InFiber g z X}

def curryEquiv {n m : ℕ} (g : (Fin m → Bool) → Bool) (z : Fin n → Bool) :
    Fibre g z ≃ ((i : Fin n) → BlockFibre g (z i)) where
  toFun X i := ⟨fun j => X.1 (i, j), X.2 i⟩
  invFun X := ⟨fun v => (X v.1).1 v.2, fun i => (X i).2⟩
  left_inv X := Subtype.ext (by funext v; rfl)
  right_inv X := by funext i; apply Subtype.ext; rfl

noncomputable def fibreBasis {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (z : Fin n → Bool) : Basis (GlobalIndex g n) (ZMod 2) (Fibre g z → ZMod 2) :=
  ((P2MProofComplexity.productFunctionBasis (fun i : Fin n => blockBasis g hg (z i))).reindex
    (indexEquiv n g)).map (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (curryEquiv g z))

theorem xMon_eval_blocks {n m : ℕ} (A : Finset (Fin n × Fin m))
    (X : Fin n × Fin m → Bool) : eval (toF2 X) (xMon A) =
      ∏ i : Fin n, eval (toF2 (fun j => X (i, j))) (xMon (blockSection A i)) := by
  classical
  simp only [xMon_eval, blockSection, Finset.prod_filter, toF2]
  rw [← Finset.prod_product']
  simp only [Finset.univ_product_univ]
  rw [← Finset.prod_filter]
  simp

@[simp] theorem fibreBasis_apply {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (z : Fin n → Bool) (A : GlobalIndex g n) (X : Fibre g z) :
    fibreBasis g hg z A X = eval (toF2 X.1) (xMon A.1) := by
  classical
  rw [fibreBasis, Basis.map_apply, Basis.reindex_apply]
  change P2MProofComplexity.productFunctionBasis (fun i : Fin n => blockBasis g hg (z i))
    (sections A) (curryEquiv g z X) = _
  rw [P2MProofComplexity.productFunctionBasis_apply, xMon_eval_blocks]
  apply Finset.prod_congr rfl
  intro i _
  rw [blockBasis_apply]
  rfl

end SemAC02.P2MFibreBasis
end

section
-- Inlined Solutions.SemanticFibreCoordinates

open Module MvPolynomial AC02Frege
open SemAC02 SemAC02.P2MFibreBasis

namespace SemAC02.P2MFibreCoordinates

noncomputable def coordinates {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) (z : Fin n → Bool) : ZMod 2 :=
  (fibreBasis g hg z).equivFun (fun X => eval (toF2 X.1) p) S

theorem coordinates_expansion {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (z : Fin n → Bool) (X : Fibre g z) :
    eval (toF2 X.1) p = ∑ S : GlobalIndex g n, coordinates g hg p S z *
      eval (toF2 X.1) (xMon S.1) := by
  classical
  have h := congrFun ((fibreBasis g hg z).equivFun.symm_apply_apply (fun X => eval (toF2 X.1) p)) X
  rw [Basis.equivFun_symm_apply] at h
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, fibreBasis_apply, coordinates] using h.symm

theorem coordinates_unique {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (c : GlobalIndex g n → (Fin n → Bool) → ZMod 2)
    (hc : ∀ (z : Fin n → Bool) (X : Fin n × Fin m → Bool), InFiber g z X →
      eval (toF2 X) p = ∑ S, c S z * eval (toF2 X) (xMon S.1)) :
    ∀ S z, c S z = coordinates g hg p S z := by
  classical
  intro S z
  have he : (fun X : Fibre g z => eval (toF2 X.1) p) =
      (fibreBasis g hg z).equivFun.symm (fun S => c S z) := by
    rw [Basis.equivFun_symm_apply]
    funext X
    rw [hc z X.1 X.2]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, fibreBasis_apply]
  have h := congrArg (fibreBasis g hg z).equivFun he
  rw [LinearEquiv.apply_symm_apply] at h
  exact (congrFun h S).symm

theorem coordinates_add {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p q : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) (z : Fin n → Bool) :
    coordinates g hg (p + q) S z = coordinates g hg p S z + coordinates g hg q S z := by
  have he : (fun X : Fibre g z => eval (toF2 X.1) (p + q)) =
      (fun X => eval (toF2 X.1) p) + (fun X => eval (toF2 X.1) q) := by
    funext X
    exact map_add _ _ _
  unfold coordinates
  rw [he, map_add]
  rfl

theorem coordinates_smul {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (a : ZMod 2) (p : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (S : GlobalIndex g n) (z : Fin n → Bool) :
    coordinates g hg (a • p) S z = a * coordinates g hg p S z := by
  have he : (fun X : Fibre g z => eval (toF2 X.1) (a • p)) =
      a • (fun X => eval (toF2 X.1) p) := by
    funext X
    simp only [smul_eval, Pi.smul_apply, smul_eq_mul]
  unfold coordinates
  rw [he, map_smul]
  rfl

end SemAC02.P2MFibreCoordinates
end

section
-- Inlined Solutions.SemanticProductCoordinates

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra
open SemAC02 SemAC02.P2MFibreBasis SemAC02.P2MFibreCoordinates

namespace SemAC02.P2MProductCoordinates

noncomputable def blockCoefficient {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : BlockIndex g) (U : Finset (Fin m)) (b : Bool) : ZMod 2 :=
  (blockBasis g hg b).repr (fun X => eval (toF2 X.1) (xMon T.1 * xMon U)) S

theorem blockCoefficient_empty {m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : BlockIndex g) (b : Bool) :
    blockCoefficient g hg S T ∅ b = if S = T then 1 else 0 := by
  classical
  have he : (fun X : BlockFibre g b => eval (toF2 X.1) (xMon T.1 * xMon ∅)) =
      blockBasis g hg b T := by
    funext X
    simp only [xMon, Finset.prod_empty, mul_one, blockBasis_apply]
  unfold blockCoefficient
  rw [he, Basis.repr_self]
  by_cases hST : S = T
  · subst S
    rw [Finsupp.single_eq_same, if_pos rfl]
  · rw [Finsupp.single_eq_of_ne hST, if_neg hST]

theorem coordinates_product {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (U : Finset (Fin n × Fin m)) (z : Fin n → Bool) :
    coordinates g hg (xMon T.1 * xMon U) S z =
      ∏ i : Fin n, blockCoefficient g hg (sections S i) (sections T i) (blockSection U i) (z i) := by
  have he : (fun X : Fibre g z => eval (toF2 X.1) (xMon T.1 * xMon U)) =
      (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (curryEquiv g z))
        (fun X : (i : Fin n) → BlockFibre g (z i) =>
          ∏ i : Fin n, eval (toF2 (X i).1) (xMon (blockSection T.1 i) * xMon (blockSection U i))) := by
    funext X
    change eval (toF2 X.1) (xMon T.1 * xMon U) =
      ∏ i : Fin n, eval (toF2 (fun j => X.1 (i, j)))
        (xMon (blockSection T.1 i) * xMon (blockSection U i))
    simp only [map_mul, xMon_eval_blocks, Finset.prod_mul_distrib]
  unfold coordinates
  rw [he]
  change (P2MProofComplexity.productFunctionBasis (fun i : Fin n => blockBasis g hg (z i))).repr
    ((LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (curryEquiv g z)).symm
      ((LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (curryEquiv g z)) _)) ((indexEquiv n g).symm S) = _
  rw [LinearEquiv.symm_apply_apply]
  exact P2MProofComplexity.productFunctionBasis_repr (fun i : Fin n => blockBasis g hg (z i))
    (fun i X => eval (toF2 X.1) (xMon (blockSection T.1 i) * xMon (blockSection U i))) (sections S)

theorem blockSection_empty {n m : ℕ} (U : Finset (Fin n × Fin m)) (i : Fin n)
    (hi : i ∉ U.image Prod.fst) : blockSection U i = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  apply hi
  have hij : (i, j) ∈ U := (Finset.mem_filter.mp hj).2
  exact Finset.mem_image.mpr ⟨(i, j), hij, rfl⟩

theorem coordinates_product_local {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (U : Finset (Fin n × Fin m))
    (z z' : Fin n → Bool) (hz : ∀ i ∈ U.image Prod.fst, z i = z' i) :
    coordinates g hg (xMon T.1 * xMon U) S z = coordinates g hg (xMon T.1 * xMon U) S z' := by
  classical
  rw [coordinates_product, coordinates_product]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ U.image Prod.fst
  · rw [hz i hi]
  · rw [blockSection_empty U i hi, blockCoefficient_empty, blockCoefficient_empty]

end SemAC02.P2MProductCoordinates
end

section
-- Inlined Solutions.SemanticCoordinateSpaces

open Module MvPolynomial AC02Frege
open SemAC02 SemAC02.P2MFibreBasis SemAC02.P2MFibreCoordinates

namespace SemAC02.P2MCoordinateSpaces

noncomputable def booleanEvaluation (n : ℕ) :
    MvPolynomial (Fin n) (ZMod 2) →ₗ[ZMod 2] ((Fin n → Bool) → ZMod 2) where
  toFun p z := eval (toF2 z) p
  map_add' p q := by funext z; exact map_add _ _ _
  map_smul' a p := by funext z; simp only [smul_eval, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

noncomputable def degreeSpace (n D : ℕ) :
    Submodule (ZMod 2) ((Fin n → Bool) → ZMod 2) :=
  (restrictTotalDegree (Fin n) (ZMod 2) D).map (booleanEvaluation n)

theorem mem_degreeSpace {n D : ℕ} (u : (Fin n → Bool) → ZMod 2) :
    u ∈ degreeSpace n D ↔ ∃ r : MvPolynomial (Fin n) (ZMod 2), r.totalDegree ≤ D ∧
      ∀ z : Fin n → Bool, eval (toF2 z) r = u z := by
  constructor
  · rintro ⟨r, hr, heq⟩
    exact ⟨r, (mem_restrictTotalDegree (Fin n) D r).mp hr, fun z => congrFun heq z⟩
  · rintro ⟨r, hr, heq⟩
    exact ⟨r, (mem_restrictTotalDegree (Fin n) D r).mpr hr, funext heq⟩

def localSpace {n : ℕ} (J : Finset (Fin n)) :
    Submodule (ZMod 2) ((Fin n → Bool) → ZMod 2) where
  carrier := {u | ∀ z z', (∀ i ∈ J, z i = z' i) → u z = u z'}
  zero_mem' := by intro z z' hz; rfl
  add_mem' := by intro f h hf hh z z' hz; exact congrArg₂ (· + ·) (hf z z' hz) (hh z z' hz)
  smul_mem' := by intro a f hf z z' hz; exact congrArg (fun x => a • x) (hf z z' hz)

theorem localSpace_mono {n : ℕ} {I J : Finset (Fin n)} (hIJ : I ⊆ J) :
    localSpace I ≤ localSpace J := by
  intro f hf z z' hz
  exact hf z z' (fun i hi => hz i (hIJ hi))

noncomputable def coordinateMap {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) :
    MvPolynomial (Fin n × Fin m) (ZMod 2) →ₗ[ZMod 2] ((Fin n → Bool) → ZMod 2) where
  toFun p := coordinates g hg p S
  map_add' p q := by funext z; exact coordinates_add g hg p q S z
  map_smul' a p := by
    funext z
    simpa only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] using coordinates_smul g hg a p S z

end SemAC02.P2MCoordinateSpaces
end

section
-- Inlined Solutions.P2MBooleanFunctionPolynomials

open MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip

namespace SemAC02.P2MBooleanFunctionPolynomials

theorem toF2_surjective {V : Type} (x : V → ZMod 2) : ∃ X : V → Bool, toF2 X = x := by
  refine ⟨fun v => decide (x v = 1), ?_⟩
  funext v
  have h : x v = 0 ∨ x v = 1 := by
    have h01 := AC02Frege.P2MMajorityFoundation.eq_zero_or_one (x v)
    exact h01
  rcases h with h | h <;> simp [toF2, h]

theorem multilinear_ext_bool {V : Type} [Finite V] {p q : MvPolynomial V (ZMod 2)}
    (hp : IsMultilinear p) (hq : IsMultilinear q)
    (he : ∀ X : V → Bool, eval (toF2 X) p = eval (toF2 X) q) : p = q := by
  apply multilinear_ext hp hq
  intro x
  obtain ⟨X, rfl⟩ := toF2_surjective x
  exact he X

theorem exists_polynomial (n : ℕ) (u : (Fin n → Bool) → ZMod 2) :
    ∃ r : MvPolynomial (Fin n) (ZMod 2),
      ∀ z : Fin n → Bool, eval (toF2 z) r = u z := by
  classical
  obtain ⟨r, _, hr⟩ := P2MBooleanLocality.represents_local_function Finset.univ u
    (fun z z' h => congrArg u (funext (fun i => h i (Finset.mem_univ i))))
  exact ⟨r, hr⟩

noncomputable def polynomial {n : ℕ} (u : (Fin n → Bool) → ZMod 2) :
    MvPolynomial (Fin n) (ZMod 2) := ML (Classical.choose (exists_polynomial n u))

theorem polynomial_multilinear {n : ℕ} (u : (Fin n → Bool) → ZMod 2) :
    IsMultilinear (polynomial u) := ml_multilinear _

@[simp] theorem eval_polynomial {n : ℕ} (u : (Fin n → Bool) → ZMod 2) (z : Fin n → Bool) :
    eval (toF2 z) (polynomial u) = u z := by
  rw [polynomial, eval_ml]
  exact Classical.choose_spec (exists_polynomial n u) z

theorem polynomial_eq {n : ℕ} (u : (Fin n → Bool) → ZMod 2)
    (r : MvPolynomial (Fin n) (ZMod 2))
    (hr : ∀ z : Fin n → Bool, eval (toF2 z) r = u z) : polynomial u = ML r := by
  apply multilinear_ext_bool
    (polynomial_multilinear u) (ml_multilinear r)
  intro z
  rw [eval_polynomial, eval_ml, hr]

noncomputable def polynomialMap (n : ℕ) :
    ((Fin n → Bool) → ZMod 2) →ₗ[ZMod 2] MvPolynomial (Fin n) (ZMod 2) where
  toFun := polynomial
  map_add' u v := by
    refine multilinear_ext_bool (polynomial_multilinear _) ?_ ?_
    · exact (mem_restrictDegree (Fin n) _ 1).mp
        (Submodule.add_mem _ ((mem_restrictDegree (Fin n) _ 1).mpr (polynomial_multilinear u))
          ((mem_restrictDegree (Fin n) _ 1).mpr (polynomial_multilinear v)))
    · intro z
      simp only [eval_polynomial, map_add, Pi.add_apply]
  map_smul' a u := by
    refine multilinear_ext_bool (polynomial_multilinear _) ?_ ?_
    · exact (mem_restrictDegree (Fin n) _ 1).mp
        (Submodule.smul_mem _ a ((mem_restrictDegree (Fin n) _ 1).mpr (polynomial_multilinear u)))
    · intro z
      simp only [eval_polynomial, smul_eval, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

theorem polynomial_degree {n D : ℕ} (u : (Fin n → Bool) → ZMod 2)
    (hu : u ∈ SemAC02.P2MCoordinateSpaces.degreeSpace n D) : (polynomial u).totalDegree ≤ D := by
  obtain ⟨r, hr, he⟩ := SemAC02.P2MCoordinateSpaces.mem_degreeSpace u |>.mp hu
  rw [polynomial_eq u r he]
  exact (ml_totalDegree_le r).trans hr

end SemAC02.P2MBooleanFunctionPolynomials
end

section
-- Inlined Solutions.SemanticMonomialLocality

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanBasis
open SemAC02 SemAC02.P2MFibreBasis SemAC02.P2MFibreCoordinates
open SemAC02.P2MProductCoordinates SemAC02.P2MCoordinateSpaces SemAC02.P2MBooleanLocality

namespace SemAC02.P2MMonomialLocality

theorem eval_monomial_squarefree {V : Type} (s : V →₀ ℕ) (a : ZMod 2) (x : V → ZMod 2) :
    eval x (monomial s a) = a * eval x (xMon s.support) := by
  calc
    eval x (monomial s a) = eval x (ML (monomial s a)) := (eval_ml _ _).symm
    _ = a * eval x (xMon s.support) := by
      rw [ml_monomial, squarefree_monomial (sqfree s) a (fun i => by simp [sqfree, Finsupp.mapRange_apply]),
        sqfree_support, smul_eval]

theorem coordinate_monomial {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (s : (Fin n × Fin m) →₀ ℕ) (a : ZMod 2) :
    coordinateMap g hg S (xMon T.1 * monomial s a) =
      a • coordinateMap g hg S (xMon T.1 * xMon s.support) := by
  funext z
  have he : (fun X : Fibre g z => eval (toF2 X.1) (xMon T.1 * monomial s a)) =
      a • (fun X : Fibre g z => eval (toF2 X.1) (xMon T.1 * xMon s.support)) := by
    funext X
    simp only [map_mul, eval_monomial_squarefree, Pi.smul_apply, smul_eq_mul]
    ring
  change (fibreBasis g hg z).equivFun (fun X => eval (toF2 X.1) (xMon T.1 * monomial s a)) S = _
  rw [he, map_smul]
  rfl

theorem support_card_le_sum {V : Type} (s : V →₀ ℕ) : s.support.card ≤ s.sum (fun _ e => e) := by
  classical
  change s.support.card ≤ ∑ i ∈ s.support, s i
  calc
    s.support.card = ∑ _i ∈ s.support, 1 := by simp
    _ ≤ ∑ i ∈ s.support, s i := Finset.sum_le_sum (fun i hi =>
      Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))

theorem degreeSpace_mono {n D E : ℕ} (hDE : D ≤ E) : degreeSpace n D ≤ degreeSpace n E := by
  intro u hu
  obtain ⟨r, hr, he⟩ := (mem_degreeSpace u).mp hu
  exact (mem_degreeSpace u).mpr ⟨r, hr.trans hDE, he⟩

theorem squarefree_local {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (U : Finset (Fin n × Fin m)) :
    coordinateMap g hg S (xMon T.1 * xMon U) ∈ localSpace (U.image Prod.fst) := by
  exact coordinates_product_local g hg S T U

theorem squarefree_degree {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (U : Finset (Fin n × Fin m)) :
    coordinateMap g hg S (xMon T.1 * xMon U) ∈ degreeSpace n U.card := by
  have hl := squarefree_local g hg S T U
  obtain ⟨r, hr, he⟩ := represents_local_function (U.image Prod.fst)
    (coordinateMap g hg S (xMon T.1 * xMon U)) hl
  exact (mem_degreeSpace _).mpr ⟨r, hr.trans (Finset.card_image_le), he⟩

theorem monomial_local {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (s : (Fin n × Fin m) →₀ ℕ) (a : ZMod 2) :
    coordinateMap g hg S (xMon T.1 * monomial s a) ∈ localSpace (s.support.image Prod.fst) := by
  rw [coordinate_monomial]
  exact Submodule.smul_mem _ a (squarefree_local g hg S T s.support)

theorem monomial_degree {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (s : (Fin n × Fin m) →₀ ℕ) (a : ZMod 2) :
    coordinateMap g hg S (xMon T.1 * monomial s a) ∈ degreeSpace n (s.sum (fun _ e => e)) := by
  rw [coordinate_monomial]
  apply Submodule.smul_mem
  exact degreeSpace_mono (support_card_le_sum s) (squarefree_degree g hg S T s.support)

end SemAC02.P2MMonomialLocality
end

section
-- Inlined Solutions.SemanticCoefficientControl

open Module MvPolynomial AC02Frege
open SemAC02 SemAC02.P2MFibreBasis SemAC02.P2MFibreCoordinates
open SemAC02.P2MCoordinateSpaces SemAC02.P2MMonomialLocality

namespace SemAC02.P2MCoefficientControl

theorem coordinate_polynomial_sum {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (f p : MvPolynomial (Fin n × Fin m) (ZMod 2)) :
    coordinateMap g hg S (f * p) = ∑ s ∈ p.support,
      coordinateMap g hg S (f * monomial s (p.coeff s)) := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [Finset.mul_sum, map_sum]

theorem basis_polynomial_degree {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) :
    coordinateMap g hg S (xMon T.1 * p) ∈ degreeSpace n p.totalDegree := by
  classical
  rw [coordinate_polynomial_sum]
  apply Submodule.sum_mem
  intro s hs
  exact degreeSpace_mono (le_totalDegree hs) (monomial_degree g hg S T s (p.coeff s))

theorem basis_polynomial_local {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S T : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (J : Finset (Fin n)) (hp : ∀ v ∈ p.vars, v.1 ∈ J) :
    coordinateMap g hg S (xMon T.1 * p) ∈ localSpace J := by
  classical
  rw [coordinate_polynomial_sum]
  apply Submodule.sum_mem
  intro s hs
  have hsub : s.support.image Prod.fst ⊆ J := by
    intro i hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    exact hp v ((support_subset_vars_of_mem_support hs) hv)
  exact localSpace_mono hsub (monomial_local g hg S T s (p.coeff s))

theorem coefficient_degree {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (f : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hf : f ∈ lnSpan g n)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) :
    coordinateMap g hg S (f * p) ∈ degreeSpace n p.totalDegree := by
  let L : MvPolynomial (Fin n × Fin m) (ZMod 2) →ₗ[ZMod 2] ((Fin n → Bool) → ZMod 2) :=
    (coordinateMap g hg S).comp (LinearMap.mulRight (ZMod 2) p)
  have hle : lnSpan g n ≤ (degreeSpace n p.totalDegree).comap L := by
    apply Submodule.span_le.mpr
    rintro q ⟨T, hT, rfl⟩
    exact basis_polynomial_degree g hg S ⟨T, hT⟩ p
  exact hle hf

theorem coefficient_locality {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (f : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hf : f ∈ lnSpan g n)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (J : Finset (Fin n)) (hp : ∀ v ∈ p.vars, v.1 ∈ J) (S : GlobalIndex g n) :
    coordinateMap g hg S (f * p) ∈ localSpace J := by
  let L : MvPolynomial (Fin n × Fin m) (ZMod 2) →ₗ[ZMod 2] ((Fin n → Bool) → ZMod 2) :=
    (coordinateMap g hg S).comp (LinearMap.mulRight (ZMod 2) p)
  have hle : lnSpan g n ≤ (localSpace J).comap L := by
    apply Submodule.span_le.mpr
    rintro q ⟨T, hT, rfl⟩
    exact basis_polynomial_local g hg S ⟨T, hT⟩ p J hp
  exact hle hf

end SemAC02.P2MCoefficientControl
end

section
-- Inlined Solutions.SemanticCoefficientPolynomials

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip
open SemAC02.P2MFibreBasis SemAC02.P2MFibreCoordinates SemAC02.P2MCoordinateSpaces
open SemAC02.P2MBooleanFunctionPolynomials SemAC02.P2MCoefficientControl

namespace SemAC02.P2MCoefficientPolynomials

noncomputable def coefficientMap {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) :
    MvPolynomial (Fin n × Fin m) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (Fin n) (ZMod 2) :=
  (polynomialMap n).comp (coordinateMap g hg S)

theorem coefficient_multilinear {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) :
    IsMultilinear (coefficientMap g hg S p) := polynomial_multilinear _

@[simp] theorem eval_coefficient {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (z : Fin n → Bool) :
    eval (toF2 z) (coefficientMap g hg S p) = coordinates g hg p S z := eval_polynomial _ _

theorem coefficient_congr {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (p q : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (he : ∀ X : Fin n × Fin m → Bool, eval (toF2 X) p = eval (toF2 X) q) :
    coefficientMap g hg S p = coefficientMap g hg S q := by
  apply multilinear_ext_bool (coefficient_multilinear g hg S p) (coefficient_multilinear g hg S q)
  intro z
  simp only [eval_coefficient, coordinates]
  exact congrArg (fun u => (fibreBasis g hg z).equivFun u S)
    (funext (fun X : Fibre g z => he X.1))

@[simp] theorem coefficient_ml {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (S : GlobalIndex g n) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) :
    coefficientMap g hg S (ML p) = coefficientMap g hg S p :=
  coefficient_congr g hg S _ _ (fun _ => eval_ml _ _)

theorem coefficient_degree_product {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (f : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hf : f ∈ lnSpan g n)
    (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) :
    (coefficientMap g hg S (f * p)).totalDegree ≤ p.totalDegree :=
  polynomial_degree _ (coefficient_degree g hg f hf p S)

theorem ble_degree {V : Type} (D : ℕ) (p : MvPolynomial V (ZMod 2)) (hp : p ∈ Ble V D) :
    p.totalDegree ≤ D := by
  classical
  have hle : Ble V D ≤ restrictTotalDegree V (ZMod 2) D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨A, hA, rfl⟩
    exact (mem_restrictTotalDegree V D _).mpr ((xMon_totalDegree A).trans_le hA)
  exact (mem_restrictTotalDegree V D p).mp (hle hp)

theorem coefficient_degree_multSpace {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (f : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hf : f ∈ lnSpan g n)
    (D : ℕ) (p : MvPolynomial (Fin n × Fin m) (ZMod 2)) (hp : p ∈ multSpace f D)
    (S : GlobalIndex g n) : (coefficientMap g hg S p).totalDegree ≤ D := by
  obtain ⟨q, hq, rfl⟩ := hp
  change (coefficientMap g hg S (ML (f * q))).totalDegree ≤ D
  rw [coefficient_ml]
  exact (coefficient_degree_product g hg f hf q S).trans (ble_degree D q hq)

theorem coordinates_mul {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p v : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) (z : Fin n → Bool) :
    coordinates g hg (p * v) S z = ∑ T : GlobalIndex g n,
      coordinates g hg p T z * coordinates g hg (xMon T.1 * v) S z := by
  classical
  have he : (fun X : Fibre g z => eval (toF2 X.1) (p * v)) =
      ∑ T : GlobalIndex g n, coordinates g hg p T z •
        (fun X : Fibre g z => eval (toF2 X.1) (xMon T.1 * v)) := by
    funext X
    simp only [map_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [coordinates_expansion g hg p z X, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro T _
    ring
  change (fibreBasis g hg z).equivFun (fun X => eval (toF2 X.1) (p * v)) S = _
  rw [he, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coordinates]

theorem coefficient_mul {n m : ℕ} (g : (Fin m → Bool) → Bool) (hg : Antitone g)
    (p v : MvPolynomial (Fin n × Fin m) (ZMod 2)) (S : GlobalIndex g n) :
    coefficientMap g hg S (p * v) = ∑ T : GlobalIndex g n,
      ML (coefficientMap g hg T p * coefficientMap g hg S (xMon T.1 * v)) := by
  classical
  refine multilinear_ext_bool (coefficient_multilinear g hg S _) ?_ ?_
  · exact (mem_restrictDegree (Fin n) _ 1).mp
      (Submodule.sum_mem _ (fun _ _ => (mem_restrictDegree (Fin n) _ 1).mpr (ml_multilinear _)))
  · intro z
    simp only [eval_coefficient, map_sum, eval_ml, map_mul]
    exact coordinates_mul g hg p v S z

end SemAC02.P2MCoefficientPolynomials
end

section
-- Inlined Solutions.P2MRelativeSpaceAlgebra

open MvPolynomial AC02Frege SemAC02
open AC02Frege.P2MBooleanAlgebra AC02Frege.P2MBooleanFlip AC02Frege.P2MBooleanBasis

namespace SemAC02.P2MRelativeSpaceAlgebra

theorem mem_Ble_iff {V : Type} (D : ℕ) (p : MvPolynomial V (ZMod 2)) :
    p ∈ Ble V D ↔ IsMultilinear p ∧ p.totalDegree ≤ D := by
  have he : Ble V D = monomialSpan (fun A : Finset V => A.card ≤ D) := by
    unfold Ble monomialSpan
    congr 1
    ext q
    constructor
    · rintro ⟨A,hA,rfl⟩
      exact ⟨A,hA,rfl⟩
    · rintro ⟨A,hA,rfl⟩
      exact ⟨A,hA,rfl⟩
  rw [he, mem_light_iff]

theorem mem_multSpace_of_degree {V : Type} [Finite V]
    (f Q : MvPolynomial V (ZMod 2)) (D : ℕ) (hQ : Q.totalDegree ≤ D) :
    mulML f Q ∈ multSpace f D := by
  refine ⟨ML Q, (mem_Ble_iff D _).mpr ⟨ml_multilinear _, (ml_totalDegree_le _).trans hQ⟩, ?_⟩
  change ML (f * ML Q) = ML (f * Q)
  exact ml_mul_right f Q

theorem multSpace_multilinear {V : Type} (f p : MvPolynomial V (ZMod 2)) (D : ℕ)
    (hp : p ∈ multSpace f D) : IsMultilinear p := by
  obtain ⟨Q,_,rfl⟩ := hp
  exact ml_multilinear _

theorem multSpace_degree {V : Type} (f p : MvPolynomial V (ZMod 2)) (k D : ℕ)
    (hf : f ∈ Ble V k) (hp : p ∈ multSpace f D) : p.totalDegree ≤ k+D := by
  obtain ⟨Q,hQ,rfl⟩ := hp
  change (ML (f*Q)).totalDegree ≤ k+D
  exact (ml_totalDegree_le _).trans ((totalDegree_mul f Q).trans
    (Nat.add_le_add ((mem_Ble_iff k f).mp hf).2 ((mem_Ble_iff D Q).mp hQ).2))

theorem relative_polynomial_mul {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2)))
    (f Q v : MvPolynomial (Fin n) (ZMod 2)) (D : ℕ)
    (hp : P2MRelativePC.Derivable P (multSpace f D) (mulML f Q))
    (hdeg : Q.totalDegree + v.totalDegree ≤ D) :
    P2MRelativePC.Derivable P (multSpace f D) (ML (mulML f Q * v)) := by
  apply P2MRelativePC.pc_polynomial_mul P (multSpace f D) (mulML f Q) v hp (ml_multilinear _)
  intro w hw
  have he : ML (mulML f Q * w) = mulML f (Q*w) := by
    change ML (ML (f*Q) * w) = ML (f*(Q*w))
    rw [ml_mul_left, mul_assoc]
  rw [he]
  apply mem_multSpace_of_degree
  exact (totalDegree_mul Q w).trans (by omega)

end SemAC02.P2MRelativeSpaceAlgebra
end

section
-- Inlined Solutions.P2MBooleanDimension

open Module MvPolynomial AC02Frege
open AC02Frege.P2MBooleanAlgebra

namespace SemAC02.P2MBooleanDimension

abbrev DegreeIndex (n D : ℕ) := {A : Finset (Fin n) // A.card ≤ D}

theorem span_degree_monomials (n D : ℕ) :
    Submodule.span (ZMod 2) (Set.range (fun A : DegreeIndex n D => xMon A.1)) = Ble (Fin n) D := by
  congr 1
  ext p
  constructor
  · rintro ⟨A,rfl⟩
    exact ⟨A.1,A.2,rfl⟩
  · rintro ⟨A,hA,rfl⟩
    exact ⟨⟨A,hA⟩,rfl⟩

noncomputable def degreeBasis (n D : ℕ) : Basis (DegreeIndex n D) (ZMod 2) (Ble (Fin n) D) :=
  (Basis.span (xMon_linearIndependent.comp (fun A : DegreeIndex n D => A.1) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (span_degree_monomials n D))

instance finite_Ble (n D : ℕ) : Module.Finite (ZMod 2) (Ble (Fin n) D) :=
  Module.Finite.of_basis (degreeBasis n D)

def degreeIndexEquiv (n D : ℕ) : DegreeIndex n D ≃
    (j : Fin (min D n + 1)) × {A : Finset (Fin n) // A.card = j.1} where
  toFun A := ⟨⟨A.1.card, by
    have hcard := Finset.card_le_univ A.1
    simp only [Fintype.card_fin] at hcard
    omega⟩,A.1,rfl⟩
  invFun B := ⟨B.2.1,by have := B.1.2; have := B.2.2; omega⟩
  left_inv A := by apply Subtype.ext; rfl
  right_inv B := by
    rcases B with ⟨⟨j,hj⟩,A,hA⟩
    cases hA
    rfl

theorem finrank_Ble (n D : ℕ) : finrank (ZMod 2) (Ble (Fin n) D) = Hn n D := by
  classical
  rw [Module.finrank_eq_card_basis (degreeBasis n D), Fintype.card_congr (degreeIndexEquiv n D), Fintype.card_sigma]
  simp only [Fintype.card_finset_len, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range _ _

theorem Hn_pos (n D : ℕ) : 0 < Hn n D := by
  unfold Hn
  apply lt_of_lt_of_le (show 0 < n.choose 0 by simp)
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)

end SemAC02.P2MBooleanDimension
end

section
-- Inlined Solutions.P2MMultiplierSupportCount

set_option maxHeartbeats 1000000

open Module MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra

namespace SemAC02.P2MMultiplierSupportCount

abbrev MultiplierIndex {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :=
  {S : Finset (Fin n × Fin m) // S.card ≤ k ∧ IsLnSupport g S}

theorem multiplier_span {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :
    Submodule.span (ZMod 2) (Set.range (fun S : MultiplierIndex g n k => xMon S.1)) =
      multiplierSpace g n k := by
  unfold multiplierSpace
  congr 1
  ext p
  constructor
  · rintro ⟨S,rfl⟩
    exact ⟨S.1,S.2,rfl⟩
  · rintro ⟨S,hS,rfl⟩
    exact ⟨⟨S,hS⟩,rfl⟩

noncomputable def multiplierBasis {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :
    Basis (MultiplierIndex g n k) (ZMod 2) (multiplierSpace g n k) :=
  (Basis.span (xMon_linearIndependent.comp (fun S : MultiplierIndex g n k => S.1) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (multiplier_span g n k))

instance finite_multiplierSpace {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :
    Module.Finite (ZMod 2) (multiplierSpace g n k) := Module.Finite.of_basis (multiplierBasis g n k)

theorem finrank_multiplier {m : ℕ} (g : (Fin m → Bool) → Bool) (n k : ℕ) :
    finrank (ZMod 2) (multiplierSpace g n k) =
      (Finset.univ.filter (fun S : Finset (Fin n × Fin m) => S.card ≤ k ∧ IsLnSupport g S)).card := by
  rw [Module.finrank_eq_card_basis (multiplierBasis g n k)]
  exact Fintype.card_subtype _

abbrev LowIndex (V : Type) (k : ℕ) := {S : Finset V // S.card ≤ k}

def lowIndexEquiv (V : Type) [Fintype V] [DecidableEq V] (k : ℕ) :
    LowIndex V k ≃ (j : Fin (min k (Fintype.card V)+1)) × {S : Finset V // S.card = j.1} where
  toFun S := ⟨⟨S.1.card,by have := Finset.card_le_univ S.1; omega⟩,S.1,rfl⟩
  invFun T := ⟨T.2.1,by have := T.1.2; have := T.2.2; omega⟩
  left_inv S := by apply Subtype.ext; rfl
  right_inv T := by rcases T with ⟨⟨j,hj⟩,S,hS⟩; cases hS; rfl

theorem low_support_card (V : Type) [Fintype V] [DecidableEq V] (k : ℕ) :
    (Finset.univ.filter (fun S : Finset V => S.card ≤ k)).card = Hn (Fintype.card V) k := by
  rw [← Fintype.card_subtype,Fintype.card_congr (lowIndexEquiv V k),Fintype.card_sigma]
  simp only [Fintype.card_finset_len]
  exact Fin.sum_univ_eq_sum_range _ _

end SemAC02.P2MMultiplierSupportCount
end

section
-- Inlined Solutions.P2MBooleanDegreeBasis

open Module MvPolynomial AC02Frege AC02Frege.P2MBooleanAlgebra

namespace SemAC02.P2MBooleanDegreeBasis

abbrev DegreeIndex (V : Type) (K : ℕ) := {T : Finset V // T.card ≤ K}

theorem degree_span (V : Type) (K : ℕ) :
    Submodule.span (ZMod 2) (Set.range (fun T : DegreeIndex V K => xMon T.1)) = Ble V K := by
  unfold Ble
  congr 1
  ext p
  constructor
  · rintro ⟨T,rfl⟩; exact ⟨T.1,T.2,rfl⟩
  · rintro ⟨T,hT,rfl⟩; exact ⟨⟨T,hT⟩,rfl⟩

noncomputable def degreeBasis (V : Type) (K : ℕ) : Basis (DegreeIndex V K) (ZMod 2) (Ble V K) :=
  (Basis.span (xMon_linearIndependent.comp (fun T : DegreeIndex V K => T.1) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (degree_span V K))

instance finite_Ble (V : Type) [Fintype V] [DecidableEq V] (K : ℕ) : Module.Finite (ZMod 2) (Ble V K) :=
  Module.Finite.of_basis (degreeBasis V K)

theorem finrank_Ble (V : Type) [Fintype V] [DecidableEq V] (K : ℕ) :
    finrank (ZMod 2) (Ble V K) = Hn (Fintype.card V) K := by
  rw [Module.finrank_eq_card_basis (degreeBasis V K)]
  have he : Fintype.card (DegreeIndex V K) =
      (Finset.univ.filter (fun T : Finset V => T.card ≤ K)).card := Fintype.card_subtype _
  rw [he]
  exact P2MMultiplierSupportCount.low_support_card V K

end SemAC02.P2MBooleanDegreeBasis
end

section
-- Inlined Solutions.P2MBooleanDegreeCounts

namespace AC02Frege.P2MBooleanDegreeCounts

open Module

lemma monoCount_eq_Hn (N K : ℕ) : monoCount N K = SemAC02.Hn N K := by
  unfold monoCount SemAC02.Hn
  apply (Finset.sum_subset (show Finset.range (min K N+1) ⊆ Finset.range (K+1) by
    apply Finset.range_mono; omega) ?_).symm
  intro i hi hnot
  have hiK : i ≤ K := by have := Finset.mem_range.mp hi; omega
  have hiN : N < i := by
    simp only [Finset.mem_range] at hnot
    omega
  exact Nat.choose_eq_zero_of_lt hiN

lemma finrank_Ble {V : Type} [Fintype V] [DecidableEq V] (K : ℕ) :
    finrank (ZMod 2) (SemAC02.Ble V K) = monoCount (Fintype.card V) K := by
  rw [SemAC02.P2MBooleanDegreeBasis.finrank_Ble,monoCount_eq_Hn]

lemma monoCount_mono (N : ℕ) {a b : ℕ} (hab : a ≤ b) : monoCount N a ≤ monoCount N b := by
  unfold monoCount
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (by omega)) (fun _ _ _ => Nat.zero_le _)

end AC02Frege.P2MBooleanDegreeCounts
end

section
-- Inlined Solutions.P2MApproximateCumulativeRatios

set_option maxHeartbeats 2000000

namespace P2MProofComplexity.P2MApproximateCumulativeRatios

open Finset

/-- Pairwise approximate monotonicity of layer densities bounds their cumulative averages,
with the error paid once, rather than at every cumulative step. -/
theorem cumulative_comparison (a w : ℕ → ℝ) (k K : ℕ) (hkK : k ≤ K)
    (hw : ∀ i ≤ K, 0 < w i) (E : ℝ) (hE : 0 ≤ E)
    (hpair : ∀ i ≤ k, ∀ j, k < j → j ≤ K → a j/w j ≤ a i/w i+E) :
    (∑ j ∈ range (K+1), a j)/(∑ j ∈ range (K+1), w j) ≤
      (∑ j ∈ range (k+1), a j)/(∑ j ∈ range (k+1), w j)+E := by
  let B := ∑ i ∈ range (k+1), a i
  let W := ∑ i ∈ range (k+1), w i
  have hW : 0 < W := by
    apply Finset.sum_pos
    · intro i hi
      exact hw i (by have := mem_range.mp hi; omega)
    · exact ⟨0,by simp⟩
  have hWfull : 0 < ∑ i ∈ range (K+1), w i := by
    apply Finset.sum_pos
    · intro i hi
      exact hw i (by have := mem_range.mp hi; omega)
    · exact ⟨0,by simp⟩
  have hlate (j : ℕ) (hkj : k < j) (hjK : j ≤ K) : a j ≤ (B/W+E)*w j := by
    have hcross : (a j/w j-E)*W ≤ B := by
      dsimp only [B,W]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := by have := mem_range.mp hi; omega
      apply (le_div_iff₀ (hw i (hik.trans hkK))).mp
      have hh := hpair i hik j hkj hjK
      linarith
    have hd : a j/w j-E ≤ B/W := (le_div_iff₀ hW).mpr hcross
    apply (div_le_iff₀ (hw j hjK)).mp
    linarith
  have hbase : B ≤ (B/W+E)*W := by
    have heq : B/W*W = B := div_mul_cancel₀ B hW.ne'
    have hn := mul_nonneg hE hW.le
    nlinarith
  have hsum : ∀ t, k ≤ t → t ≤ K →
      (∑ j ∈ range (t+1), a j) ≤ (B/W+E)*(∑ j ∈ range (t+1), w j) := by
    intro t hkt
    induction t,hkt using Nat.le_induction with
    | base => intro _; exact hbase
    | succ t hkt ih =>
      intro htK
      have hh := ih (by omega)
      have hl := hlate (t+1) (by omega) htK
      rw [Finset.sum_range_succ a (t+1),Finset.sum_range_succ w (t+1)]
      nlinarith
  exact (div_le_iff₀ hWfull).mpr (hsum K hkK le_rfl)

/-- A per-step error bounded by e*N accumulates to at most e*N^2 over at most N steps. -/
theorem density_drift (δ : ℕ → ℝ) (N K : ℕ) (hKN : K ≤ N) (e : ℝ) (he : 0 ≤ e)
    (hstep : ∀ j < K, δ (j+1) ≤ δ j+e*N) :
    ∀ i ≤ K, ∀ j, i ≤ j → j ≤ K → δ j ≤ δ i+e*(N : ℝ)^2 := by
  intro i hi j hij hjK
  have hchain : ∀ t, i ≤ t → t ≤ K → δ t ≤ δ i+e*N*((t-i : ℕ) : ℝ) := by
    intro t hit
    induction t,hit using Nat.le_induction with
    | base => intro _; simp
    | succ t hit ih =>
      intro htK
      have hh := ih (by omega)
      have hs := hstep t (by omega)
      have hsub : t+1-i = (t-i)+1 := by omega
      rw [hsub,Nat.cast_add,Nat.cast_one]
      nlinarith
  have h := hchain j hij hjK
  have hlen : ((j-i : ℕ) : ℝ) ≤ N := by exact_mod_cast (show j-i ≤ N by omega)
  have hn : 0 ≤ e*(N : ℝ) := mul_nonneg he (Nat.cast_nonneg _)
  have he' := mul_le_mul_of_nonneg_left hlen hn
  nlinarith

end P2MProofComplexity.P2MApproximateCumulativeRatios
end

section
-- Inlined Solutions.P2MApproximateBinomialRatios

set_option maxHeartbeats 2000000

namespace AC02Frege.P2MApproximateBinomialRatios

open Finset P2MExcludedCumulativeCounts

lemma monoCount_pos (N j : ℕ) : 0 < monoCount N j := by
  have h : 1 ≤ monoCount N j := by
    unfold monoCount
    simpa only [Nat.choose_zero_right] using
      (Finset.single_le_sum (f := fun i => N.choose i) (s := range (j+1)) (by intros; omega) (show 0 ∈ range (j+1) by simp))
  omega

lemma density_step (N K : ℕ) (hKN : 2*K < N) (b E : ℕ → ℕ) (e : ℝ) (he : 0 ≤ e)
    (hinc : ∀ j < K, b (j+1)*(j+1) ≤ (b j+E j)*(N-j))
    (hE : ∀ j ≤ K, (E j : ℝ) ≤ e*(monoCount N j : ℝ)) (j : ℕ) (hj : j < K) :
    (b (j+1) : ℝ)/(N.choose (j+1) : ℝ) ≤ (b j : ℝ)/(N.choose j : ℝ)+e*(j+1) := by
  have hjN : j+1 ≤ N := by omega
  have hp : (0 : ℝ) < (N.choose j : ℝ) := by exact_mod_cast Nat.choose_pos (by omega : j ≤ N)
  have hp' : (0 : ℝ) < (N.choose (j+1) : ℝ) := by exact_mod_cast Nat.choose_pos hjN
  have hi : (b (j+1) : ℝ)*(j+1) ≤ ((b j : ℝ)+(E j : ℝ))*((N-j : ℕ) : ℝ) := by exact_mod_cast hinc j hj
  have hc : (N.choose (j+1) : ℝ)*(j+1) = (N.choose j : ℝ)*((N-j : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq N j
  have hcross : (b (j+1) : ℝ)*(N.choose j : ℝ) ≤ ((b j : ℝ)+(E j : ℝ))*(N.choose (j+1) : ℝ) := by
    apply (mul_le_mul_iff_of_pos_right (by positivity : (0 : ℝ) < j+1)).mp
    calc
      _ = ((b (j+1) : ℝ)*(j+1))*(N.choose j : ℝ) := by ring
      _ ≤ (((b j : ℝ)+(E j : ℝ))*((N-j : ℕ) : ℝ))*(N.choose j : ℝ) :=
        mul_le_mul_of_nonneg_right hi hp.le
      _ = ((b j : ℝ)+(E j : ℝ))*((N.choose j : ℝ)*((N-j : ℕ) : ℝ)) := by ring
      _ = _ := by rw [← hc]; ring
  have hratio : (b (j+1) : ℝ)/(N.choose (j+1) : ℝ) ≤ ((b j : ℝ)+(E j : ℝ))/(N.choose j : ℝ) :=
    (div_le_div_iff₀ hp' hp).mpr hcross
  have hcount : (monoCount N j : ℝ) ≤ (j+1)*(N.choose j : ℝ) := by
    exact_mod_cast cumulative_choose_le N j (by omega)
  have hEb : (E j : ℝ) ≤ e*(j+1)*(N.choose j : ℝ) :=
    (hE j (by omega)).trans (by nlinarith [mul_le_mul_of_nonneg_left hcount he])
  have hEr : (E j : ℝ)/(N.choose j : ℝ) ≤ e*(j+1) := (div_le_iff₀ hp).mpr hEb
  rw [add_div] at hratio
  linarith

/-- The numerical conclusion of Appendix B.1 from its approximate incidence hypothesis. -/
theorem cumulative_bound (N K k : ℕ) (hKN : 2*K < N) (hk : k ≤ K)
    (b E : ℕ → ℕ) (e : ℝ) (he : 0 ≤ e)
    (hinc : ∀ j < K, b (j+1)*(j+1) ≤ (b j+E j)*(N-j))
    (hE : ∀ j ≤ K, (E j : ℝ) ≤ e*(monoCount N j : ℝ)) :
    (monoCount N k : ℝ)/(monoCount N K : ℝ)*(∑ j ∈ range (K+1), (b j : ℝ))
        -(N : ℝ)^2*e*(monoCount N k : ℝ) ≤ ∑ j ∈ range (k+1), (b j : ℝ) := by
  let δ := fun j => (b j : ℝ)/(N.choose j : ℝ)
  have hstep (j : ℕ) (hj : j < K) : δ (j+1) ≤ δ j+e*N := by
    have h := density_step N K hKN b E e he hinc hE j hj
    have hn : (j : ℝ)+1 ≤ N := by exact_mod_cast (show j+1 ≤ N by omega)
    dsimp only [δ]
    nlinarith [mul_le_mul_of_nonneg_left hn he]
  have hpair := P2MProofComplexity.P2MApproximateCumulativeRatios.density_drift δ N K (by omega) e he hstep
  have hw (i : ℕ) (hi : i ≤ K) : (0 : ℝ) < (N.choose i : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : i ≤ N)
  have hcum := P2MProofComplexity.P2MApproximateCumulativeRatios.cumulative_comparison
    (fun j => (b j : ℝ)) (fun j => (N.choose j : ℝ)) k K hk hw
    (e*(N : ℝ)^2) (mul_nonneg he (sq_nonneg _))
    (fun i hi j hkj hj => hpair i (hi.trans hk) j (by omega) hj)
  have hkpos : (0 : ℝ) < (monoCount N k : ℝ) := by exact_mod_cast monoCount_pos N k
  have hM : ∀ j, (∑ i ∈ range (j+1), (N.choose i : ℝ)) = (monoCount N j : ℝ) := by
    intro j
    rw [monoCount,Nat.cast_sum]
  rw [hM,hM] at hcum
  have h := mul_le_mul_of_nonneg_right hcum hkpos.le
  rw [add_mul,div_mul_cancel₀ _ hkpos.ne'] at h
  have hl : ((∑ j ∈ range (K+1), (b j : ℝ))/(monoCount N K : ℝ))*(monoCount N k : ℝ) =
      (monoCount N k : ℝ)/(monoCount N K : ℝ)*(∑ j ∈ range (K+1), (b j : ℝ)) := by ring
  rw [hl] at h
  nlinarith

end AC02Frege.P2MApproximateBinomialRatios
end

section
-- Inlined Solutions.P2MMajorityApproximationNumerics

namespace AC02Frege.P2MMajorityApproximationNumerics

lemma eta_pos (N K r : ℕ) : 0 < etaFrac N K r := by
  have hm : (0 : ℝ) < (monoCount N (K-r) : ℝ) := by exact_mod_cast P2MApproximateBinomialRatios.monoCount_pos N (K-r)
  have hM : (0 : ℝ) < (monoCount N K : ℝ) := by exact_mod_cast P2MApproximateBinomialRatios.monoCount_pos N K
  unfold etaFrac
  positivity

lemma eta_le_half (N K r : ℕ) : etaFrac N K r ≤ (1/2 : ℝ) := by
  have hM : (0 : ℝ) < (monoCount N K : ℝ) := by exact_mod_cast P2MApproximateBinomialRatios.monoCount_pos N K
  have hm : (monoCount N (K-r) : ℝ) ≤ (monoCount N K : ℝ) := by
    exact_mod_cast P2MBooleanDegreeCounts.monoCount_mono N (Nat.sub_le K r)
  unfold etaFrac
  apply (div_le_iff₀ hM).mpr
  nlinarith

lemma contraction_numerics (N M m e x z y EK Es : ℝ) (hN : 1 ≤ N) (hm : m ≤ M)
    (hM : 0 ≤ M) (he : 0 ≤ e) (α : ℝ)
    (hcomp : α*x-N^2*e*m ≤ z) (hgain : y ≤ x-(1/2)*z+EK+(1/2)*Es)
    (hEK : EK ≤ e*M) (hEs : Es ≤ e*m) : y ≤ (1-(1/2)*α)*x+2*N^2*e*M := by
  have hsq : 1 ≤ N^2 := by nlinarith
  have hsmall : e*m ≤ e*M := mul_le_mul_of_nonneg_left hm he
  have hbig : N^2*e*m ≤ N^2*e*M := mul_le_mul_of_nonneg_left hm (mul_nonneg (sq_nonneg _) he)
  have hscale : e*M ≤ N^2*e*M := by
    have hh := mul_le_mul_of_nonneg_right hsq (mul_nonneg he hM)
    nlinarith
  nlinarith

end AC02Frege.P2MMajorityApproximationNumerics
end

section
-- Inlined Solutions.P2MMajorityStandardParameters

set_option maxHeartbeats 2000000

namespace AC02Frege.P2MMajorityStandardParameters

open MvPolynomial LiftSAParity

theorem counts {n ℓ : ℕ} (hℓ : Odd ℓ) (c a : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (ha : 1 ≤ a) (ha' : 2*Real.log 2+12 ≤ c*a^2/8)
    (hn : 1 ≤ n) (hlarge : 128*(a+2) ≤ Real.sqrt ℓ)
    (F : CNF (Fin n)) (hF : ¬ PCDerivable F ⌊c*n⌋₊ 1) :
    let D := ⌊c*n⌋₊
    let Q := ⌊c*n/16⌋₊
    let K := ⌊((n*ℓ : ℕ) : ℝ)/2-a*n*Real.sqrt ℓ⌋₊
    n ≤ K ∧ 2*K < n*ℓ ∧ 0 < (hThresh F ℓ D K : ℝ) ∧
      epsExcl n ℓ Q K*(monoCount (n*ℓ) K : ℝ) ≤ Real.exp (-12*(n : ℝ))*(hThresh F ℓ D K : ℝ) ∧
      (Eexcl n ℓ Q K : ℝ) ≤ Real.exp (-12*(n : ℝ))*(hThresh F ℓ D K : ℝ) := by
  dsimp only
  obtain ⟨harg,hnK,hKN⟩ := P2MMajorityCutoff.offset_bounds n ℓ a hn ha hlarge
  obtain ⟨hh,he,hratio⟩ := lemma_4_19_two_counts hℓ c a hc0 hc1 ha F hF harg
  have hM : (0 : ℝ) < monoCount (n*ℓ) ⌊((n*ℓ : ℕ) : ℝ)/2-a*n*Real.sqrt ℓ⌋₊ := by
    exact_mod_cast P2MApproximateBinomialRatios.monoCount_pos _ _
  have hpos : 0 < (hThresh F ℓ ⌊c*n⌋₊ ⌊((n*ℓ : ℕ) : ℝ)/2-a*n*Real.sqrt ℓ⌋₊ : ℝ) :=
    (div_pos hM (by positivity)).trans_le hh
  have hemul := (div_le_iff₀ hpos).mp (hratio ha')
  have hE := P2MExcludedCumulativeCounts.excluded_bound n ℓ ⌊c*n/16⌋₊
    ⌊((n*ℓ : ℕ) : ℝ)/2-a*n*Real.sqrt ℓ⌋₊ ⌊((n*ℓ : ℕ) : ℝ)/2-a*n*Real.sqrt ℓ⌋₊ le_rfl (by omega)
  exact ⟨hnK,hKN,hpos,hemul,hE.trans hemul⟩

theorem inverse_eta (n ℓ r : ℕ) (a : ℝ) (hn : 2 ≤ n) (ha : 1 ≤ a)
    (hlarge : 128*(a+2) ≤ Real.sqrt ℓ) (hr : 1 ≤ r) (hrn : r ≤ n) :
    (etaFrac (n*ℓ) ⌊((n*ℓ : ℕ) : ℝ)/2-a*n*Real.sqrt ℓ⌋₊ r)⁻¹ ≤
      2*Real.exp (64*(a+2)*r/Real.sqrt ℓ) := by
  have hc := lemma_C_1_cumulative_counts n ℓ r a hn ha hlarge hr hrn
  have hpos := P2MMajorityApproximationNumerics.eta_pos (n*ℓ) ⌊((n*ℓ : ℕ) : ℝ)/2-a*n*Real.sqrt ℓ⌋₊ r
  calc
    _ ≤ ((1/2 : ℝ)*Real.exp (-(64*(a+2)*r/Real.sqrt ℓ)))⁻¹ :=
      (inv_le_inv₀ hpos (by positivity)).mpr hc
    _ = _ := by rw [mul_inv_rev,Real.exp_neg,inv_inv]; norm_num <;> ring

end AC02Frege.P2MMajorityStandardParameters
end

section
-- Inlined Solutions.P2MDepth35LowerBound

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace AC02Frege.P2MDepth35LowerBound

open Module MvPolynomial LiftSAParity Filter

theorem lower_bound :
    ∀ c : ℝ, 0 < c → ∀ lam₁ lam₂ : ℝ, 0 < lam₁ → lam₁ ≤ lam₂ →
    ∃ α : ℝ, 0 < α ∧ ∀ w : ℕ, ∃ k n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ F : CNF (Fin n), (∀ C ∈ F, C.card ≤ w) → ¬ PCDerivable F ⌊c*n⌋₊ 1 →
    ∀ ℓ : ℕ, Odd ℓ → lam₁*Real.log n ≤ ℓ → (ℓ : ℝ) ≤ lam₂*Real.log n →
      encLength (lift F ℓ) ≤ n^k ∧
      ∀ b : ℕ, 1 ≤ b → b^2 ≤ ℓ → ∀ π : List (Line (Fin n × Fin ℓ)),
        IsRefutation b (lift F ℓ) π →
          α*Real.log n^((3 : ℝ)/2)/b ≤ Real.log (totalSize π) := by
  intro c hc lam₁ lam₂ hlam₁ hlam
  let c₀ := min c (1/2)
  have hc₀ : 0 < c₀ := lt_min hc (by norm_num)
  have hc₀1 : c₀ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨a,ha,ha'⟩ := P2MDepth35Constants.choose_offset c₀ hc₀
  let A := 64*(a+2)
  have hA : 0 < A := by dsimp [A]; linarith
  obtain ⟨α,hα,hsmooth⟩ := P2MDepth35Constants.choose_alpha A lam₁ hA hlam₁
  refine ⟨α,hα,?_⟩
  intro w
  obtain ⟨k,hpoly⟩ := P2MMajorityLiftSize.eventually_polynomial_size lam₂ w
  have hready := P2MDepth35AsymptoticGrowth.eventually_ready c₀ A α lam₁ lam₂ hc₀ hA hα hlam₁ hlam w
  obtain ⟨n₀,hn₀⟩ := Filter.eventually_atTop.mp (hpoly.and hready)
  refine ⟨k,n₀,?_⟩
  intro n hn F hw hF ℓ hℓ hlow hupp
  obtain ⟨hsize,hparam⟩ := hn₀ n hn
  have hd := hparam ℓ hlow hupp
  refine ⟨hsize ℓ hupp F hw,?_⟩
  intro b hb hbell π hπ
  by_contra hnot
  have hnot' : Real.log (totalSize π) < α*Real.log n^((3 : ℝ)/2)/(b : ℝ) := lt_of_not_ge hnot
  let D := ⌊c₀*n⌋₊
  let Q := ⌊c₀*n/16⌋₊
  let K := ⌊((n*ℓ : ℕ) : ℝ)/2-a*n*Real.sqrt ℓ⌋₊
  let η : ℕ → ℝ := fun d => etaFrac (n*ℓ) K d
  let T : ℝ := totalSize π
  have hF₀ : ¬ PCDerivable F D 1 := by
    intro hp
    apply hF
    exact P2MDepth35Constants.pc_degree_mono (Nat.floor_mono
      (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg n : (0 : ℝ) ≤ _))) hp
  have hlarge : 128*(a+2) ≤ Real.sqrt (ℓ : ℝ) := by
    have hh := hd.block_large
    dsimp [A] at hh
    linarith
  obtain ⟨hnK,hKN,hh,he,hE⟩ := P2MMajorityStandardParameters.counts hℓ c₀ a hc₀ hc₀1 ha ha'
    (by have hn2 := hd.n_large; omega) hlarge F hF₀
  have hT : 1 ≤ T := by
    dsimp only [T]
    exact_mod_cast P2MDepth35ProofSize.total_size_pos (lift F ℓ)
      (P2MDepth35ProofSize.no_empty_lift F ℓ (P2MDepth35ProofSize.no_empty_base F hF₀)) π hπ
  have hTp : 0 < T := by linarith
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbp : 0 < (b : ℝ) := by linarith
  have hbn : b ≤ n := by have hell := hd.block_le_n; nlinarith
  have hbx : (b : ℝ) ≤ Real.sqrt (ℓ : ℝ) := Real.le_sqrt_of_sq_le (by exact_mod_cast hbell)
  have hx : 0 < Real.sqrt (ℓ : ℝ) := by linarith
  have hz : 0 < Real.log (n : ℝ) := by have hz1 := hd.log_large; linarith
  have hsmall : (b : ℝ)*Real.log T ≤ α*Real.log n*Real.sqrt (Real.log (n : ℝ)) := by
    have hh := (lt_div_iff₀ hbp).mp hnot'
    rw [P2MDepth35Constants.rpow_three_halves hz] at hh
    dsimp [T]
    nlinarith
  have heta : ∀ d : ℕ, 1 ≤ d → d ≤ n → 0 < η d ∧ (η d)⁻¹ ≤ 2*Real.exp (A*d/Real.sqrt ℓ) := by
    intro d hd1 hdn
    exact ⟨P2MMajorityApproximationNumerics.eta_pos _ _ _,
      P2MMajorityStandardParameters.inverse_eta n ℓ d a hd.n_large ha hlarge hd1 hdn⟩
  obtain ⟨tin,tout,htin,htout,hRn,hRq,hS,hpin,hpout,hInv,hlogT⟩ :=
    P2MDepth35FactorBounds.factor_parameters η hd.log_large hx hA hα (Real.sqrt_pos.mpr hlam₁)
      hb hbn hbx hT hsmooth hd.root_lower hsmall (hd.absorb b hbell) hd.inner_dom hd.outer_dom heta
  have hRK : b*tin ≤ K := hRn.trans hnK
  have hTexp : T ≤ Real.exp (n : ℝ) := by
    calc
      _ = Real.exp (Real.log T) := (Real.exp_log hTp).symm
      _ ≤ _ := Real.exp_le_exp.mpr (hlogT.trans hd.size_dom)
  have hEtaSum : (η b)⁻¹+(η (b*tin))⁻¹ ≤ Real.exp (n : ℝ) := hInv.trans hd.inverse_dom
  have hRate : T*((η b)⁻¹+(η (b*tin))⁻¹) ≤ Real.exp (2*(n : ℝ)) := by
    have hηb := (heta b hb hbn).1
    have hR1 : 1 ≤ b*tin := by nlinarith
    have hηR := (heta (b*tin) hR1 hRn).1
    calc
      _ ≤ Real.exp (n : ℝ)*Real.exp (n : ℝ) :=
        mul_le_mul hTexp hEtaSum (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨hbudget,hbase⟩ := P2MDepth35DegreeBudgets.budgets hd.degree_large htout
    (hS.trans hd.degree_dom) hd.width_dom hd.base_width_dom
  have hwidth := P2MMajorityLiftCounts.width_le F hw (ℓ := ℓ)
  have hwidthF : width F ≤ w := Finset.sup_le hw
  have h41a : Q+max (2*(b*tin)*tout+2*(b*tin)) (b*tin*tout+width (lift F ℓ)) ≤ D := by
    dsimp [Q,D]
    omega
  have h41b : Q+2*width F ≤ D := by dsimp [Q,D]; omega
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by have h := hd.n_large; omega)
  have hN : ((n*ℓ : ℕ) : ℝ) ≤ (n : ℝ)^2 := by
    have hnℓ := Nat.mul_le_mul_left n hd.block_le_n
    exact_mod_cast (show n*ℓ ≤ n^2 by nlinarith)
  exact P2MDepth35FiniteContradiction.no_small_refutation hℓ F b D Q K tin tout htin htout π hπ
    hRK hKN h41a h41b hn1 hN hh he hE hpin hpout hRate

end AC02Frege.P2MDepth35LowerBound
end

end P2MSyntacticRootProof
open AC02Frege MvPolynomial LiftSAParity

theorem solution :
    ∀ c : ℝ, 0 < c → ∀ lam₁ lam₂ : ℝ, 0 < lam₁ → lam₁ ≤ lam₂ →
    ∃ α : ℝ, 0 < α ∧ ∀ w : ℕ, ∃ k n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ F : CNF (Fin n), (∀ C ∈ F, C.card ≤ w) → ¬ PCDerivable F ⌊c * n⌋₊ 1 →
    ∀ ℓ : ℕ, Odd ℓ → lam₁ * Real.log n ≤ ℓ → (ℓ : ℝ) ≤ lam₂ * Real.log n →
      encLength (lift F ℓ) ≤ n ^ k ∧
      ∀ b : ℕ, 1 ≤ b → b ^ 2 ≤ ℓ → ∀ π : List (Line (Fin n × Fin ℓ)),
        IsRefutation b (lift F ℓ) π →
          α * Real.log n ^ ((3 : ℝ) / 2) / b ≤ Real.log (totalSize π)  := by
  exact P2MSyntacticRootProof.AC02Frege.P2MDepth35LowerBound.lower_bound
