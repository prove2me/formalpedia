-- Prove2me | Definitions.Def_FreeGroupFactorProof19
-- name    : FreeGroupFactorProof19
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T04:14:27.858828+00:00
-- url     : https://prove2.me/theorems/d5626ee8-6c0e-4f7a-b792-2fa08b5473c9
-- title:
--   Free group factors: supporting development, part 19
-- statement:
--   Part 19 of the supporting Lean development for the isomorphism of all interpolated free group factors. It continues the chain of earlier parts and contains proved upstream lemmas on the polynomial flow and on corners of the stabilization, with the declarations they rest on, in source order. No result is assumed.
--
--   **Formalization Note** Eight of these lemmas were first published as child theorems, but the platform's target-type check rejected their universe-polymorphic solutions even though the solution type and the published statement have the same elaborated term locally. They are therefore proved here, so that the parent theorems can use them. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

set_option linter.all false

section
namespace OAI

noncomputable section

universe uA uE uι

open Set Metric
open scoped NNReal Topology

open Set Metric
open scoped NNReal Topology
namespace FreeGroupFactorMain

theorem global_solution_of_bounded_lipschitz
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → E) (K L : ℝ≥0) (hf : LipschitzWith K f)
    (hbound : ∀ x, ‖f x‖ ≤ L) (x₀ : E) :
    ∃ X : ℝ → E, X 0 = x₀ ∧ ∀ t, HasDerivAt X (f (X t)) t := by
  have hlocal (R : ℝ) (hR : 0 < R) :
      ∃ X : ℝ → E, X 0 = x₀ ∧
        ∀ t ∈ Ioo (-R) R, HasDerivAt X (f (X t)) t := by
    let r : ℝ≥0 := NNReal.mk R hR.le
    have hp : IsPicardLindelof (fun _ : ℝ => f)
        (⟨0, by constructor <;> linarith⟩ : Icc (-R) R)
        x₀ (L * r) 0 L K := by
      constructor
      · intro t ht
        exact hf.lipschitzOnWith
      · intro x hx
        exact continuousOn_const
      · intro t ht x hx
        exact hbound x
      · simp [r, NNReal.coe_mul]
    obtain ⟨X, hX₀, hX⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    refine ⟨X, hX₀, fun t ht => ?_⟩
    exact (hX t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  choose sol init deriv using hlocal
  have agree (R Q : ℝ) (hR : 0 < R) (hQ : 0 < Q) (t : ℝ)
      (htR : t ∈ Ioo (-R) R) (htQ : t ∈ Ioo (-Q) Q) :
      sol R hR t = sol Q hQ t := by
    have hm : 0 < min R Q := lt_min hR hQ
    have heq : EqOn (sol R hR) (sol Q hQ) (Ioo (-min R Q) (min R Q)) := by
      apply ODE_solution_unique_of_mem_Ioo
        (v := fun _ : ℝ => f) (s := fun _ => univ) (t₀ := 0)
        (fun _ _ => hf.lipschitzOnWith)
        (by constructor <;> linarith) _ _ (by rw [init, init])
      · intro u hu
        refine ⟨deriv R hR u ?_, mem_univ _⟩
        constructor <;> have := min_le_left R Q <;> linarith [hu.1, hu.2]
      · intro u hu
        refine ⟨deriv Q hQ u ?_, mem_univ _⟩
        constructor <;> have := min_le_right R Q <;> linarith [hu.1, hu.2]
    apply heq
    constructor
    · have hh : -t < min R Q := lt_min (by linarith [htR.1]) (by linarith [htQ.1])
      linarith
    · exact lt_min htR.2 htQ.2
  let X : ℝ → E := fun t => sol (|t| + 1) (by positivity) t
  have hEq (R : ℝ) (hR : 0 < R) : EqOn X (sol R hR) (Ioo (-R) R) := by
    intro t ht
    apply agree
    · constructor <;> linarith [neg_abs_le t, le_abs_self t]
    · exact ht
  refine ⟨X, ?_, fun t => ?_⟩
  · exact init _ _
  · let R := |t| + 1
    have hR : 0 < R := by dsimp [R]; positivity
    have ht : t ∈ Ioo (-R) R := by
      dsimp [R]
      constructor <;> linarith [neg_abs_le t, le_abs_self t]
    have hh : X =ᶠ[nhds t] sol R hR :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht) (hEq R hR)
    rw [hEq R hR ht]
    exact (deriv R hR t ht).congr_of_eventuallyEq hh

end FreeGroupFactorMain

open scoped NNReal
namespace FreeGroupFactorMain

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

def radialClip (x : E) : E := (max 1 ‖x‖)⁻¹ • x

theorem radialClip_eq {x : E} (hx : ‖x‖ ≤ 1) : radialClip x = x := by
  simp [radialClip, max_eq_left hx]

theorem norm_radialClip_le (x : E) : ‖radialClip x‖ ≤ 1 := by
  have ha : 0 < max 1 ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [radialClip, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ha]
  simpa only [div_eq_mul_inv, mul_comm] using (div_le_one ha).mpr (le_max_right 1 ‖x‖)

theorem radialClip_lipschitz : LipschitzWith 2 (radialClip : E → E) := by
  have hle (x y : E) (hxy : max 1 ‖y‖ ≤ max 1 ‖x‖) :
      ‖radialClip x - radialClip y‖ ≤ 2 * ‖x - y‖ := by
    let a := max 1 ‖x‖
    let b := max 1 ‖y‖
    have ha1 : 1 ≤ a := le_max_left _ _
    have hb1 : 1 ≤ b := le_max_left _ _
    have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
    have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
    have hba : b ≤ a := hxy
    have hiny : ‖y‖ ≤ b := le_max_right _ _
    have hdiff : a - b ≤ ‖x - y‖ := by
      have := (lipschitzWith_one_norm.const_max 1).dist_le_mul x y
      exact (le_abs_self (a - b)).trans (by simpa [a, b, Real.dist_eq, dist_eq_norm] using this)
    have hinv : a⁻¹ ≤ b⁻¹ := inv_anti₀ hb hba
    have hterm : (b⁻¹ - a⁻¹) * ‖y‖ ≤ a - b := by
      calc
        (b⁻¹ - a⁻¹) * ‖y‖ = (a - b) * (‖y‖ / (a * b)) := by
          field_simp
        _ ≤ (a - b) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hba)
          apply (div_le_one (mul_pos ha hb)).mpr
          exact hiny.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr ha1) hb.le])
        _ = a - b := mul_one _
    have hfirst : a⁻¹ * ‖x - y‖ ≤ ‖x - y‖ :=
      mul_le_of_le_one_left (norm_nonneg _) ((inv_le_one₀ ha).mpr ha1)
    have hid : radialClip x - radialClip y =
        a⁻¹ • (x - y) + (a⁻¹ - b⁻¹) • y := by
      dsimp [radialClip, a, b]
      module
    rw [hid]
    calc
      ‖a⁻¹ • (x - y) + (a⁻¹ - b⁻¹) • y‖ ≤
          ‖a⁻¹ • (x - y)‖ + ‖(a⁻¹ - b⁻¹) • y‖ := norm_add_le _ _
      _ = a⁻¹ * ‖x - y‖ + (b⁻¹ - a⁻¹) * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr ha), abs_of_nonpos (sub_nonpos.mpr hinv)]
        ring
      _ ≤ 2 * ‖x - y‖ := by linarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_ofNat, dist_eq_norm]
  rcases le_total (max 1 ‖y‖) (max 1 ‖x‖) with h | h
  · exact hle x y h
  · simpa only [norm_sub_rev (radialClip y), norm_sub_rev y] using hle y x h

end FreeGroupFactorMain

open scoped NNReal BigOperators
namespace FreeGroupFactorMain

variable {E : Type uE} {A : Type uA} [NormedAddCommGroup E] [NormedRing A]

def BoundedLip (f : E → A) : Prop :=
  ∃ M K : ℝ, 0 ≤ M ∧ 0 ≤ K ∧ (∀ x, ‖f x‖ ≤ M) ∧
    ∀ x y, ‖f x - f y‖ ≤ K * ‖x - y‖

namespace BoundedLip

theorem const (c : A) : BoundedLip (fun _ : E => c) := by
  refine ⟨‖c‖, 0, norm_nonneg _, le_rfl, fun _ => le_rfl, ?_⟩
  intro x y
  simp

theorem add {f g : E → A} (hf : BoundedLip f) (hg : BoundedLip g) :
    BoundedLip (fun x => f x + g x) := by
  obtain ⟨M, K, hM, hK, hfb, hfl⟩ := hf
  obtain ⟨N, L, hN, hL, hgb, hgl⟩ := hg
  refine ⟨M + N, K + L, add_nonneg hM hN, add_nonneg hK hL, ?_, ?_⟩
  · intro x
    exact (norm_add_le _ _).trans (add_le_add (hfb x) (hgb x))
  · intro x y
    rw [show f x + g x - (f y + g y) = (f x - f y) + (g x - g y) by abel]
    exact (norm_add_le _ _).trans (by nlinarith only [hfl x y, hgl x y])

theorem mul {f g : E → A} (hf : BoundedLip f) (hg : BoundedLip g) :
    BoundedLip (fun x => f x * g x) := by
  obtain ⟨M, K, hM, hK, hfb, hfl⟩ := hf
  obtain ⟨N, L, hN, hL, hgb, hgl⟩ := hg
  refine ⟨M * N, M * L + K * N, mul_nonneg hM hN,
    add_nonneg (mul_nonneg hM hL) (mul_nonneg hK hN), ?_, ?_⟩
  · intro x
    exact (norm_mul_le _ _).trans (mul_le_mul (hfb x) (hgb x) (norm_nonneg _) hM)
  · intro x y
    calc
      ‖f x * g x - f y * g y‖ =
          ‖f x * (g x - g y) + (f x - f y) * g y‖ := by
        congr 1
        noncomm_ring
      _ ≤ ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ M * (L * ‖x - y‖) + (K * ‖x - y‖) * N := by
        exact add_le_add
          (mul_le_mul (hfb x) (hgl x y) (norm_nonneg _) hM)
          (mul_le_mul (hfl x y) (hgb y) (norm_nonneg _)
            (mul_nonneg hK (norm_nonneg _)))
      _ = (M * L + K * N) * ‖x - y‖ := by ring

theorem star [StarRing A] [NormedStarGroup A] {f : E → A} (hf : BoundedLip f) :
    BoundedLip (fun x => star (f x)) := by
  obtain ⟨M, K, hM, hK, hfb, hfl⟩ := hf
  refine ⟨M, K, hM, hK, ?_, ?_⟩
  · simpa only [norm_star] using hfb
  · simpa only [← star_sub, norm_star] using hfl

theorem sum {ι : Type uι} (s : Finset ι) (f : ι → E → A)
    (hf : ∀ i ∈ s, BoundedLip (f i)) : BoundedLip (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (E := E) (0 : A))
  | @insert i s hi ih =>
    simpa [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem smul [NormedAlgebra ℂ A] (c : ℂ) {f : E → A} (hf : BoundedLip f) :
    BoundedLip (fun x => c • f x) := by
  simpa only [Algebra.smul_def] using (const (E := E) (algebraMap ℂ A c)).mul hf

theorem pi {ι : Type uι} [Fintype ι] {f : E → ι → A}
    (hf : ∀ i, BoundedLip (fun x => f x i)) : BoundedLip f := by
  classical
  choose M K hM hK hb hl using hf
  have hMs (i : ι) : M i ≤ ∑ j, M j :=
    Finset.single_le_sum (fun j _ => hM j) (Finset.mem_univ i)
  have hKs (i : ι) : K i ≤ ∑ j, K j :=
    Finset.single_le_sum (fun j _ => hK j) (Finset.mem_univ i)
  have hMsum : 0 ≤ ∑ j, M j := Finset.sum_nonneg fun j _ => hM j
  have hKsum : 0 ≤ ∑ j, K j := Finset.sum_nonneg fun j _ => hK j
  refine ⟨∑ j, M j, ∑ j, K j, hMsum, hKsum, ?_, ?_⟩
  · intro x
    exact (pi_norm_le_iff_of_nonneg hMsum).mpr fun i => (hb i x).trans (hMs i)
  · intro x y
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hKsum (norm_nonneg _))).mpr
    intro i
    exact (hl i x y).trans (mul_le_mul_of_nonneg_right (hKs i) (norm_nonneg _))

theorem to_bounds {f : E → A} (hf : BoundedLip f) :
    ∃ M K : ℝ≥0, (∀ x, ‖f x‖ ≤ M) ∧ LipschitzWith K f := by
  obtain ⟨M, K, hM, hK, hb, hl⟩ := hf
  refine ⟨NNReal.mk M hM, NNReal.mk K hK, hb, LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  simpa only [dist_eq_norm, NNReal.coe_mk] using hl x y

end BoundedLip
end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uι

open Set Metric
open scoped NNReal Topology BigOperators

open scoped BigOperators ContDiff
namespace FreeGroupFactorMain
namespace PolynomialFlow

section

variable {A : Type uA} [CStarAlgebra A]
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

 omit [DecidableEq ι] in
 theorem smooth_wordList (w : List (ι × Bool)) :
    ContDiff ℝ ∞ (wordList (A := A) w) := by
  induction w with
  | nil =>
    change ContDiff ℝ ∞ (fun _ : ι → A => (1 : A))
    exact contDiff_const
  | cons a w ih =>
    rcases a with ⟨i, b⟩
    cases b
    · change ContDiff ℝ ∞ (fun X : ι → A => star (X i) * wordList w X)
      exact ((starL ℝ (A := A)).contDiff.comp (contDiff_apply ℝ A i)).mul ih
    · change ContDiff ℝ ∞ (fun X : ι → A => X i * wordList w X)
      exact (contDiff_apply ℝ A i).mul ih

 theorem smooth_word (g : FreeGroup ι) : ContDiff ℝ ∞ (word (A := A) g) :=
  smooth_wordList _

 theorem smooth_hamiltonian (S : A) (h : FreeGroup ι →₀ ℝ) :
    ContDiff ℝ ∞ (hamiltonian S h) := by
  classical
  unfold hamiltonian Finsupp.sum
  apply ContDiff.sum
  intro g hg
  exact (contDiff_const (c := (h g : ℂ))).smul
    (((smooth_word (A := A) g).mul (contDiff_const (c := S))).mul
      ((starL ℝ (A := A)).contDiff.comp (smooth_word (A := A) g)))

 theorem smooth_field (S : A) (h : ι → FreeGroup ι →₀ ℝ) :
    ContDiff ℝ ∞ (field S h) := by
  apply contDiff_pi.mpr
  intro j
  exact (contDiff_const (c := Complex.I)).smul
    ((smooth_hamiltonian S (h j)).mul (contDiff_apply ℝ A j))

 omit [Fintype ι] in
 theorem selfAdjoint_hamiltonian (S : A) (hS : IsSelfAdjoint S)
    (h : FreeGroup ι →₀ ℝ) (X : ι → A) : IsSelfAdjoint (hamiltonian S h X) := by
  classical
  unfold hamiltonian Finsupp.sum
  change star (∑ g ∈ h.support, (h g : ℂ) • (word g X * S * star (word g X))) = _
  simp only [star_sum, star_smul, Complex.star_def, Complex.conj_ofReal, star_mul, star_star, hS.star_eq, mul_assoc]

end

section
open scoped NNReal BigOperators
variable {A : Type uA} [CStarAlgebra A]
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem boundedLip_clip_coordinate (j : ι) :
    BoundedLip (fun X : ι → A => radialClip X j) := by
  refine ⟨1, 2, by positivity, by positivity, ?_, ?_⟩
  · intro X
    exact (norm_le_pi_norm (radialClip X) j).trans (norm_radialClip_le X)
  · intro X Y
    exact (norm_le_pi_norm (radialClip X - radialClip Y) j).trans
      (by simpa only [dist_eq_norm, NNReal.coe_ofNat] using radialClip_lipschitz.dist_le_mul X Y)

omit [DecidableEq ι] in
theorem boundedLip_clip_wordList (w : List (ι × Bool)) :
    BoundedLip (fun X : ι → A => wordList w (radialClip X)) := by
  induction w with
  | nil => exact BoundedLip.const 1
  | cons a w ih =>
    rcases a with ⟨i, b⟩
    cases b
    · exact (boundedLip_clip_coordinate i).star.mul ih
    · exact (boundedLip_clip_coordinate i).mul ih

theorem boundedLip_clip_word (g : FreeGroup ι) :
    BoundedLip (fun X : ι → A => word g (radialClip X)) :=
  boundedLip_clip_wordList _

theorem boundedLip_clip_hamiltonian (S : A) (h : FreeGroup ι →₀ ℝ) :
    BoundedLip (fun X : ι → A => hamiltonian S h (radialClip X)) := by
  classical
  unfold hamiltonian Finsupp.sum
  apply BoundedLip.sum
  intro g hg
  exact ((boundedLip_clip_word g).mul (BoundedLip.const S) |>.mul
    (boundedLip_clip_word g).star).smul (h g : ℂ)

theorem boundedLip_clip_field (S : A) (h : ι → FreeGroup ι →₀ ℝ) :
    BoundedLip (fun X => field S h (radialClip X)) := by
  apply BoundedLip.pi
  intro j
  exact ((boundedLip_clip_hamiltonian S (h j)).mul
    (boundedLip_clip_coordinate j)).smul Complex.I

theorem tangent_clipped (S : A) (hS : IsSelfAdjoint S)
    (h : ι → FreeGroup ι →₀ ℝ) (X : ι → A) (j : ι) :
    star (field S h (radialClip X) j) * X j +
      star (X j) * field S h (radialClip X) j = 0 := by
  let r : ℝ := (max 1 ‖X‖)⁻¹
  have he : radialClip X j = r • X j := rfl
  simp only [field, he, mul_smul_comm, smul_comm Complex.I r, star_smul,
    star_trivial, star_mul, (selfAdjoint_hamiltonian S hS (h j) (radialClip X)).star_eq,
    Complex.star_def, Complex.conj_I, neg_smul, neg_mul, smul_mul_assoc,
    mul_assoc]
  module

theorem global_unitary_solution [Nontrivial A]
    (S : A) (hS : IsSelfAdjoint S) (h : ι → FreeGroup ι →₀ ℝ)
    (V : ι → A) (hV : ∀ j, V j ∈ unitary A) :
    ∃ X : ℝ → ι → A, X 0 = V ∧
      (∀ t, HasDerivAt X (field S h (X t)) t) ∧
      ∀ t j, X t j ∈ unitary A := by
  obtain ⟨M, K, hb, hl⟩ := (boundedLip_clip_field S h).to_bounds
  obtain ⟨X, hX₀, hX⟩ := global_solution_of_bounded_lipschitz
    (fun X => field S h (radialClip X)) K M hl hb V
  have hd (j : ι) (t : ℝ) :
      HasDerivAt (fun u => star (X u j) * X u j) 0 t := by
    have hj := hasDerivAt_pi.mp (hX t) j
    convert! hj.star.mul hj using 1
    exact (tangent_clipped S hS h (X t) j).symm
  have hisom (t : ℝ) (j : ι) : star (X t j) * X t j = 1 := by
    have he := is_const_of_deriv_eq_zero (fun u => (hd j u).differentiableAt)
      (fun u => (hd j u).deriv) t 0
    rw [he, hX₀]
    exact (Unitary.mem_iff.mp (hV j)).1
  have hn (t : ℝ) : ‖X t‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro j
    have he := congrArg norm (hisom t j)
    rw [CStarRing.norm_star_mul_self, norm_one] at he
    nlinarith [norm_nonneg (X t j)]
  have hder (t : ℝ) : HasDerivAt X (field S h (X t)) t := by
    simpa only [radialClip_eq (hn t)] using hX t
  refine ⟨X, hX₀, hder, ?_⟩
  intro t j
  have hc : Continuous (fun u => X u j) :=
    continuous_iff_continuousAt.mpr fun u => (hasDerivAt_pi.mp (hder u) j).continuousAt
  have hset : {u | X u j ∈ unitary A} = {u | IsUnit (X u j)} := by
    ext u
    constructor
    · intro hu
      exact Unitary.isUnit_coe (U := ⟨X u j, hu⟩)
    · exact fun hu => hu.mem_unitary_of_star_mul_self (hisom u j)
  have hcl : IsClosed {u | X u j ∈ unitary A} := isClosed_unitary.preimage hc
  have hop : IsOpen {u | X u j ∈ unitary A} := by
    rw [hset]
    exact Units.isOpen.preimage hc
  have hall := (IsClopen.eq_univ ⟨hcl, hop⟩ ⟨0, by change X 0 j ∈ unitary A; rw [hX₀]; exact hV j⟩)
  exact (show t ∈ {u | X u j ∈ unitary A} from by rw [hall]; trivial)

end

variable {A : Type uA} [CStarAlgebra A]
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem smooth_solution (S : A) (h : ι → FreeGroup ι →₀ ℝ)
    (X : ℝ → ι → A) (hX : ∀ t, HasDerivAt X (field S h (X t)) t) :
    ContDiff ℝ ∞ X := by
  have hdiff : Differentiable ℝ X := fun t => (hX t).differentiableAt
  apply contDiff_infty.mpr
  intro n
  induction n with
  | zero => exact contDiff_zero.mpr hdiff.continuous
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
    refine ⟨hdiff, by simp, ?_⟩
    have heq : deriv X = fun t => field S h (X t) := funext fun t => (hX t).deriv
    rw [heq]
    exact (contDiff_infty.mp (smooth_field S h) n).comp ih

omit [DecidableEq ι] in
theorem norm_unitary_tuple_le [Nontrivial A] (V : ι → A)
    (hV : ∀ j, V j ∈ unitary A) : ‖V‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  exact (CStarRing.norm_of_mem_unitary (hV j)).le

theorem unitary_solutions_unique [Nontrivial A]
    (S : A) (h : ι → FreeGroup ι →₀ ℝ) (X Y : ℝ → ι → A)
    (hX : ∀ t, HasDerivAt X (field S h (X t)) t)
    (hY : ∀ t, HasDerivAt Y (field S h (Y t)) t)
    (hUX : ∀ t j, X t j ∈ unitary A) (hUY : ∀ t j, Y t j ∈ unitary A)
    (t₀ : ℝ) (hinit : X t₀ = Y t₀) : X = Y := by
  obtain ⟨M, K, _hb, hl⟩ := (boundedLip_clip_field S h).to_bounds
  funext t
  let R := |t| + |t₀| + 1
  have ht : t ∈ Set.Ioo (-R) R := by
    dsimp [R]
    constructor <;> linarith [neg_abs_le t, le_abs_self t, abs_nonneg t₀]
  have ht₀ : t₀ ∈ Set.Ioo (-R) R := by
    dsimp [R]
    constructor <;> linarith [neg_abs_le t₀, le_abs_self t₀, abs_nonneg t]
  have heq : Set.EqOn X Y (Set.Ioo (-R) R) := by
    apply ODE_solution_unique_of_mem_Ioo
      (v := fun _ Z => field S h (radialClip Z)) (s := fun _ => Set.univ) (t₀ := t₀)
      (fun _ _ => hl.lipschitzOnWith) ht₀ _ _ hinit
    · intro u _
      rw [radialClip_eq (norm_unitary_tuple_le _ (hUX u))]
      exact ⟨hX u, Set.mem_univ _⟩
    · intro u _
      rw [radialClip_eq (norm_unitary_tuple_le _ (hUY u))]
      exact ⟨hY u, Set.mem_univ _⟩
  exact heq ht

end PolynomialFlow
end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uι

open Set Metric
open scoped NNReal Topology BigOperators ContDiff

open scoped BigOperators ContDiff
namespace FreeGroupFactorMain
namespace NCPolynomial

inductive Expr (ι : Type uι) where
  | scalar : ℂ → Expr ι
  | gen : ι → Expr ι
  | add : Expr ι → Expr ι → Expr ι
  | mul : Expr ι → Expr ι → Expr ι

def degree {ι : Type uι} : Expr ι → ℕ
  | .scalar _ => 0
  | .gen _ => 1
  | .add p q => max (degree p) (degree q)
  | .mul p q => degree p + degree q

def mass {ι : Type uι} : Expr ι → ℝ
  | .scalar c => ‖c‖
  | .gen _ => 1
  | .add p q => mass p + mass q
  | .mul p q => mass p * mass q

def eval {ι : Type uι} {A : Type uA} [Semiring A] [Algebra ℂ A] (X : ι → A) : Expr ι → A
  | .scalar c => algebraMap ℂ A c
  | .gen i => X i
  | .add p q => eval X p + eval X q
  | .mul p q => eval X p * eval X q

def delta {ι : Type uι} (V : ι → Expr ι) : Expr ι → Expr ι
  | .scalar _ => .scalar 0
  | .gen i => V i
  | .add p q => .add (delta V p) (delta V q)
  | .mul p q => .add (.mul (delta V p) q) (.mul p (delta V q))

 theorem mass_nonneg {ι : Type uι} (p : Expr ι) : 0 ≤ mass p := by
  induction p with
  | scalar c => exact norm_nonneg _
  | gen i => exact zero_le_one
  | add p q hp hq => exact add_nonneg hp hq
  | mul p q hp hq => exact mul_nonneg hp hq

 theorem degree_delta {ι : Type uι} (V : ι → Expr ι) (J : ℕ)
    (hV : ∀ i, degree (V i) ≤ J + 1) (p : Expr ι) :
    degree (delta V p) ≤ degree p + J := by
  induction p with
  | scalar c => simp [delta, degree]
  | gen i => simpa [delta, degree, Nat.add_comm] using hV i
  | add p q hp hq =>
    simp only [delta, degree]
    omega
  | mul p q hp hq =>
    simp only [delta, degree]
    omega

 theorem mass_delta {ι : Type uι} (V : ι → Expr ι) (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ i, mass (V i) ≤ B) (p : Expr ι) :
    mass (delta V p) ≤ mass p * (degree p : ℝ) * B := by
  induction p with
  | scalar c => simp [delta, mass, degree]
  | gen i => simpa [delta, mass, degree] using hV i
  | add p q hp hq =>
    simp only [delta, mass, degree]
    have hl : (degree p : ℝ) ≤ (max (degree p) (degree q) : ℕ) := by exact_mod_cast le_max_left _ _
    have hr : (degree q : ℝ) ≤ (max (degree p) (degree q) : ℕ) := by exact_mod_cast le_max_right _ _
    calc
      mass (delta V p) + mass (delta V q) ≤
          mass p * (degree p : ℝ) * B + mass q * (degree q : ℝ) * B := add_le_add hp hq
      _ ≤ mass p * (max (degree p) (degree q) : ℕ) * B +
          mass q * (max (degree p) (degree q) : ℕ) * B := by
        gcongr
        · exact mass_nonneg p
        · exact mass_nonneg q
      _ = _ := by ring
  | mul p q hp hq =>
    simp only [delta, mass, degree, Nat.cast_add]
    calc
      mass (delta V p) * mass q + mass p * mass (delta V q) ≤
          (mass p * (degree p : ℝ) * B) * mass q +
          mass p * (mass q * (degree q : ℝ) * B) := by
        exact add_le_add (mul_le_mul_of_nonneg_right hp (mass_nonneg q))
          (mul_le_mul_of_nonneg_left hq (mass_nonneg p))
      _ = _ := by ring

 theorem degree_iterate {ι : Type uι} (V : ι → Expr ι) (J : ℕ)
    (hV : ∀ i, degree (V i) ≤ J + 1) (p : Expr ι) (r : ℕ) :
    degree ((delta V)^[r] p) ≤ degree p + r * J := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact (degree_delta V J hV _).trans (by simpa [Nat.add_mul, Nat.add_assoc] using Nat.add_le_add_right ih J)

 theorem mass_iterate {ι : Type uι} (V : ι → Expr ι) (J : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hdeg : ∀ i, degree (V i) ≤ J + 1) (hmass : ∀ i, mass (V i) ≤ B)
    (p : Expr ι) (r : ℕ) :
    mass ((delta V)^[r] p) ≤
      mass p * (B * ((degree p : ℝ) + J)) ^ r * (r.factorial : ℝ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    have hd : (degree ((delta V)^[r] p) : ℝ) ≤ ((degree p : ℝ) + J) * (r + 1) := by
      have := degree_iterate V J hdeg p r
      have hh : (degree ((delta V)^[r] p) : ℝ) ≤ (degree p : ℝ) + r * J := by exact_mod_cast this
      nlinarith [Nat.cast_nonneg (α := ℝ) (degree p)]
    calc
      mass (delta V ((delta V)^[r] p)) ≤
          mass ((delta V)^[r] p) * (degree ((delta V)^[r] p) : ℝ) * B :=
        mass_delta V B hB hmass _
      _ ≤ (mass p * (B * ((degree p : ℝ) + J)) ^ r * (r.factorial : ℝ)) *
          (((degree p : ℝ) + J) * (r + 1)) * B := by
        gcongr
        exact mul_nonneg (mul_nonneg (mass_nonneg p) (pow_nonneg (mul_nonneg hB (by positivity)) _)) (by positivity)
      _ = _ := by simp [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add]; ring

 theorem norm_eval {ι : Type uι} {A : Type uA} [NormedRing A] [NormedAlgebra ℂ A] [NormOneClass A]
    (X : ι → A) (R : ℝ) (hR : 1 ≤ R) (hX : ∀ i, ‖X i‖ ≤ R) (p : Expr ι) :
    ‖eval X p‖ ≤ mass p * R ^ degree p := by
  induction p with
  | scalar c => simp [eval, mass, degree, norm_algebraMap']
  | gen i => simpa [eval, mass, degree] using hX i
  | add p q hp hq =>
    simp only [eval, mass, degree]
    calc
      ‖eval X p + eval X q‖ ≤ ‖eval X p‖ + ‖eval X q‖ := norm_add_le _ _
      _ ≤ mass p * R ^ degree p + mass q * R ^ degree q := add_le_add hp hq
      _ ≤ mass p * R ^ max (degree p) (degree q) +
          mass q * R ^ max (degree p) (degree q) := by
        gcongr
        · exact mass_nonneg p
        · exact le_max_left _ _
        · exact mass_nonneg q
        · exact le_max_right _ _
      _ = _ := by ring
  | mul p q hp hq =>
    simp only [eval, mass, degree, pow_add]
    calc
      ‖eval X p * eval X q‖ ≤ ‖eval X p‖ * ‖eval X q‖ := norm_mul_le _ _
      _ ≤ (mass p * R ^ degree p) * (mass q * R ^ degree q) := by
        exact mul_le_mul hp hq (norm_nonneg _) (mul_nonneg (mass_nonneg _) (pow_nonneg (by linarith) _))
      _ = _ := by ring

 theorem hasDerivAt_eval {ι : Type uι} {A : Type uA} [NormedRing A] [NormedAlgebra ℂ A]
    (X : ℝ → ι → A) (V : ι → Expr ι) (t : ℝ)
    (hX : ∀ i, HasDerivAt (fun s => X s i) (eval (X t) (V i)) t) (p : Expr ι) :
    HasDerivAt (fun s => eval (X s) p) (eval (X t) (delta V p)) t := by
  induction p with
  | scalar c => simpa [eval, delta] using hasDerivAt_const t (algebraMap ℂ A c)
  | gen i => exact hX i
  | add p q hp hq => exact hp.add hq
  | mul p q hp hq => exact hp.mul hq

theorem norm_eval_iterate {ι : Type uι} {A : Type uA} [NormedRing A] [NormedAlgebra ℂ A]
    [NormOneClass A] (X : ι → A) (R : ℝ) (hR : 1 ≤ R) (hX : ∀ i, ‖X i‖ ≤ R)
    (V : ι → Expr ι) (J : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hdeg : ∀ i, degree (V i) ≤ J + 1) (hmass : ∀ i, mass (V i) ≤ B)
    (p : Expr ι) (r : ℕ) :
    ‖eval X ((delta V)^[r] p)‖ ≤
      (mass p * R ^ degree p) * (B * ((degree p : ℝ) + J) * R ^ J) ^ r *
        (r.factorial : ℝ) := by
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  calc
    ‖eval X ((delta V)^[r] p)‖ ≤ mass ((delta V)^[r] p) * R ^ degree ((delta V)^[r] p) :=
      norm_eval X R hR hX _
    _ ≤ (mass p * (B * ((degree p : ℝ) + J)) ^ r * (r.factorial : ℝ)) *
        R ^ (degree p + r * J) := by
      apply mul_le_mul (mass_iterate V J B hB hdeg hmass p r)
      · exact pow_le_pow_right₀ hR (degree_iterate V J hdeg p r)
      · exact pow_nonneg hR0 _
      · exact mul_nonneg (mul_nonneg (mass_nonneg p) (pow_nonneg (mul_nonneg hB (by positivity)) _)) (by positivity)
    _ = _ := by simp only [pow_add, mul_pow, ← pow_mul]; rw [Nat.mul_comm r J]; ring

theorem smooth_eval {ι : Type uι} {A : Type uA} [NormedRing A] [NormedAlgebra ℂ A]
    (X : ℝ → ι → A) (hX : ∀ i, ContDiff ℝ ∞ (fun t => X t i)) (p : Expr ι) :
    ContDiff ℝ ∞ (fun t => eval (X t) p) := by
  induction p with
  | scalar c => exact contDiff_const
  | gen i => exact hX i
  | add p q hp hq => exact hp.add hq
  | mul p q hp hq => exact hp.mul hq

end NCPolynomial
end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uB uG uι

open Set Metric
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain
namespace TraceCocycle

abbrev CF (G : Type uG) := G →₀ ℂ

def shift {G : Type uG} [Group G] (g : G) : CF G ≃+ CF G :=
  Finsupp.domCongr (MulAut.conj g).toEquiv

@[simp] theorem shift_apply {G : Type uG} [Group G] (g : G) (p : CF G) (b : G) :
    shift g p b = p (g⁻¹ * b * g) := rfl

@[simp] theorem shift_one {G : Type uG} [Group G] (p : CF G) : shift (1 : G) p = p := by
  ext b
  simp

@[simp] theorem shift_mul {G : Type uG} [Group G] (g b : G) (p : CF G) :
    shift (g * b) p = shift g (shift b p) := by
  ext c
  simp [mul_assoc]

def action (G : Type uG) [Group G] : G →* MulAut (Multiplicative (CF G)) where
  toFun g := AddEquiv.toMultiplicative (shift g)
  map_one' := by
    apply MulEquiv.ext
    intro p
    exact shift_one p.toAdd
  map_mul' g b := by
    apply MulEquiv.ext
    intro p
    exact shift_mul g b p.toAdd

def graph {ι : Type uι} (h : ι → CF (FreeGroup ι)) :
    FreeGroup ι →* (Multiplicative (CF (FreeGroup ι)) ⋊[action (FreeGroup ι)] FreeGroup ι) :=
  FreeGroup.lift (fun i => ⟨Multiplicative.ofAdd (h i), FreeGroup.of i⟩)

@[simp] theorem graph_right {ι : Type uι} (h : ι → CF (FreeGroup ι)) (g : FreeGroup ι) :
    (graph h g).right = g := by
  have hr : SemidirectProduct.rightHom.comp (graph h) = MonoidHom.id _ := by
    ext i
    simp [graph]
  exact DFunLike.congr_fun hr g

def cocycle {ι : Type uι} (h : ι → CF (FreeGroup ι)) (g : FreeGroup ι) : CF (FreeGroup ι) :=
  (graph h g).left.toAdd

@[simp] theorem cocycle_of {ι : Type uι} (h : ι → CF (FreeGroup ι)) (i : ι) :
    cocycle h (FreeGroup.of i) = h i := by
  simp [cocycle, graph]

@[simp] theorem cocycle_one {ι : Type uι} (h : ι → CF (FreeGroup ι)) : cocycle h 1 = 0 := by
  simp [cocycle]

theorem cocycle_mul {ι : Type uι} (h : ι → CF (FreeGroup ι)) (g b : FreeGroup ι) :
    cocycle h (g * b) = cocycle h g + shift g (cocycle h b) := by
  unfold cocycle
  rw [map_mul, SemidirectProduct.mul_left, graph_right]
  rfl

theorem cocycle_inv {ι : Type uι} (h : ι → CF (FreeGroup ι)) (g : FreeGroup ι) :
    cocycle h g⁻¹ = -shift g⁻¹ (cocycle h g) := by
  have he := cocycle_mul h g⁻¹ g
  simp only [inv_mul_cancel, cocycle_one] at he
  exact eq_neg_of_add_eq_zero_left he.symm

def traceDerivative {ι : Type uι} (h : ι → CF (FreeGroup ι)) (g : FreeGroup ι) : ℂ :=
  cocycle h g g⁻¹

theorem traceDerivative_conjugate {ι : Type uι} (h : ι → CF (FreeGroup ι))
    (a g : FreeGroup ι) :
    traceDerivative h (a * g * a⁻¹) = traceDerivative h g := by
  simp only [traceDerivative, cocycle_mul, cocycle_inv, shift_apply,
    Finsupp.add_apply, Finsupp.neg_apply, mul_inv_rev, inv_inv]
  simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  ring

def CyclicConjugate {G : Type uG} [Group G] (c b : G) : Prop :=
  ∃ (a : G) (k : ℤ), b = a * c ^ k * a⁻¹

theorem CyclicConjugate.conj {G : Type uG} [Group G] {c b : G}
    (hb : CyclicConjugate c b) (g : G) : CyclicConjugate c (g * b * g⁻¹) := by
  obtain ⟨a, k, rfl⟩ := hb
  exact ⟨g * a, k, by simp [mul_assoc]⟩

theorem CyclicConjugate.inv {G : Type uG} [Group G] {c b : G}
    (hb : CyclicConjugate c b) : CyclicConjugate c b⁻¹ := by
  obtain ⟨a, k, rfl⟩ := hb
  exact ⟨a, -k, by simp [mul_assoc]⟩

def SupportedOn {G : Type uG} (P : G → Prop) (p : CF G) : Prop :=
  ∀ b, ¬P b → p b = 0

@[simp] theorem supported_zero {G : Type uG} (P : G → Prop) : SupportedOn P (0 : CF G) := by
  intro b hb
  rfl

theorem supported_add {G : Type uG} {P : G → Prop} {p q : CF G}
    (hp : SupportedOn P p) (hq : SupportedOn P q) : SupportedOn P (p + q) := by
  intro b hb
  simp [hp b hb, hq b hb]

theorem supported_neg {G : Type uG} {P : G → Prop} {p : CF G}
    (hp : SupportedOn P p) : SupportedOn P (-p) := by
  intro b hb
  simp [hp b hb]

theorem supported_shift {G : Type uG} [Group G] {c : G} {p : CF G}
    (hp : SupportedOn (CyclicConjugate c) p) (g : G) :
    SupportedOn (CyclicConjugate c) (shift g p) := by
  intro b hb
  apply hp
  intro h
  have := h.conj g
  apply hb
  simpa [mul_assoc] using this

end TraceCocycle
end FreeGroupFactorMain

namespace FreeGroupFactorMain.TraceCocycle

 theorem cocycle_supported {ι : Type uι} (h : ι → CF (FreeGroup ι)) (c : FreeGroup ι)
    (hh : ∀ i, SupportedOn (CyclicConjugate c) (h i)) (g : FreeGroup ι) :
    SupportedOn (CyclicConjugate c) (cocycle h g) := by
  induction g using FreeGroup.induction_on with
  | C1 => simp
  | of i => simpa using hh i
  | inv_of g hg => rw [cocycle_inv]; exact supported_neg (supported_shift hg _)
  | mul g b hg hb => rw [cocycle_mul]; exact supported_add hg (supported_shift hb _)

 theorem cocycle_pow_zero {ι : Type uι} (h : ι → CF (FreeGroup ι)) (c : FreeGroup ι)
    (hc : cocycle h c = 0) (k : ℕ) : cocycle h (c ^ k) = 0 := by
  induction k with
  | zero => simp
  | succ k ih => simp [pow_succ, cocycle_mul, ih, hc]

 theorem cocycle_zpow_zero {ι : Type uι} (h : ι → CF (FreeGroup ι)) (c : FreeGroup ι)
    (hc : cocycle h c = 0) (k : ℤ) : cocycle h (c ^ k) = 0 := by
  cases k with
  | ofNat k => simpa using cocycle_pow_zero h c hc k
  | negSucc k => simp [zpow_negSucc, cocycle_inv, cocycle_pow_zero h c hc]

 theorem universalGroupTraceIdentity {ι : Type uι} (h : ι → CF (FreeGroup ι)) (c : ι)
    (hh : ∀ i, SupportedOn (CyclicConjugate (FreeGroup.of c)) (h i))
    (hc : h c = 0) (g : FreeGroup ι) : traceDerivative h g = 0 := by
  classical
  by_cases hg : CyclicConjugate (FreeGroup.of c) g
  · obtain ⟨a, k, rfl⟩ := hg
    rw [traceDerivative_conjugate, traceDerivative,
      cocycle_zpow_zero h _ (by simpa using hc)]
    rfl
  · apply cocycle_supported h (FreeGroup.of c) hh g
    intro hginv
    exact hg (by simpa using hginv.inv)

def rightShift {G : Type uG} [Group G] (g : G) : CF G ≃ₗ[ℂ] CF G :=
  Finsupp.domLCongr (Equiv.mulRight g)

@[simp] theorem rightShift_apply {G : Type uG} [Group G] (g : G) (p : CF G) (b : G) :
    rightShift g p b = p (b * g⁻¹) := rfl

def polynomialDerivative {ι : Type uι} (h : ι → CF (FreeGroup ι)) :
    CF (FreeGroup ι) →ₗ[ℂ] CF (FreeGroup ι) :=
  Finsupp.linearCombination ℂ (fun g => rightShift g (cocycle h g))

@[simp] theorem polynomialDerivative_single {ι : Type uι} (h : ι → CF (FreeGroup ι))
    (g : FreeGroup ι) (a : ℂ) :
    polynomialDerivative h (Finsupp.single g a) = a • rightShift g (cocycle h g) := by
  simp [polynomialDerivative]

 theorem polynomialDerivative_trace_zero {ι : Type uι} (h : ι → CF (FreeGroup ι)) (c : ι)
    (hh : ∀ i, SupportedOn (CyclicConjugate (FreeGroup.of c)) (h i))
    (hc : h c = 0) (p : CF (FreeGroup ι)) : (polynomialDerivative h p) 1 = 0 := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | single g a =>
    simp only [polynomialDerivative_single, Finsupp.smul_apply, smul_eq_mul,
      rightShift_apply, one_mul]
    change a * traceDerivative h g = 0
    rw [universalGroupTraceIdentity h c hh hc, mul_zero]

def algebraDerivative {ι : Type uι} (h : ι → CF (FreeGroup ι)) :
    MonoidAlgebra ℂ (FreeGroup ι) →ₗ[ℂ] MonoidAlgebra ℂ (FreeGroup ι) :=
  (MonoidAlgebra.coeffLinearEquiv ℂ).symm.toLinearMap ∘ₗ
    polynomialDerivative h ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

@[simp] theorem algebraDerivative_coeff {ι : Type uι} (h : ι → CF (FreeGroup ι))
    (p : MonoidAlgebra ℂ (FreeGroup ι)) :
    (algebraDerivative h p).coeff = polynomialDerivative h p.coeff := rfl

@[simp] theorem algebraDerivative_of_coeff {ι : Type uι} (h : ι → CF (FreeGroup ι))
    (g : FreeGroup ι) (b : FreeGroup ι) :
    (algebraDerivative h (MonoidAlgebra.of ℂ (FreeGroup ι) g)).coeff b =
      cocycle h g (b * g⁻¹) := by
  simp [MonoidAlgebra.of_apply]

theorem algebraDerivative_mul_of {ι : Type uι} (h : ι → CF (FreeGroup ι))
    (g b : FreeGroup ι) :
    algebraDerivative h (MonoidAlgebra.of ℂ (FreeGroup ι) g *
      MonoidAlgebra.of ℂ (FreeGroup ι) b) =
      algebraDerivative h (MonoidAlgebra.of ℂ (FreeGroup ι) g) *
        MonoidAlgebra.of ℂ (FreeGroup ι) b +
      MonoidAlgebra.of ℂ (FreeGroup ι) g *
        algebraDerivative h (MonoidAlgebra.of ℂ (FreeGroup ι) b) := by
  rw [← map_mul]
  ext x
  simp [MonoidAlgebra.of_apply, cocycle_mul, mul_assoc]

theorem algebraDerivative_mul {ι : Type uι} (h : ι → CF (FreeGroup ι))
    (p q : MonoidAlgebra ℂ (FreeGroup ι)) :
    algebraDerivative h (p * q) = algebraDerivative h p * q + p * algebraDerivative h q := by
  induction p using MonoidAlgebra.induction_on with
  | of g =>
    induction q using MonoidAlgebra.induction_on with
    | of b => exact algebraDerivative_mul_of h g b
    | add q₁ q₂ ih₁ ih₂ => simp only [mul_add, map_add, ih₁, ih₂]; abel
    | smul r q ih => simp only [mul_smul_comm, map_smul, ih, smul_add]
  | add p₁ p₂ ih₁ ih₂ => simp only [add_mul, map_add, ih₁, ih₂]; abel
  | smul r p ih => simp only [smul_mul_assoc, map_smul, ih, smul_add]

def laurent {G : Type uG} [Group G] (c : G) (l : ℤ →₀ ℂ) : CF G :=
  Finsupp.linearCombination ℂ (fun k => Finsupp.single (c ^ k) 1) l

theorem supported_smul {G : Type uG} {P : G → Prop} {p : CF G}
    (hp : SupportedOn P p) (a : ℂ) : SupportedOn P (a • p) := by
  intro b hb
  simp [hp b hb]

theorem laurent_supported {G : Type uG} [Group G] (c : G) (l : ℤ →₀ ℂ) :
    SupportedOn (CyclicConjugate c) (laurent c l) := by
  classical
  induction l using Finsupp.induction_linear with
  | zero => simp [laurent]
  | add p q hp hq => simpa only [laurent, map_add] using supported_add hp hq
  | single k a =>
    simp only [laurent, Finsupp.linearCombination_single]
    apply supported_smul
    intro b hb
    apply Finsupp.single_eq_of_ne
    intro heq
    apply hb
    exact ⟨1, k, by simpa using heq⟩

def fieldCoefficients {ι : Type uι} (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ) :
    Option ι → CF (FreeGroup (Option ι))
  | none => 0
  | some i => (h i).sum fun g a => ((a : ℂ) * Complex.I) •
      shift (FreeGroup.map Option.some g) (laurent (FreeGroup.of none) l)

theorem fieldCoefficients_supported {ι : Type uι} (h : ι → FreeGroup ι →₀ ℝ)
    (l : ℤ →₀ ℂ) (i : Option ι) :
    SupportedOn (CyclicConjugate (FreeGroup.of none)) (fieldCoefficients h l i) := by
  classical
  cases i with
  | none => exact supported_zero _
  | some i =>
    intro b hb
    simp only [fieldCoefficients, Finsupp.sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro g hg
    exact supported_smul (supported_shift (laurent_supported _ _) _) _ b hb

theorem sourceLaurentTraceIdentity {ι : Type uι} (h : ι → FreeGroup ι →₀ ℝ)
    (l : ℤ →₀ ℂ) (p : MonoidAlgebra ℂ (FreeGroup (Option ι))) (r : ℕ) :
    ((algebraDerivative (fieldCoefficients h l))^[r + 1] p).coeff 1 = 0 := by
  rw [Function.iterate_succ_apply', algebraDerivative_coeff]
  exact polynomialDerivative_trace_zero _ none (fieldCoefficients_supported h l) rfl _

end FreeGroupFactorMain.TraceCocycle

namespace FreeGroupFactorMain
namespace AlgebraPolynomial
open NCPolynomial

def signed {ι : Type uι} (ib : ι × Bool) : FreeGroup ι :=
  if ib.2 then FreeGroup.of ib.1 else (FreeGroup.of ib.1)⁻¹

def wordExpr {ι : Type uι} : List (ι × Bool) → Expr (ι × Bool)
  | [] => .scalar 1
  | a :: w => .mul (.gen a) (wordExpr w)

theorem eval_wordExpr {ι : Type uι} {A : Type uA} [Semiring A] [Algebra ℂ A]
    (ρ : FreeGroup ι →* A) (w : List (ι × Bool)) :
    eval (fun ib => ρ (signed ib)) (wordExpr w) = ρ (FreeGroup.mk w) := by
  induction w with
  | nil => simp [wordExpr, eval, ← FreeGroup.one_eq_mk]
  | cons a w ih =>
    rcases a with ⟨i, b⟩
    change ρ (signed (i, b)) * eval (fun ib => ρ (signed ib)) (wordExpr w) = _
    rw [ih, ← map_mul]
    cases b <;> rfl

def groupExpr {ι : Type uι} [DecidableEq ι] (g : FreeGroup ι) : Expr (ι × Bool) :=
  wordExpr g.toWord

theorem eval_groupExpr {ι : Type uι} {A : Type uA} [DecidableEq ι] [Semiring A] [Algebra ℂ A]
    (ρ : FreeGroup ι →* A) (g : FreeGroup ι) :
    eval (fun ib => ρ (signed ib)) (groupExpr g) = ρ g := by
  rw [groupExpr, eval_wordExpr, FreeGroup.mk_toWord]

def sumExpr {ι : Type uι} : List (Expr ι) → Expr ι
  | [] => .scalar 0
  | p :: ps => .add p (sumExpr ps)

theorem eval_sumExpr {ι : Type uι} {A : Type uA} [Semiring A] [Algebra ℂ A]
    (X : ι → A) (ps : List (Expr ι)) :
    eval X (sumExpr ps) = (ps.map (eval X)).sum := by
  induction ps with
  | nil => simp [sumExpr, eval]
  | cons p ps ih => simp [sumExpr, eval, ih]

def encode {ι : Type uι} [DecidableEq ι] (p : MonoidAlgebra ℂ (FreeGroup ι)) :
    Expr (ι × Bool) :=
  sumExpr (p.coeff.support.toList.map fun g => .mul (.scalar (p.coeff g)) (groupExpr g))

theorem eval_encode {ι : Type uι} [DecidableEq ι] (p : MonoidAlgebra ℂ (FreeGroup ι)) :
    eval (fun ib => MonoidAlgebra.of ℂ (FreeGroup ι) (signed ib)) (encode p) = p := by
  classical
  rw [encode, eval_sumExpr, List.map_map]
  simp only [Function.comp_def, eval]
  simp_rw [eval_groupExpr]
  simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    MonoidAlgebra.of_apply, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  rw [Finset.sum_map_toList]
  simpa only [Finsupp.sum] using (MonoidAlgebra.sum_coeff_single p)

def encodedField {ι : Type uι} [DecidableEq ι]
    (h : ι → TraceCocycle.CF (FreeGroup ι)) (ib : ι × Bool) : Expr (ι × Bool) :=
  encode (TraceCocycle.algebraDerivative h (MonoidAlgebra.of ℂ (FreeGroup ι) (signed ib)))

theorem algebraDerivative_one {ι : Type uι} (h : ι → TraceCocycle.CF (FreeGroup ι)) :
    TraceCocycle.algebraDerivative h 1 = 0 := by
  have he := TraceCocycle.algebraDerivative_mul h 1 1
  simp only [one_mul, mul_one] at he
  exact (add_eq_left.mp he.symm)

theorem eval_delta_encoded {ι : Type uι} [DecidableEq ι]
    (h : ι → TraceCocycle.CF (FreeGroup ι)) (p : Expr (ι × Bool)) :
    eval (fun ib => MonoidAlgebra.of ℂ (FreeGroup ι) (signed ib))
      (delta (encodedField h) p) =
    TraceCocycle.algebraDerivative h
      (eval (fun ib => MonoidAlgebra.of ℂ (FreeGroup ι) (signed ib)) p) := by
  induction p with
  | scalar c =>
    simp only [delta, eval, Algebra.algebraMap_eq_smul_one, map_smul,
      algebraDerivative_one, smul_zero, zero_smul]
  | gen ib => exact eval_encode _
  | add p q hp hq => simp only [delta, eval, hp, hq, map_add]
  | mul p q hp hq => simp only [delta, eval, hp, hq, TraceCocycle.algebraDerivative_mul]

theorem map_eval {ι : Type uι} {A : Type uA} {B : Type uB} [Semiring A] [Semiring B]
    [Algebra ℂ A] [Algebra ℂ B] (φ : A →ₐ[ℂ] B) (X : ι → A) (p : Expr ι) :
    φ (eval X p) = eval (fun i => φ (X i)) p := by
  induction p with
  | scalar c => exact φ.commutes c
  | gen i => rfl
  | add p q hp hq => simp only [eval, map_add, hp, hq]
  | mul p q hp hq => simp only [eval, map_mul, hp, hq]

theorem encoded_initial_trace {ι : Type uι} [DecidableEq ι]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ) (p : Expr ((Option ι) × Bool)) :
    (eval (fun ib => MonoidAlgebra.of ℂ (FreeGroup (Option ι)) (signed ib))
      (delta (encodedField (TraceCocycle.fieldCoefficients h l)) p)).coeff 1 = 0 := by
  rw [eval_delta_encoded]
  exact TraceCocycle.sourceLaurentTraceIdentity h l _ 0

end AlgebraPolynomial
end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uG uι

open Set Metric
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain
namespace UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A]
variable {ι : Type uι}

theorem wordHom_word [DecidableEq ι]
    (U : ι → unitary A) (g : FreeGroup ι) :
    wordHom U g = PolynomialFlow.word g (fun i => (U i : A)) := by
  conv_lhs => rw [← FreeGroup.mk_toWord (x := g)]
  change ((FreeGroup.lift U (FreeGroup.mk g.toWord) : unitary A) : A) = _
  rw [FreeGroup.lift_mk]
  rw [Submonoid.coe_list_prod]
  simp only [List.map_map, Function.comp_def]
  unfold PolynomialFlow.word PolynomialFlow.wordList
  apply congrArg List.prod
  apply List.map_congr_left
  intro ib _
  rcases ib with ⟨i, b⟩
  cases b <;> rfl

def algebraHom (U : ι → unitary A) : MonoidAlgebra ℂ (FreeGroup ι) →ₐ[ℂ] A :=
  MonoidAlgebra.lift ℂ A (FreeGroup ι) (wordHom U)

@[simp] theorem algebraHom_of (U : ι → unitary A) (g : FreeGroup ι) :
    algebraHom U (MonoidAlgebra.of ℂ (FreeGroup ι) g) = wordHom U g := by
  simp [algebraHom]

@[simp] theorem eval_encode [DecidableEq ι]
    (U : ι → unitary A) (p : MonoidAlgebra ℂ (FreeGroup ι)) :
    NCPolynomial.eval (fun ib => wordHom U (AlgebraPolynomial.signed ib))
      (AlgebraPolynomial.encode p) = algebraHom U p := by
  calc
    _ = algebraHom U (NCPolynomial.eval
        (fun ib => MonoidAlgebra.of ℂ (FreeGroup ι) (AlgebraPolynomial.signed ib))
        (AlgebraPolynomial.encode p)) := by
      rw [AlgebraPolynomial.map_eval]
      congr 1
      funext ib
      exact (algebraHom_of U _).symm
    _ = algebraHom U p := by rw [AlgebraPolynomial.eval_encode]

theorem algebraHom_ofCoeff (U : ι → unitary A) (p : FreeGroup ι →₀ ℂ) :
    algebraHom U (MonoidAlgebra.ofCoeff p) = coefficientHom (wordHom U) p := by
  simp [algebraHom, MonoidAlgebra.lift_apply, coefficientHom, Finsupp.linearCombination_apply]

theorem coefficientHom_shift {G : Type uG} [Group G] (ρ : G →* A)
    (g : G) (p : G →₀ ℂ) :
    coefficientHom ρ (TraceCocycle.shift g p) =
      ρ g * coefficientHom ρ p * ρ g⁻¹ := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [map_add, hp, hq, mul_add, add_mul]
  | single b c =>
    have hs : TraceCocycle.shift g (Finsupp.single b c) =
        Finsupp.single (g * b * g⁻¹) c := by
      simp only [TraceCocycle.shift, Finsupp.domCongr_apply,
        Finsupp.equivMapDomain_eq_mapDomain, Finsupp.mapDomain_single]
      rfl
    rw [hs, coefficientHom_single, coefficientHom_single]
    simp only [map_mul, smul_mul_assoc, mul_smul_comm]

theorem derivative_of (h : ι → TraceCocycle.CF (FreeGroup ι)) (g : FreeGroup ι) :
    TraceCocycle.algebraDerivative h (MonoidAlgebra.of ℂ (FreeGroup ι) g) =
      MonoidAlgebra.ofCoeff (TraceCocycle.cocycle h g) *
        MonoidAlgebra.of ℂ (FreeGroup ι) g := by
  ext b
  simp [MonoidAlgebra.of_apply]

theorem eval_derivative_of (U : ι → unitary A)
    (h : ι → TraceCocycle.CF (FreeGroup ι)) (g : FreeGroup ι) :
    algebraHom U (TraceCocycle.algebraDerivative h (MonoidAlgebra.of ℂ (FreeGroup ι) g)) =
      coefficientHom (wordHom U) (TraceCocycle.cocycle h g) * wordHom U g := by
  rw [derivative_of, map_mul, algebraHom_ofCoeff, algebraHom_of]

theorem eval_encodedField_pos [DecidableEq ι] (U : ι → unitary A)
    (h : ι → TraceCocycle.CF (FreeGroup ι)) (i : ι) :
    NCPolynomial.eval (fun ib => wordHom U (AlgebraPolynomial.signed ib))
      (AlgebraPolynomial.encodedField h (i, true)) =
      coefficientHom (wordHom U) (h i) * (U i : A) := by
  rw [AlgebraPolynomial.encodedField, eval_encode, eval_derivative_of]
  simp only [AlgebraPolynomial.signed, ↓reduceIte, TraceCocycle.cocycle_of, wordHom_of]

theorem eval_encodedField_neg [DecidableEq ι] (U : ι → unitary A)
    (h : ι → TraceCocycle.CF (FreeGroup ι)) (i : ι) :
    NCPolynomial.eval (fun ib => wordHom U (AlgebraPolynomial.signed ib))
      (AlgebraPolynomial.encodedField h (i, false)) =
      -(star (U i : A) * coefficientHom (wordHom U) (h i)) := by
  rw [AlgebraPolynomial.encodedField, eval_encode, eval_derivative_of]
  simp only [AlgebraPolynomial.signed, Bool.false_eq_true, ↓reduceIte,
    TraceCocycle.cocycle_inv, TraceCocycle.cocycle_of, map_neg, coefficientHom_shift,
    wordHom_inv, inv_inv, wordHom_of, neg_mul]
  rw [mul_assoc, mul_assoc, (U i).property.2, mul_one]

end UnitaryEvaluation
end FreeGroupFactorMain

namespace FreeGroupFactorMain.UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

@[simp] theorem coefficientHom_laurent (U : ι → unitary A) (C : unitary A) (l : ℤ →₀ ℂ) :
    coefficientHom (wordHom (extendUnitary U C))
      (TraceCocycle.laurent (FreeGroup.of none) l) = laurentValue C l := by
  induction l using Finsupp.induction_linear with
  | zero => simp [TraceCocycle.laurent, laurentValue]
  | add p q hp hq => simpa [TraceCocycle.laurent, laurentValue, map_add] using congrArg₂ (· + ·) hp hq
  | single k c =>
    simp only [TraceCocycle.laurent, Finsupp.linearCombination_single, map_smul,
      coefficientHom_single, one_smul, laurentValue]
    congr 1
    change ((FreeGroup.lift (extendUnitary U C) (FreeGroup.of none ^ k) : unitary A) : A) = _
    rw [map_zpow, FreeGroup.lift_apply_of]
    rfl

 theorem coefficientHom_fieldCoefficients [DecidableEq ι]
    (U : ι → unitary A) (C : unitary A) (h : ι → FreeGroup ι →₀ ℝ)
    (l : ℤ →₀ ℂ) (i : ι) :
    coefficientHom (wordHom (extendUnitary U C)) (TraceCocycle.fieldCoefficients h l (some i)) =
      Complex.I • PolynomialFlow.hamiltonian (laurentValue C l) (h i) (fun j => (U j : A)) := by
  classical
  simp only [TraceCocycle.fieldCoefficients, PolynomialFlow.hamiltonian, Finsupp.sum,
    map_sum, map_smul, coefficientHom_shift, coefficientHom_laurent,
    wordHom_inv, wordHom_extend, Finset.smul_sum]
  simp only [wordHom_word]
  apply Finset.sum_congr rfl
  intro g hg
  rw [smul_smul, mul_comm]

def signedTrajectory (X : ℝ → ι → A) (hU : ∀ t j, X t j ∈ unitary A)
    (C : unitary A) (t : ℝ) (ib : Option ι × Bool) : A :=
  wordHom (extendUnitary (fun j => ⟨X t j, hU t j⟩) C) (AlgebraPolynomial.signed ib)

 theorem signedTrajectory_some_pos (X : ℝ → ι → A) (hU : ∀ t j, X t j ∈ unitary A)
    (C : unitary A) (t : ℝ) (i : ι) :
    signedTrajectory X hU C t (some i, true) = X t i := by
  simp [signedTrajectory, AlgebraPolynomial.signed, extendUnitary]

 theorem signedTrajectory_some_neg (X : ℝ → ι → A) (hU : ∀ t j, X t j ∈ unitary A)
    (C : unitary A) (t : ℝ) (i : ι) :
    signedTrajectory X hU C t (some i, false) = star (X t i) := by
  simp [signedTrajectory, AlgebraPolynomial.signed, extendUnitary]

 theorem signedTrajectory_none_pos (X : ℝ → ι → A) (hU : ∀ t j, X t j ∈ unitary A)
    (C : unitary A) (t : ℝ) :
    signedTrajectory X hU C t (none, true) = C := by
  simp [signedTrajectory, AlgebraPolynomial.signed, extendUnitary]

 theorem signedTrajectory_none_neg (X : ℝ → ι → A) (hU : ∀ t j, X t j ∈ unitary A)
    (C : unitary A) (t : ℝ) :
    signedTrajectory X hU C t (none, false) = star (C : A) := by
  simp [signedTrajectory, AlgebraPolynomial.signed, extendUnitary]

 theorem signedTrajectory_ode [Fintype ι] [DecidableEq ι]
    (C : unitary A) (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue C l))
    (X : ℝ → ι → A) (hU : ∀ t j, X t j ∈ unitary A)
    (hX : ∀ t, HasDerivAt X (PolynomialFlow.field (laurentValue C l) h (X t)) t)
    (t : ℝ) (ib : Option ι × Bool) :
    HasDerivAt (fun s => signedTrajectory X hU C s ib)
      (NCPolynomial.eval (signedTrajectory X hU C t)
        (AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l) ib)) t := by
  have hpos (j : Option ι) : NCPolynomial.eval (signedTrajectory X hU C t)
      (AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l) (j,true)) =
      coefficientHom (wordHom (extendUnitary (fun j => ⟨X t j, hU t j⟩) C))
        (TraceCocycle.fieldCoefficients h l j) *
        (extendUnitary (fun j => ⟨X t j,hU t j⟩) C j : A) :=
    eval_encodedField_pos _ _ _
  have hneg (j : Option ι) : NCPolynomial.eval (signedTrajectory X hU C t)
      (AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l) (j,false)) =
      -(star (extendUnitary (fun j => ⟨X t j,hU t j⟩) C j : A) *
        coefficientHom (wordHom (extendUnitary (fun j => ⟨X t j, hU t j⟩) C))
          (TraceCocycle.fieldCoefficients h l j)) :=
    eval_encodedField_neg _ _ _
  rcases ib with ⟨i,b⟩
  cases i with
  | none =>
    cases b
    · rw [hneg]
      simp only [TraceCocycle.fieldCoefficients, map_zero, mul_zero, neg_zero]
      simpa only [signedTrajectory_none_neg] using hasDerivAt_const t (star (C : A))
    · rw [hpos]
      simp only [TraceCocycle.fieldCoefficients, map_zero, zero_mul]
      simpa only [signedTrajectory_none_pos] using hasDerivAt_const t (C : A)
  | some i =>
    have hi := hasDerivAt_pi.mp (hX t) i
    cases b
    · rw [hneg, coefficientHom_fieldCoefficients]
      have hs := hi.star
      have he : star (PolynomialFlow.field (laurentValue C l) h (X t) i) =
          -(star (X t i) * (Complex.I • PolynomialFlow.hamiltonian (laurentValue C l) (h i) (X t))) := by
        simp only [PolynomialFlow.field, star_smul, star_mul, Complex.star_def,
          Complex.conj_I, (PolynomialFlow.selfAdjoint_hamiltonian _ hS _ _).star_eq,
          neg_smul, mul_smul_comm]
      rw [he] at hs
      simpa only [signedTrajectory_some_neg, extendUnitary, Option.elim_some] using hs
    · rw [hpos, coefficientHom_fieldCoefficients]
      simpa only [signedTrajectory_some_pos, extendUnitary, Option.elim_some,
        PolynomialFlow.field, smul_mul_assoc] using hi

end FreeGroupFactorMain.UnitaryEvaluation

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

open scoped Topology ContDiff
open Set Filter
namespace FreeGroupFactorMain

theorem flat_local_of_factorial_bound (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (B c : ℝ) (_hB : 0 ≤ B) (hc : 0 < c)
    (hbound : ∀ r t, |iteratedDeriv r f t| ≤ B * c ^ r * (r.factorial : ℝ))
    (a : ℝ) (ha : ∀ r, iteratedDeriv (r + 1) f a = 0)
    (x : ℝ) (hx : c * |x - a| < 1) : f x = f a := by
  by_cases hax : a = x
  · simp [hax]
  have htaylor (n : ℕ) : taylorWithinEval f n (uIcc a x) a x = f a := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [taylorWithinEval_succ, ih,
        iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hax)
          ((hf.of_le (by exact_mod_cast (le_top : ((n + 1 : ℕ) : ℕ∞) ≤ ⊤))).contDiffAt)
          (left_mem_uIcc), ha n]
      simp
  have hest (n : ℕ) : |f x - f a| ≤ B * (c * |x - a|) ^ (n + 1) := by
    obtain ⟨y, _, hy⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hax
      ((hf.of_le (by exact_mod_cast (le_top : ((n + 1 : ℕ) : ℕ∞) ≤ ⊤))).contDiffOn)
    rw [htaylor] at hy
    have hfpos : (0 : ℝ) < ((n + 1).factorial : ℝ) := by positivity
    calc
      |f x - f a| = |iteratedDeriv (n + 1) f y| * |x - a| ^ (n + 1) /
          ((n + 1).factorial : ℝ) := by rw [hy, abs_div, abs_mul, abs_pow, abs_of_pos hfpos]
      _ ≤ (B * c ^ (n + 1) * ((n + 1).factorial : ℝ)) * |x - a| ^ (n + 1) /
          ((n + 1).factorial : ℝ) := by gcongr; exact hbound _ _
      _ = B * (c * |x - a|) ^ (n + 1) := by rw [mul_pow]; field_simp
  have hlim : Tendsto (fun n : ℕ => B * (c * |x - a|) ^ (n + 1)) atTop (nhds 0) := by
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg hc.le (abs_nonneg _)) hx)
    simpa using (hp.comp (tendsto_add_atTop_nat 1)).const_mul B
  have hz : |f x - f a| ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hest)
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hz)

theorem flat_global_of_factorial_bound (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (B c : ℝ) (hB : 0 ≤ B) (hc : 0 < c)
    (hbound : ∀ r t, |iteratedDeriv r f t| ≤ B * c ^ r * (r.factorial : ℝ))
    (ha : ∀ r, iteratedDeriv (r + 1) f 0 = 0) (x : ℝ) : f x = f 0 := by
  let Z : Set ℝ := {a | ∀ r, iteratedDeriv (r + 1) f a = 0}
  have hclosed : IsClosed Z := by
    change IsClosed {a | ∀ r, iteratedDeriv (r + 1) f a = 0}
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro r
    exact isClosed_eq (hf.continuous_iteratedDeriv (r + 1) (by exact_mod_cast (le_top : ((r + 1 : ℕ) : ℕ∞) ≤ ⊤))) continuous_const
  have hopen : IsOpen Z := by
    apply isOpen_iff_mem_nhds.mpr
    intro a ha
    have hδ : 0 < c⁻¹ := inv_pos.mpr hc
    apply Filter.mem_of_superset (Metric.ball_mem_nhds a hδ)
    intro y hy
    have heq : f =ᶠ[nhds y] (fun _ => f a) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hy] with z hz
      apply flat_local_of_factorial_bound f hf B c hB hc hbound a ha z
      rw [Metric.mem_ball, Real.dist_eq] at hz
      have := mul_lt_mul_of_pos_left hz hc
      simpa [ne_of_gt hc] using this
    intro r
    rw [heq.iteratedDeriv_eq (r + 1)]
    simp [iteratedDeriv_const]
  have hall : Z = univ := (show IsClopen Z from ⟨hclosed, hopen⟩).eq_univ ⟨0, ha⟩
  have hderiv (a : ℝ) : deriv f a = 0 := by
    have hz : a ∈ Z := hall ▸ mem_univ a
    simpa using hz 0
  exact isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ
    (fun a _ => ((hf.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).differentiable (by simp)).differentiableOn a (mem_univ a))
    (fun a _ => hderiv a) (mem_univ x) (mem_univ 0)

namespace NCPolynomial

theorem iteratedDeriv_moment {ι : Type uι} {A : Type uA} [NormedRing A] [NormedAlgebra ℂ A]
    (X : ℝ → ι → A) (V : ι → Expr ι) (L : A →L[ℝ] ℝ)
    (hX : ∀ t i, HasDerivAt (fun s => X s i) (eval (X t) (V i)) t)
    (p : Expr ι) (r : ℕ) :
    iteratedDeriv r (fun t => L (eval (X t) p)) =
      fun t => L (eval (X t) ((delta V)^[r] p)) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [Function.iterate_succ_apply']
    convert! (L.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_eval X V t (hX t) ((delta V)^[r] p))).deriv using 1

theorem polynomial_moments {ι : Type uι} {A : Type uA} [NormedRing A] [NormedAlgebra ℂ A]
    [NormOneClass A] (X : ℝ → ι → A) (V : ι → Expr ι) (L : A →L[ℝ] ℝ)
    (hsmooth : ∀ i, ContDiff ℝ ∞ (fun t => X t i))
    (hX : ∀ t i, HasDerivAt (fun s => X s i) (eval (X t) (V i)) t)
    (R : ℝ) (hR : 1 ≤ R) (hbounded : ∀ t i, ‖X t i‖ ≤ R)
    (J : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hdeg : ∀ i, degree (V i) ≤ J + 1) (hmass : ∀ i, mass (V i) ≤ B)
    (htrace : ∀ p, L (eval (X 0) (delta V p)) = 0)
    (p : Expr ι) (t : ℝ) : L (eval (X t) p) = L (eval (X 0) p) := by
  let b := ‖L‖ * (mass p * R ^ degree p)
  let c := B * ((degree p : ℝ) + J) * R ^ J + 1
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hbase : 0 ≤ B * ((degree p : ℝ) + J) * R ^ J := by positivity
  have hb : 0 ≤ b := mul_nonneg (norm_nonneg _) (mul_nonneg (mass_nonneg _) (pow_nonneg hR0 _))
  have hc : 0 < c := by dsimp [c]; linarith
  apply flat_global_of_factorial_bound (fun t => L (eval (X t) p)) (L.contDiff.comp (smooth_eval X hsmooth p)) b c hb hc
  · intro r u
    rw [iteratedDeriv_moment X V L hX]
    calc
      |L (eval (X u) ((delta V)^[r] p))| ≤ ‖L‖ * ‖eval (X u) ((delta V)^[r] p)‖ :=
        L.le_opNorm _
      _ ≤ ‖L‖ * ((mass p * R ^ degree p) *
          (B * ((degree p : ℝ) + J) * R ^ J) ^ r * (r.factorial : ℝ)) := by
        gcongr
        exact norm_eval_iterate (X u) R hR (hbounded u) V J B hB hdeg hmass p r
      _ ≤ b * c ^ r * (r.factorial : ℝ) := by
        dsimp [b]
        calc
          _ = (‖L‖ * (mass p * R ^ degree p)) *
              (B * ((degree p : ℝ) + J) * R ^ J) ^ r * (r.factorial : ℝ) := by ring
          _ ≤ _ := by
            gcongr
            dsimp [c]; linarith
  · intro r
    rw [iteratedDeriv_moment X V L hX, Function.iterate_succ_apply']
    exact htrace _

end NCPolynomial
end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uG uH

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

open scoped ENNReal

def rightRegular {G : Type uG} [Group G] (g : G) : GroupOperator G :=
  (hilbertReindex (Equiv.mulRight g⁻¹)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem rightRegular_apply {G : Type uG} [Group G] (g : G)
    (ξ : GroupHilbert G) (h : G) : rightRegular g ξ h = ξ (h * g) := by
  simp [rightRegular]

@[simp] theorem rightRegular_star {G : Type uG} [Group G] (g : G) :
    star (rightRegular g) = rightRegular g⁻¹ := by
  change star ((hilbertReindex (Equiv.mulRight g⁻¹)) : GroupOperator G) = _
  rw [LinearIsometryEquiv.star_eq_symm]
  ext ξ b
  change ξ (b * g⁻¹) = rightRegular g⁻¹ ξ b
  rw [rightRegular_apply]

theorem left_right_commute {G : Type uG} [Group G] (g h : G) :
    leftRegular g * rightRegular h = rightRegular h * leftRegular g := by
  ext ξ b
  simp [mul_assoc]

theorem rightRegular_mem_commutant {G : Type uG} [Group G] (g : G) :
    rightRegular g ∈ StarSubalgebra.centralizer ℂ (leftTranslations G) := by
  rw [StarSubalgebra.mem_centralizer_iff, leftTranslations_eq_range]
  rintro _ ⟨h, rfl⟩
  exact ⟨left_right_commute h g, by simp only [leftRegular_star]; exact left_right_commute _ _⟩

theorem groupVN_commute_right {G : Type uG} [Group G] (T : groupVonNeumann G) (g : G) :
    rightRegular g * (T : GroupOperator G) = (T : GroupOperator G) * rightRegular g :=
  ((StarSubalgebra.mem_centralizer_iff ℂ).mp T.property _ (rightRegular_mem_commutant g)).1

theorem groupVN_separating {G : Type uG} [Group G] [DecidableEq G] (T : groupVonNeumann G)
    (hT : (T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ)) = 0) : T = 0 := by
  classical
  have hr (g : G) : rightRegular g⁻¹ (lp.single 2 (1 : G) (1 : ℂ)) = lp.single 2 g 1 := by
    ext b
    simp [lp.single_apply, Pi.single_apply, mul_inv_eq_one]
  have hsingle (g : G) : (T : GroupOperator G) (lp.single 2 g 1) = 0 := by
    rw [← hr g]
    have hc := congrArg (fun f : GroupOperator G => f (lp.single 2 (1 : G) (1 : ℂ)))
      (groupVN_commute_right T g⁻¹)
    simpa [hT] using hc.symm
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro ξ
  have hs := ((lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) ξ).mapL (T : GroupOperator G))
  have hz (g : G) : (T : GroupOperator G) (lp.single 2 g (ξ g)) = 0 := by
    have he : lp.single (E := fun _ : G => ℂ) 2 g (ξ g) = (ξ g) • lp.single (E := fun _ : G => ℂ) 2 g (1 : ℂ) := by
      ext b
      simp [lp.single_apply, Pi.single_apply]
    rw [he, map_smul, hsingle, smul_zero]
  simp only [hz] at hs
  exact HasSum.unique hs hasSum_zero

theorem canonicalTrace_eq_inner {G : Type uG} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) :
    canonicalTrace T = inner ℂ (lp.single 2 (1 : G) (1 : ℂ))
      ((T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))) := by
  classical
  simp only [canonicalTrace, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
  apply congrArg (fun v : GroupHilbert G => ((T : GroupOperator G) v) 1)
  ext b
  simp [lp.single_apply, Pi.single_apply]

theorem canonicalTrace_star_mul {G : Type uG} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) :
    canonicalTrace (star T * T) =
      (‖(T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))‖ ^ 2 : ℂ) := by
  rw [canonicalTrace_eq_inner]
  change inner ℂ (lp.single 2 (1 : G) (1 : ℂ))
    (star (T : GroupOperator G) ((T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ)))) = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq_to_K _

def canonicalTraceLinear {G : Type uG} [Group G] : groupVonNeumann G →ₗ[ℂ] ℂ where
  toFun := canonicalTrace
  map_add' T U := by simp [canonicalTrace]
  map_smul' c T := by simp [canonicalTrace]

theorem norm_canonicalTrace_le {G : Type uG} [Group G] (T : groupVonNeumann G) :
    ‖canonicalTrace T‖ ≤ ‖T‖ := by
  classical
  rw [canonicalTrace_eq_inner]
  calc
    ‖inner ℂ (lp.single 2 (1 : G) (1 : ℂ))
        ((T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ)))‖ ≤
        ‖lp.single (E := fun _ : G => ℂ) 2 (1 : G) (1 : ℂ)‖ *
        ‖(T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))‖ := norm_inner_le_norm _ _
    _ ≤ ‖lp.single (E := fun _ : G => ℂ) 2 (1 : G) (1 : ℂ)‖ *
        (‖(T : GroupOperator G)‖ * ‖lp.single (E := fun _ : G => ℂ) 2 (1 : G) (1 : ℂ)‖) := by
      gcongr
      exact (T : GroupOperator G).le_opNorm _
    _ = ‖T‖ := by simp

end FreeGroupFactorMain

end

end OAI
end


