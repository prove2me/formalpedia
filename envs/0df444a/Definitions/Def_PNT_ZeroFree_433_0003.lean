-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0003
-- name    : PNT_ZeroFree_433_0003
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T12:01:28.073606+00:00
-- url     : https://prove2.me/theorems/a0a35697-0ab0-442b-9b95-389ae2aaab9c
-- title:
--   Zero-free region foundations: Mellin.LogProfiles [0003]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Mellin.LogProfiles
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L13-L1539

import Definitions.Def_PNT_ZeroFree_433_0002

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L13-L1539
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Mellin.LogProfiles
section
namespace OAI

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology

namespace ShortDraftMellin

theorem mobiusExpSum_continuousOn_pos
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ContinuousOn (mobiusExpSum χ) (Set.Ioi (0 : ℝ)) := by
  intro t ht
  change 0 < t at ht
  let δ : ℝ := t / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδt : δ < t := by dsimp [δ]; linarith
  have hexp : Summable (fun n : ℕ => Real.exp (-(n : ℝ) * δ)) := by
    convert! (Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hδ)) using 1
    ext n
    congr 1
    ring
  have hcontTerm (n : ℕ) : ContinuousOn
      (fun u : ℝ => χ n * (ArithmeticFunction.moebius n : ℂ) *
        Real.exp (-(n : ℝ) * u)) (Set.Ici δ) := by
    fun_prop
  have hcoeff (n : ℕ) :
      ‖χ n * (ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rw [norm_mul]
    have hχ : ‖χ n‖ ≤ 1 := χ.norm_le_one _
    have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
    nlinarith [mul_nonneg (sub_nonneg.mpr hχ)
      (norm_nonneg ((ArithmeticFunction.moebius n : ℂ))),
      mul_nonneg (sub_nonneg.mpr hμ) (norm_nonneg (χ n))]
  have hbound (n : ℕ) (u : ℝ) (hu : u ∈ Set.Ici δ) :
      ‖χ n * (ArithmeticFunction.moebius n : ℂ) *
        Real.exp (-(n : ℝ) * u)‖ ≤
      Real.exp (-(n : ℝ) * δ) := by
    have hnu : -(n : ℝ) * u ≤ -(n : ℝ) * δ := by
      have hu' : δ ≤ u := hu
      nlinarith [mul_le_mul_of_nonneg_left hu'
        (Nat.cast_nonneg (α := ℝ) n)]
    have hexpmon := Real.exp_le_exp.mpr hnu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      ‖χ n * (ArithmeticFunction.moebius n : ℂ)‖ *
          Real.exp (-(n : ℝ) * u) ≤
          1 * Real.exp (-(n : ℝ) * u) :=
        mul_le_mul_of_nonneg_right (hcoeff n) (Real.exp_pos _).le
      _ ≤ Real.exp (-(n : ℝ) * δ) := by simpa using hexpmon
  have hcontHalf : ContinuousOn (mobiusExpSum χ) (Set.Ici δ) := by
    change ContinuousOn
      (fun u : ℝ => ∑' n : ℕ,
        χ n * (ArithmeticFunction.moebius n : ℂ) *
          Real.exp (-(n : ℝ) * u)) (Set.Ici δ)
    exact continuousOn_tsum hcontTerm hexp hbound
  exact (hcontHalf.continuousAt (Ici_mem_nhds hδt)).continuousWithinAt

theorem mobiusExpSum_inv_continuousOn_pos
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ContinuousOn (fun D : ℝ => mobiusExpSum χ D⁻¹) (Set.Ioi 0) := by
  apply (mobiusExpSum_continuousOn_pos χ).comp
    (continuousOn_inv₀.mono (by
      intro D hD
      exact ne_of_gt hD))
  intro D hD
  exact inv_pos.mpr (show 0 < D from hD)

theorem mobiusExpSum_inv_locallyIntegrableOn_pos
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    LocallyIntegrableOn
      (fun D : ℝ => mobiusExpSum χ D⁻¹) (Set.Ioi 0) :=
  (mobiusExpSum_inv_continuousOn_pos χ).locallyIntegrableOn measurableSet_Ioi

theorem dirichlet_exp_zero_free_of_power_bound_only
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (σ : ℝ) (hσpos : 0 < σ) (hσ : σ < 1)
    (htop : (fun D : ℝ => mobiusExpSum χ D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (ρ : ℂ) (hρ : σ < ρ.re) : χ.LFunction ρ ≠ 0 := by
  exact dirichlet_exp_zero_free_of_power_bound χ hχ σ hσpos hσ
    (mobiusExpSum_inv_locallyIntegrableOn_pos χ) htop
    (mobiusExpSum_flat_at_zero χ) ρ hρ

theorem principal_dirichlet_exp_zero_free_of_power_bound_only
    (q : ℕ) [NeZero q]
    (σ : ℝ) (hσpos : 0 < σ) (hσ : σ < 1)
    (htop : (fun D : ℝ => mobiusExpSum
        (1 : DirichletCharacter ℂ q) D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) ρ ≠ 0 := by
  let U : Set ℂ := {s | σ < s.re}
  have hopen : IsOpen U := Complex.isOpen_re_gt σ
  have hLregular : AnalyticOnNhd ℂ
      (DirichletCharacter.LFunctionTrivChar₁ q) U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (DirichletCharacter.differentiable_LFunctionTrivChar₁ q).differentiableOn
  have hM : AnalyticOnNhd ℂ
      (fun s : ℂ => mellin
        (fun D : ℝ => mobiusExpSum (1 : DirichletCharacter ℂ q) D⁻¹) (-s)) U :=
    inverse_mellin_analytic_of_flat _ σ
      (mobiusExpSum_inv_locallyIntegrableOn_pos 1) htop
      (mobiusExpSum_flat_at_zero 1)
  have hW : AnalyticOnNhd ℂ Complex.Gamma U := by
    apply (Complex.analyticOnNhd_iff_differentiableOn hopen).2
    intro s hs
    apply (Complex.differentiableAt_Gamma s ?_).differentiableWithinAt
    intro m hm
    have hreal : s.re = -(m : ℝ) := by
      simpa using congrArg Complex.re hm
    have hspos : 0 < s.re := lt_trans hσpos hs
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hregular : ∀ s : ℂ, σ < s.re → s ≠ 1 →
      DirichletCharacter.LFunctionTrivChar₁ q s =
        (s - 1) * DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ q) s := by
    intro s _ hs
    simp [DirichletCharacter.LFunctionTrivChar₁,
      DirichletCharacter.LFunctionTrivChar, Function.update_of_ne hs]
  have heq : ∀ s : ℂ, 1 < s.re →
      DirichletCharacter.LFunctionTrivChar₁ q s *
        mellin (fun D : ℝ => mobiusExpSum
          (1 : DirichletCharacter ℂ q) D⁻¹) (-s) =
        (s - 1) * Complex.Gamma s := by
    intro s hs
    rw [hregular s (lt_trans hσ hs) (by
      intro h; subst s; norm_num at hs)]
    rw [mul_assoc, dirichlet_exp_mellin_identity 1 s hs]
  have hWρ : Complex.Gamma ρ ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (lt_trans hσpos hρ)
  exact ShortDraft.zero_free_of_regularized_analytic_identity σ hσ
    (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
    (DirichletCharacter.LFunctionTrivChar₁ q)
    (fun s => mellin (fun D : ℝ => mobiusExpSum
      (1 : DirichletCharacter ℂ q) D⁻¹) (-s))
    Complex.Gamma hLregular hM hW hregular heq ρ hρ hρone hWρ

def ExponentialMobiusPowerBound : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ : ℝ),
    (23 / 24 : ℝ) < σ → σ < 1 →
      (fun D : ℝ => mobiusExpSum χ D⁻¹) =O[atTop]
        (fun D : ℝ => D ^ σ)

theorem dirichletTarget_of_exponentialMobiusPowerBound
    (hbound : ExponentialMobiusPowerBound) : ShortDraft.DirichletTarget := by
  intro q _ χ s h23 hprincipal
  by_cases hs : s.re < 1
  · let σ : ℝ := ((23 / 24 : ℝ) + s.re) / 2
    have hσ23 : (23 / 24 : ℝ) < σ := by dsimp [σ]; linarith
    have hσs : σ < s.re := by dsimp [σ]; linarith
    have hσone : σ < 1 := lt_trans hσs hs
    have hσpos : 0 < σ := lt_trans (by norm_num : (0 : ℝ) < 23 / 24) hσ23
    by_cases hχ : χ = 1
    · subst χ
      have hsone : s ≠ 1 := by
        intro h; exact hprincipal ⟨rfl, h⟩
      exact principal_dirichlet_exp_zero_free_of_power_bound_only q σ
        hσpos hσone (hbound q 1 σ hσ23 hσone) s hσs hsone
    · exact dirichlet_exp_zero_free_of_power_bound_only χ hχ σ
        hσpos hσone (hbound q χ σ hσ23 hσone) s hσs
  · exact ShortDraft.dirichlet_target_of_one_le_re q χ s
      (le_of_not_gt hs) hprincipal

end ShortDraftMellin

namespace FiniteRingSieve

variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]

noncomputable local instance : Fintype (MulChar R ℂ) := Fintype.ofFinite _

omit [DecidableEq R] in
private theorem sum_chars_zero {a : R} (ha : a ≠ 1) :
    (∑ χ : MulChar R ℂ, χ a) = 0 := by
  obtain ⟨χ, hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity R ℂ ha
  refine eq_zero_of_mul_eq_self_left hχ ?_
  simp only [Finset.mul_sum, ← MulChar.mul_apply]
  exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun χ' => rfl

theorem sum_chars (a : R) :
    (∑ χ : MulChar R ℂ, χ a) =
      if a = 1 then (Fintype.card Rˣ : ℂ) else 0 := by
  split_ifs with ha
  · subst a
    simp only [map_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have hc : Fintype.card (MulChar R ℂ) = Fintype.card Rˣ := by
      simpa only [Nat.card_eq_fintype_card] using
        MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity R ℂ
    exact_mod_cast hc
  · exact sum_chars_zero ha

theorem unit_char_orthogonal (u v : Rˣ) :
    (∑ χ : MulChar R ℂ, star (χ (u : R)) * χ (v : R)) =
      if u = v then (Fintype.card Rˣ : ℂ) else 0 := by
  calc
    _ = ∑ χ : MulChar R ℂ, χ ((u⁻¹ * v : Rˣ) : R) := by
      apply Finset.sum_congr rfl
      intro χ _
      rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit,
        Units.val_mul, map_mul]
    _ = if ((u⁻¹ * v : Rˣ) : R) = 1 then (Fintype.card Rˣ : ℂ) else 0 :=
      sum_chars _
    _ = _ := by simp only [Units.val_eq_one, inv_mul_eq_one]

theorem complete_character_plancherel (a : Rˣ → ℂ) :
    (∑ χ : MulChar R ℂ, ‖∑ u : Rˣ, a u * χ (u : R)‖ ^ 2) =
      (Fintype.card Rˣ : ℝ) * ∑ u : Rˣ, ‖a u‖ ^ 2 := by
  classical
  have hnorm (χ : MulChar R ℂ) :
      (↑(‖∑ u : Rˣ, a u * χ (u : R)‖ ^ 2) : ℂ) =
        (∑ u : Rˣ, star (a u) * star (χ (u : R))) *
          (∑ v : Rˣ, a v * χ (v : R)) := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    simp only [map_sum, map_mul, starRingEnd_apply]
  apply Complex.ofReal_inj.mp
  rw [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_sum]
  simp_rw [hnorm]
  calc
    (∑ χ : MulChar R ℂ,
        (∑ u : Rˣ, star (a u) * star (χ (u : R))) *
          (∑ v : Rˣ, a v * χ (v : R))) =
      ∑ u : Rˣ, ∑ v : Rˣ,
        (star (a u) * a v) *
          ∑ χ : MulChar R ℂ, star (χ (u : R)) * χ (v : R) := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        congr 1
        funext u
        rw [Finset.sum_comm]
        congr 1
        funext v
        calc
          (∑ χ : MulChar R ℂ,
              star (a u) * star (χ (u : R)) * (a v * χ (v : R))) =
            ∑ χ : MulChar R ℂ,
              (star (a u) * a v) * (star (χ (u : R)) * χ (v : R)) := by
              apply Finset.sum_congr rfl
              intro χ _
              ring
          _ = _ := by rfl
    _ = (Fintype.card Rˣ : ℂ) * ∑ u : Rˣ, (↑(‖a u‖ ^ 2) : ℂ) := by
        simp_rw [unit_char_orthogonal]
        simp_rw [mul_ite]
        simp only [mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        simp [Complex.sq_norm, Complex.normSq_eq_conj_mul_self, Finset.mul_sum,
          mul_comm, mul_left_comm]

end FiniteRingSieve

namespace FiniteFieldSieve

variable {F : Type*} [Field F] [Fintype F]

private theorem complex_sum_cauchy {ι : Type*} (S : Finset ι) (x y : ι → ℂ) :
    ‖∑ i ∈ S, x i * y i‖ ^ 2 ≤
      (∑ i ∈ S, ‖x i‖ ^ 2) * ∑ i ∈ S, ‖y i‖ ^ 2 := by
  have htri : ‖∑ i ∈ S, x i * y i‖ ≤ ∑ i ∈ S, ‖x i‖ * ‖y i‖ := by
    simpa only [norm_mul] using norm_sum_le S (fun i => x i * y i)
  have hsquare := (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg
      (fun i hi => mul_nonneg (norm_nonneg _) (norm_nonneg _)))).mpr htri
  exact hsquare.trans (Finset.sum_mul_sq_le_sq_mul_sq S (fun i => ‖x i‖)
    (fun i => ‖y i‖))

private theorem character_norm_le_one (χ : MulChar F ℂ) (u : F) : ‖χ u‖ ≤ 1 := by
  let : Fintype Fˣ := Fintype.ofFinite _
  by_cases hu : u = 0
  · rw [hu, MulChar.map_zero]
    simp
  · let v : Fˣ := Units.mk0 u hu
    have hv : (v : F) = u := rfl
    rw [← hv]
    have h : ‖χ (v : F)‖ = 1 := by
      simpa only [MulChar.coe_equivToUnitHom] using
        Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity v)
    exact h.le

theorem primitive_gauss_norm_sq (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
  have h := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq] at h
  have hnorm : ((‖gaussSum χ ψ‖ ^ 2 : ℝ) : ℂ) =
      gaussSum χ ψ * star (gaussSum χ ψ) := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    simp only [starRingEnd_apply, mul_comm]
  apply Complex.ofReal_inj.mp
  rw [hnorm]
  exact h

theorem gauss_shift_all (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (n : F) :
    gaussSum χ (ψ.mulShift n) = χ⁻¹ n * gaussSum χ ψ := by
  by_cases hn : n = 0
  · subst n
    simp only [AddChar.mulShift_zero, MulChar.map_zero, zero_mul]
    exact gaussSum_one_right hχ
  · let u : Fˣ := Units.mk0 n hn
    have hu : (u : F) = n := rfl
    rw [← hu]
    exact gaussSum_mulShift_eq χ ψ u

theorem character_gauss_expansion (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (n : F) :
    χ n * gaussSum χ⁻¹ ψ =
      ∑ u : F, χ⁻¹ u * ψ (n * u) := by
  calc
    χ n * gaussSum χ⁻¹ ψ = gaussSum χ⁻¹ (ψ.mulShift n) := by
      simpa using (gauss_shift_all χ⁻¹ ψ (by simpa using hχ) n).symm
    _ = _ := by simp [gaussSum, AddChar.mulShift_apply, mul_comm]

theorem character_sum_le_additive_energy {ι : Type*} (I : Finset ι)
    (n : ι → F) (a : ι → ℂ) (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖∑ i ∈ I, a i * χ (n i)‖ ^ 2 ≤
      ∑ u : F, ‖∑ i ∈ I, a i * ψ (n i * u)‖ ^ 2 := by
  classical
  let g := gaussSum χ⁻¹ ψ
  let T (u : F) := ∑ i ∈ I, a i * ψ (n i * u)
  let S := ∑ i ∈ I, a i * χ (n i)
  have hsum : g * S = ∑ u : F, χ⁻¹ u * T u := by
    calc
      g * S = ∑ i ∈ I, a i * (χ (n i) * g) := by
        rw [mul_comm g S, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i ∈ I, a i *
          (∑ u : F, χ⁻¹ u * ψ (n i * u)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [character_gauss_expansion χ ψ hχ (n i)]
      _ = ∑ u : F, χ⁻¹ u * T u := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hmass : (∑ u : F, ‖χ⁻¹ u‖ ^ 2) ≤ (Fintype.card F : ℝ) := by
    calc
      _ ≤ ∑ u : F, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro u _
        have hu := character_norm_le_one χ⁻¹ u
        nlinarith [norm_nonneg (χ⁻¹ u)]
      _ = _ := by simp
  have hcauchy := complex_sum_cauchy (Finset.univ : Finset F)
    (fun u => χ⁻¹ u) T
  have hgauss : ‖g‖ ^ 2 = (Fintype.card F : ℝ) := by
    exact primitive_gauss_norm_sq χ⁻¹ ψ (by simpa using hχ) hψ
  have hnonneg : 0 ≤ ∑ u : F, ‖T u‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hpre : (Fintype.card F : ℝ) * ‖S‖ ^ 2 ≤
      (Fintype.card F : ℝ) * ∑ u : F, ‖T u‖ ^ 2 := by
    calc
      _ = ‖g * S‖ ^ 2 := by rw [norm_mul, mul_pow, hgauss]
      _ = ‖∑ u : F, χ⁻¹ u * T u‖ ^ 2 := by rw [hsum]
      _ ≤ (∑ u : F, ‖χ⁻¹ u‖ ^ 2) * ∑ u : F, ‖T u‖ ^ 2 := hcauchy
      _ ≤ _ := mul_le_mul_of_nonneg_right hmass hnonneg
  have hcard : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  exact (mul_le_mul_iff_of_pos_left hcard).mp hpre

end FiniteFieldSieve

namespace ProductResidueSieve

variable {R S : Type*} [CommRing R] [CommRing S]

noncomputable def mulCharProd (χ : MulChar R ℂ) (η : MulChar S ℂ) : MulChar (R × S) ℂ where
  toFun x := χ x.1 * η x.2
  map_one' := by simp
  map_mul' x y := by simp [mul_mul_mul_comm]
  map_nonunit' x hx := by
    rw [Prod.isUnit_iff] at hx
    by_cases h₁ : IsUnit x.1
    · have h₂ : ¬IsUnit x.2 := by tauto
      simp [MulChar.map_nonunit η h₂]
    · simp [MulChar.map_nonunit χ h₁]

def addCharProd (ψ : AddChar R ℂ) (φ : AddChar S ℂ) : AddChar (R × S) ℂ where
  toFun x := ψ x.1 * φ x.2
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    simp only [Prod.fst_add, Prod.snd_add, AddChar.map_add_eq_mul]
    ring

@[simp] theorem mulCharProd_apply (χ : MulChar R ℂ) (η : MulChar S ℂ) (x : R × S) :
    mulCharProd χ η x = χ x.1 * η x.2 := rfl

@[simp] theorem addCharProd_apply (ψ : AddChar R ℂ) (φ : AddChar S ℂ) (x : R × S) :
    addCharProd ψ φ x = ψ x.1 * φ x.2 := rfl

end ProductResidueSieve

open MeasureTheory Real
open scoped FourierTransform SchwartzMap

open scoped ContDiff

namespace FourierBridge

theorem schwartz_log_inversion (g : 𝓢(ℝ, ℂ)) (y : ℝ) :
    g y = ∫ t : ℝ,
      Complex.exp ((↑(2 * Real.pi * inner ℝ t y) * Complex.I)) * (𝓕 g) t := by
  have hinv : (𝓕⁻ (𝓕 g) : 𝓢(ℝ, ℂ)) = g := by simp
  have h := congrArg (fun f : 𝓢(ℝ, ℂ) => f y) hinv
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq'] at h
  simpa only [smul_eq_mul] using h.symm

noncomputable def logProfile
    (W : ℝ → ℂ) (F : ℝ → ℂ) (R a : ℝ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W)
    (hFs : ContDiff ℝ ∞ F) : 𝓢(ℝ, ℂ) := by
  let G : ℝ → ℂ := fun y => W y * F (R * Real.exp (a * y))
  have harg : ContDiff ℝ ∞ (fun y : ℝ => R * Real.exp (a * y)) := by
    fun_prop
  have hGs : ContDiff ℝ ∞ G := by
    dsimp [G]
    exact hWs.mul (hFs.comp harg)
  have hGc : HasCompactSupport G := by
    dsimp [G]
    exact hWc.mul_right
  exact hGc.toSchwartzMap hGs

theorem logProfile_apply
    (W : ℝ → ℂ) (F : ℝ → ℂ) (R a y : ℝ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W)
    (hFs : ContDiff ℝ ∞ F) :
    logProfile W F R a hWc hWs hFs y = W y * F (R * Real.exp (a * y)) := rfl

theorem smooth_log_separation
    (W : ℝ → ℂ) (F : ℝ → ℂ) (R a y : ℝ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W)
    (hFs : ContDiff ℝ ∞ F) :
    W y * F (R * Real.exp (a * y)) =
      ∫ t : ℝ, Complex.exp ((↑(2 * Real.pi * inner ℝ t y) * Complex.I)) *
        (𝓕 (logProfile W F R a hWc hWs hFs)) t := by
  rw [← logProfile_apply W F R a y hWc hWs hFs]
  exact schwartz_log_inversion _ _

theorem fourier_coefficient_moment (g : 𝓢(ℝ, ℂ)) (J : ℕ) :
    ∫ t : ℝ, ‖t‖ ^ J * ‖(𝓕 g) t‖ ≤
      (2 ^ (volume : Measure ℝ).integrablePower *
        ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
      ((SchwartzMap.seminorm ℝ 0 0) (𝓕 g) +
        (SchwartzMap.seminorm ℝ (J + (volume : Measure ℝ).integrablePower) 0) (𝓕 g)) := by
  simpa using SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℝ volume (𝓕 g) J 0

theorem logProfile_coefficient_integrable
    (W F : ℝ → ℂ) (R a : ℝ) (J : ℕ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W)
    (hFs : ContDiff ℝ ∞ F) :
    Integrable (fun t : ℝ => ‖t‖ ^ J *
      ‖(𝓕 (logProfile W F R a hWc hWs hFs)) t‖) volume :=
  (𝓕 (logProfile W F R a hWc hWs hFs)).integrable_pow_mul volume J

theorem logProfile_coefficient_moment
    (W F : ℝ → ℂ) (R a : ℝ) (J : ℕ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W)
    (hFs : ContDiff ℝ ∞ F) :
    ∫ t : ℝ, ‖t‖ ^ J * ‖(𝓕 (logProfile W F R a hWc hWs hFs)) t‖ ≤
      (2 ^ (volume : Measure ℝ).integrablePower *
        ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
      ((SchwartzMap.seminorm ℝ 0 0)
          (𝓕 (logProfile W F R a hWc hWs hFs)) +
        (SchwartzMap.seminorm ℝ (J + (volume : Measure ℝ).integrablePower) 0)
          (𝓕 (logProfile W F R a hWc hWs hFs))) :=
  fourier_coefficient_moment _ J

theorem logProfile_pointwise_decay
    (W F : ℝ → ℂ) (R a m CW CF : ℝ) (A : ℕ)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hWbound : ∀ y, ‖W y‖ ≤ CW)
    (hlower : ∀ y, W y ≠ 0 → m ≤ Real.exp (a * y))
    (hFdecay : ∀ u, 0 ≤ u → (1 + u) ^ A * ‖F u‖ ≤ CF)
    (y : ℝ) :
    m ^ A * (1 + R) ^ A * ‖W y * F (R * Real.exp (a * y))‖ ≤
      CW * CF := by
  by_cases hWy : W y = 0
  · simp [hWy, mul_nonneg hCW hCF]
  have hE : m ≤ Real.exp (a * y) := hlower y hWy
  have hu : 0 ≤ R * Real.exp (a * y) := by positivity
  have hscale : m * (1 + R) ≤ 1 + R * Real.exp (a * y) := by
    nlinarith [mul_nonneg hR (sub_nonneg.mpr hE)]
  have hpow : (m * (1 + R)) ^ A ≤
      (1 + R * Real.exp (a * y)) ^ A := by gcongr
  have hbase : (m * (1 + R)) ^ A * ‖F (R * Real.exp (a * y))‖ ≤ CF :=
    (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans
      (hFdecay _ hu)
  rw [Complex.norm_mul]
  calc
    m ^ A * (1 + R) ^ A * (‖W y‖ * ‖F (R * Real.exp (a * y))‖) =
      ‖W y‖ * ((m * (1 + R)) ^ A * ‖F (R * Real.exp (a * y))‖) := by rw [mul_pow]; ring
    _ ≤ CW * ((m * (1 + R)) ^ A * ‖F (R * Real.exp (a * y))‖) :=
      mul_le_mul_of_nonneg_right (hWbound y) (by positivity)
    _ ≤ CW * CF := mul_le_mul_of_nonneg_left hbase hCW

theorem logProfile_zero_seminorm_decay
    (W F : ℝ → ℂ) (R a m CW CF : ℝ) (A : ℕ)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hWbound : ∀ y, ‖W y‖ ≤ CW)
    (hlower : ∀ y, W y ≠ 0 → m ≤ Real.exp (a * y))
    (hFdecay : ∀ u, 0 ≤ u → (1 + u) ^ A * ‖F u‖ ≤ CF)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W)
    (hFs : ContDiff ℝ ∞ F) :
    m ^ A * (1 + R) ^ A *
      (SchwartzMap.seminorm ℝ 0 0) (logProfile W F R a hWc hWs hFs) ≤
      CW * CF := by
  let g := logProfile W F R a hWc hWs hFs
  let scale := m ^ A * (1 + R) ^ A
  have hscale : 0 < scale := by dsimp [scale]; positivity
  have hnum : 0 ≤ CW * CF := mul_nonneg hCW hCF
  have hbound : ∀ y, ‖g y‖ ≤ CW * CF / scale := by
    intro y
    apply (le_div_iff₀ hscale).mpr
    have hp := logProfile_pointwise_decay W F R a m CW CF A hR hm hm1
      hCW hCF hWbound hlower hFdecay y
    simpa [g, scale, logProfile_apply, mul_comm, mul_left_comm, mul_assoc] using hp
  have hsemi : (SchwartzMap.seminorm ℝ 0 0) g ≤ CW * CF / scale := by
    apply SchwartzMap.seminorm_le_bound ℝ 0 0 g (div_nonneg hnum hscale.le)
    intro y
    simpa using hbound y
  calc
    scale * (SchwartzMap.seminorm ℝ 0 0) g ≤ scale * (CW * CF / scale) :=
      mul_le_mul_of_nonneg_left hsemi hscale.le
    _ = CW * CF := by field_simp

theorem exp_argument_derivative_bound
    (R a y H : ℝ) (i : ℕ)
    (hR : 0 ≤ R) (hH : 1 ≤ H)
    (ha : |a| ≤ H) (hexp : Real.exp (a * y) ≤ H)
    (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (fun z : ℝ => R * Real.exp (a * z)) y‖ ≤
      (H ^ 2 * (1 + R)) ^ i := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_exp_const_mul]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hR,
    abs_of_pos (Real.exp_pos _), abs_pow]
  have hpowH : H ≤ H ^ i := by
    calc H = H ^ 1 := by ring
         _ ≤ H ^ i := pow_le_pow_right₀ hH hi
  have hpowR : R ≤ (1 + R) ^ i := by
    calc R ≤ 1 + R := by linarith
         _ = (1 + R) ^ 1 := by ring
         _ ≤ (1 + R) ^ i := pow_le_pow_right₀ (by linarith) hi
  calc
    R * (|a| ^ i * Real.exp (a * y)) ≤ R * (H ^ i * H) := by gcongr
    _ ≤ (1 + R) ^ i * (H ^ i * H ^ i) := by gcongr
    _ = (H ^ 2 * (1 + R)) ^ i := by simp only [mul_pow, pow_two]; ring

theorem coupled_factor_derivative_bound
    (F : ℝ → ℂ) (R a y H CF : ℝ) (A n j : ℕ)
    (hF : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hH : 1 ≤ H)
    (ha : |a| ≤ H) (hexp : Real.exp (a * y) ≤ H)
    (hj : j ≤ n)
    (_hCF : 0 ≤ CF)
    (hFdecay : ∀ i ≤ n, ∀ u, 0 ≤ u →
      (1 + u) ^ (A + n) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    ‖iteratedFDeriv ℝ j (fun z : ℝ => F (R * Real.exp (a * z))) y‖ ≤
      j.factorial * (CF / (1 + R * Real.exp (a * y)) ^ (A + n)) *
        (H ^ 2 * (1 + R)) ^ j := by
  have harg : ContDiff ℝ ∞ (fun z : ℝ => R * Real.exp (a * z)) := by fun_prop
  have hu : 0 ≤ R * Real.exp (a * y) := by positivity
  have hden : 0 < (1 + R * Real.exp (a * y)) ^ (A + n) := by positivity
  apply norm_iteratedFDeriv_comp_le hF harg (by first | simp | exact_mod_cast le_top) y
  · intro i hi
    apply (le_div_iff₀ hden).mpr
    simpa [mul_comm] using hFdecay i (hi.trans hj) _ hu
  · intro i hi₁ hi₂
    exact exp_argument_derivative_bound R a y H i hR hH ha hexp hi₁

theorem derivative_scale_absorption
    (R u m H CF : ℝ) (A n j : ℕ)
    (hR : 0 ≤ R) (hm : 0 < m)
    (_hH : 0 ≤ H) (hCF : 0 ≤ CF)
    (hu : 0 ≤ u) (hlower : m * (1 + R) ≤ 1 + u)
    (hj : j ≤ n) :
    m ^ (A + n) * (1 + R) ^ A *
      ((j.factorial : ℝ) * (CF / (1 + u) ^ (A + n)) *
        (H ^ 2 * (1 + R)) ^ j) ≤
      (j.factorial : ℝ) * CF * (H ^ 2) ^ j := by
  have hRp : 1 ≤ 1 + R := by linarith
  have hden : 0 < (1 + u) ^ (A + n) := by positivity
  have hpowR : (1 + R) ^ (A + j) ≤ (1 + R) ^ (A + n) :=
    pow_le_pow_right₀ hRp (Nat.add_le_add_left hj A)
  have hscale : m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j ≤
      (1 + u) ^ (A + n) := by
    calc
      m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j =
          m ^ (A + n) * (1 + R) ^ (A + j) := by rw [pow_add]; ring
      _ ≤ m ^ (A + n) * (1 + R) ^ (A + n) :=
        mul_le_mul_of_nonneg_left hpowR (by positivity)
      _ = (m * (1 + R)) ^ (A + n) := by rw [mul_pow]
      _ ≤ (1 + u) ^ (A + n) := by gcongr
  let Q : ℝ := (j.factorial : ℝ) * CF * (H ^ 2) ^ j
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hQscale : Q * (m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j) ≤
      Q * (1 + u) ^ (A + n) := mul_le_mul_of_nonneg_left hscale hQ
  calc
    m ^ (A + n) * (1 + R) ^ A *
        ((j.factorial : ℝ) * (CF / (1 + u) ^ (A + n)) *
          (H ^ 2 * (1 + R)) ^ j) =
      Q * (m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j) /
        (1 + u) ^ (A + n) := by dsimp [Q]; rw [mul_pow]; ring
    _ ≤ Q := (div_le_iff₀ hden).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hQscale)
    _ = (j.factorial : ℝ) * CF * (H ^ 2) ^ j := rfl

theorem coupled_factor_uniform_derivative
    (F : ℝ → ℂ) (R a y m H CF : ℝ) (A n j : ℕ)
    (hF : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hH : 1 ≤ H) (ha : |a| ≤ H)
    (hexpLower : m ≤ Real.exp (a * y))
    (hexpUpper : Real.exp (a * y) ≤ H)
    (hj : j ≤ n) (hCF : 0 ≤ CF)
    (hFdecay : ∀ i ≤ n, ∀ u, 0 ≤ u →
      (1 + u) ^ (A + n) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    m ^ (A + n) * (1 + R) ^ A *
      ‖iteratedFDeriv ℝ j (fun z : ℝ => F (R * Real.exp (a * z))) y‖ ≤
        (j.factorial : ℝ) * CF * (H ^ 2) ^ j := by
  have hcomp := coupled_factor_derivative_bound F R a y H CF A n j hF hR hH
    ha hexpUpper hj hCF hFdecay
  have hscale : 0 ≤ m ^ (A + n) * (1 + R) ^ A := by positivity
  have hlower : m * (1 + R) ≤ 1 + R * Real.exp (a * y) := by
    nlinarith [mul_nonneg hR (sub_nonneg.mpr hexpLower)]
  exact (mul_le_mul_of_nonneg_left hcomp hscale).trans
    (derivative_scale_absorption R (R * Real.exp (a * y)) m H CF A n j
      hR hm (by linarith) hCF (by positivity) hlower hj)

theorem logProfile_derivative_decay
    (W F : ℝ → ℂ) (R a m H CW CF : ℝ) (A n : ℕ)
    (hWs : ContDiff ℝ ∞ W) (hFs : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hH : 1 ≤ H) (ha : |a| ≤ H)
    (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hWderiv : ∀ i ≤ n, ∀ y,
      ‖iteratedFDeriv ℝ i W y‖ ≤ CW)
    (hwindow : ∀ y,
      (∃ i ≤ n, ‖iteratedFDeriv ℝ i W y‖ ≠ 0) →
        m ≤ Real.exp (a * y) ∧ Real.exp (a * y) ≤ H)
    (hFdecay : ∀ i ≤ n, ∀ u, 0 ≤ u →
      (1 + u) ^ (A + n) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF)
    (y : ℝ) :
    m ^ (A + n) * (1 + R) ^ A *
      ‖iteratedFDeriv ℝ n (fun z : ℝ => W z * F (R * Real.exp (a * z))) y‖ ≤
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * CW *
          ((n - i).factorial * CF * (H ^ 2) ^ (n - i)) := by
  have harg : ContDiff ℝ ∞ (fun z : ℝ => R * Real.exp (a * z)) := by fun_prop
  have hG : ContDiff ℝ ∞ (fun z : ℝ => F (R * Real.exp (a * z))) :=
    hFs.comp harg
  have hprod := norm_iteratedFDeriv_mul_le hWs hG y (n := n) (by first | simp | exact_mod_cast le_top)
  have hscale : 0 ≤ m ^ (A + n) * (1 + R) ^ A := by positivity
  calc
    m ^ (A + n) * (1 + R) ^ A *
        ‖iteratedFDeriv ℝ n (fun z : ℝ => W z * F (R * Real.exp (a * z))) y‖ ≤
      (m ^ (A + n) * (1 + R) ^ A) *
        (∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i W y‖ *
          ‖iteratedFDeriv ℝ (n - i)
            (fun z : ℝ => F (R * Real.exp (a * z))) y‖) :=
      mul_le_mul_of_nonneg_left hprod hscale
    _ = ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i W y‖ *
          ((m ^ (A + n) * (1 + R) ^ A) *
            ‖iteratedFDeriv ℝ (n - i)
              (fun z : ℝ => F (R * Real.exp (a * z))) y‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * CW *
          ((n - i).factorial * CF * (H ^ 2) ^ (n - i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      by_cases hWi : ‖iteratedFDeriv ℝ i W y‖ = 0
      · simp [hWi]
        positivity
      obtain ⟨hLower, hUpper⟩ := hwindow y ⟨i, hi', hWi⟩
      have hGbound := coupled_factor_uniform_derivative F R a y m H CF A n
        (n - i) hFs hR hm hm1 hH ha hLower hUpper (Nat.sub_le n i)
        hCF hFdecay
      have hWbound := hWderiv i hi' y
      gcongr

theorem logProfile_uniform_seminorm
    (W F : ℝ → ℂ) (R a m H L CW CF : ℝ) (A n k : ℕ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W) (hFs : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hH : 1 ≤ H) (ha : |a| ≤ H)
    (hL : 0 ≤ L) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hWderiv : ∀ i ≤ n, ∀ y,
      ‖iteratedFDeriv ℝ i W y‖ ≤ CW)
    (hwindow : ∀ y,
      (∃ i ≤ n, ‖iteratedFDeriv ℝ i W y‖ ≠ 0) →
        m ≤ Real.exp (a * y) ∧
        Real.exp (a * y) ≤ H ∧ |y| ≤ L)
    (hFdecay : ∀ i ≤ n, ∀ u, 0 ≤ u →
      (1 + u) ^ (A + n) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    m ^ (A + n) * (1 + R) ^ A *
      (SchwartzMap.seminorm ℝ k n) (logProfile W F R a hWc hWs hFs) ≤
      L ^ k * (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * CW *
          ((n - i).factorial * CF * (H ^ 2) ^ (n - i))) := by
  let g := logProfile W F R a hWc hWs hFs
  have hgeq : (g : ℝ → ℂ) = fun z => W z * F (R * Real.exp (a * z)) := by
    funext z
    exact logProfile_apply W F R a z hWc hWs hFs
  let scale := m ^ (A + n) * (1 + R) ^ A
  let C := ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * CW *
          ((n - i).factorial * CF * (H ^ 2) ^ (n - i))
  have hscale : 0 < scale := by dsimp [scale]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hLC : 0 ≤ L ^ k * C := by positivity
  have hpoint (y : ℝ) :
      scale * (|y| ^ k * ‖iteratedDeriv n g y‖) ≤ L ^ k * C := by
    by_cases hactive : ∃ i ≤ n, ‖iteratedFDeriv ℝ i W y‖ ≠ 0
    · obtain ⟨hlower, hupper, habs⟩ := hwindow y hactive
      have hraw := logProfile_derivative_decay W F R a m H CW CF A n
        hWs hFs hR hm hm1 hH ha hCW hCF hWderiv
        (by intro z hz; obtain ⟨h₁,h₂,_⟩ := hwindow z hz; exact ⟨h₁,h₂⟩)
        hFdecay y
      have hnorm : scale * ‖iteratedDeriv n g y‖ ≤ C := by
        rw [hgeq]
        simpa [scale, C, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hraw
      calc
        scale * (|y| ^ k * ‖iteratedDeriv n g y‖) =
          |y| ^ k * (scale * ‖iteratedDeriv n g y‖) := by ring
        _ ≤ |y| ^ k * C :=
          mul_le_mul_of_nonneg_left hnorm (pow_nonneg (abs_nonneg _) _)
        _ ≤ L ^ k * C :=
          mul_le_mul_of_nonneg_right (by gcongr) hC
    · have hzero (i : ℕ) (hi : i ≤ n) :
          ‖iteratedFDeriv ℝ i W y‖ = 0 := by
        by_contra hne
        exact hactive ⟨i, hi, hne⟩
      have harg : ContDiff ℝ ∞ (fun z : ℝ => R * Real.exp (a * z)) := by fun_prop
      have hG : ContDiff ℝ ∞ (fun z : ℝ => F (R * Real.exp (a * z))) :=
        hFs.comp harg
      have hprod := norm_iteratedFDeriv_mul_le hWs hG y (n := n) (by first | simp | exact_mod_cast le_top)
      have hsumzero :
          (∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i W y‖ *
              ‖iteratedFDeriv ℝ (n - i)
                (fun z : ℝ => F (R * Real.exp (a * z))) y‖) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hzero i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
        ring
      have hnormzero : ‖iteratedDeriv n g y‖ = 0 := by
        have hzero' :
            ‖iteratedFDeriv ℝ n
              (fun z : ℝ => W z * F (R * Real.exp (a * z))) y‖ = 0 :=
          le_antisymm (hprod.trans_eq hsumzero) (norm_nonneg _)
        rw [hgeq]
        simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hzero'
      simp [hnormzero, hLC]
  have hsemi : (SchwartzMap.seminorm ℝ k n) g ≤ L ^ k * C / scale := by
    apply SchwartzMap.seminorm_le_bound' ℝ k n g (div_nonneg hLC hscale.le)
    intro y
    exact (le_div_iff₀ hscale).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hpoint y)
  calc
    scale * (SchwartzMap.seminorm ℝ k n) g ≤ scale * (L ^ k * C / scale) :=
      mul_le_mul_of_nonneg_left hsemi hscale.le
    _ = L ^ k * C := by field_simp

theorem fourier_seminorm_from_derivative_integrals
    (g : 𝓢(ℝ, ℂ)) (k : ℕ) :
    (SchwartzMap.seminorm ℝ k 0) (𝓕 g) ≤
      (2 : ℝ) ^ k *
        ∑ p ∈ Finset.range 1 ×ˢ Finset.range (k + 1),
          ∫ v : ℝ, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 g v‖ := by
  have hpoint (w : ℝ) :=
    Real.pow_mul_norm_iteratedFDeriv_fourier_le
      (K := ⊤) (N := ⊤) (f := (g : ℝ → ℂ)) (g.smooth ⊤)
      (by intro a b ha hb; exact g.integrable_pow_mul_iteratedFDeriv volume a b)
      (k := 0) (n := k) (by first | simp | exact_mod_cast le_top) (by first | simp | exact_mod_cast le_top) w
  have hpoint' (w : ℝ) :
      ‖w‖ ^ k * ‖(𝓕 g) w‖ ≤
        (2 : ℝ) ^ k *
          ∑ p ∈ Finset.range 1 ×ˢ Finset.range (k + 1),
            ∫ v : ℝ, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 g v‖ := by
    simpa [SchwartzMap.fourier_coe] using hpoint w
  apply SchwartzMap.seminorm_le_bound ℝ k 0 (𝓕 g) (by positivity)
  intro w
  simpa using hpoint' w

theorem uniform_fourier_seminorm_transfer
    (g : 𝓢(ℝ, ℂ)) (k : ℕ) (S C : ℝ)
    (hS : 0 ≤ S) (_hC : 0 ≤ C)
    (hsource : ∀ i ≤ k,
      S * ((SchwartzMap.seminorm ℝ 0 i) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) ≤ C) :
    S * (SchwartzMap.seminorm ℝ k 0) (𝓕 g) ≤
      (2 : ℝ) ^ k * (k + 1) *
        (2 ^ (volume : Measure ℝ).integrablePower *
          ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C := by
  let V : ℝ := 2 ^ (volume : Measure ℝ).integrablePower *
    ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hI (i : ℕ) (hi : i ≤ k) :
      S * (∫ t : ℝ, ‖iteratedFDeriv ℝ i g t‖) ≤ V * C := by
    have hbase := SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℝ volume g 0 i
    have hbase' :
        (∫ t : ℝ, ‖iteratedFDeriv ℝ i g t‖) ≤
          V * ((SchwartzMap.seminorm ℝ 0 i) g +
            (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) := by
      simpa [V] using hbase
    calc
      S * (∫ t : ℝ, ‖iteratedFDeriv ℝ i g t‖) ≤
          S * (V * ((SchwartzMap.seminorm ℝ 0 i) g +
            (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g)) :=
        mul_le_mul_of_nonneg_left hbase' hS
      _ = V * (S * ((SchwartzMap.seminorm ℝ 0 i) g +
            (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g)) := by ring
      _ ≤ V * C := mul_le_mul_of_nonneg_left (hsource i hi) hV
  have hFourier := fourier_seminorm_from_derivative_integrals g k
  calc
    S * (SchwartzMap.seminorm ℝ k 0) (𝓕 g) ≤
      S * ((2 : ℝ) ^ k *
        ∑ p ∈ Finset.range 1 ×ˢ Finset.range (k + 1),
          ∫ t : ℝ, ‖t‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 g t‖) :=
      mul_le_mul_of_nonneg_left hFourier hS
    _ = (2 : ℝ) ^ k *
      ∑ p ∈ Finset.range 1 ×ˢ Finset.range (k + 1),
        S * (∫ t : ℝ, ‖t‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 g t‖) := by
      simp only [Finset.mul_sum]
      ring_nf
    _ ≤ (2 : ℝ) ^ k *
      ∑ _p ∈ Finset.range 1 ×ˢ Finset.range (k + 1), V * C := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro p hp
      have hp0 : p.1 = 0 := by
        have hlt := Finset.mem_range.mp (Finset.mem_product.mp hp).1
        omega
      have hp2 : p.2 ≤ k := Nat.lt_succ_iff.mp
        (Finset.mem_range.mp (Finset.mem_product.mp hp).2)
      simpa [hp0] using hI p.2 hp2
    _ = (2 : ℝ) ^ k * (k + 1) * V * C := by
      simp []
      ring
    _ = (2 : ℝ) ^ k * (k + 1) *
        (2 ^ (volume : Measure ℝ).integrablePower *
          ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C := rfl

theorem uniform_fourier_coefficient_moment
    (g : 𝓢(ℝ, ℂ)) (J : ℕ) (S C : ℝ)
    (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hsource : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      S * ((SchwartzMap.seminorm ℝ 0 i) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) ≤ C) :
    S * (∫ t : ℝ, ‖t‖ ^ J * ‖(𝓕 g) t‖) ≤
      (2 ^ (volume : Measure ℝ).integrablePower *
        ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
      ((2 : ℝ) ^ 0 * (0 + 1) *
        (2 ^ (volume : Measure ℝ).integrablePower *
          ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C +
        (2 : ℝ) ^ (J + (volume : Measure ℝ).integrablePower) *
          (J + (volume : Measure ℝ).integrablePower + 1) *
          (2 ^ (volume : Measure ℝ).integrablePower *
            ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C) := by
  let p := (volume : Measure ℝ).integrablePower
  let V : ℝ := 2 ^ p * ∫ t : ℝ, (1 + ‖t‖) ^ (-(p : ℝ))
  let K := J + p
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hfourier_zero := uniform_fourier_seminorm_transfer g 0 S C hS hC
    (by intro i hi; exact hsource i (by omega))
  have hfourier_K := uniform_fourier_seminorm_transfer g K S C hS hC
    (by intro i hi; exact hsource i (by simpa [K, p] using hi))
  have hmoment := fourier_coefficient_moment g J
  calc
    S * (∫ t : ℝ, ‖t‖ ^ J * ‖(𝓕 g) t‖) ≤
        S * (V * ((SchwartzMap.seminorm ℝ 0 0) (𝓕 g) +
          (SchwartzMap.seminorm ℝ K 0) (𝓕 g))) :=
      mul_le_mul_of_nonneg_left (by simpa [V, K, p] using hmoment) hS
    _ = V * (S * (SchwartzMap.seminorm ℝ 0 0) (𝓕 g) +
        S * (SchwartzMap.seminorm ℝ K 0) (𝓕 g)) := by ring
    _ ≤ V * ((2 : ℝ) ^ 0 * (0 + 1) * V * C +
        (2 : ℝ) ^ K * (K + 1) * V * C) := by
      apply mul_le_mul_of_nonneg_left _ hV
      exact add_le_add (by simpa [V] using hfourier_zero)
        (by simpa [K, V] using hfourier_K)
    _ = _ := by simp [V, K, p, Nat.cast_add]

noncomputable def profileDerivativeConstant (n : ℕ) (H CW CF : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) * CW *
      ((n - i).factorial * CF * (H ^ 2) ^ (n - i))

theorem profileDerivativeConstant_nonneg (n : ℕ) (H CW CF : ℝ)
    (hCW : 0 ≤ CW) (hCF : 0 ≤ CF) :
    0 ≤ profileDerivativeConstant n H CW CF := by
  unfold profileDerivativeConstant
  apply Finset.sum_nonneg
  intro i hi
  positivity

noncomputable def profileMomentConstant (K : ℕ) (L H CW CF : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (K + 1),
    (1 + L ^ (volume : Measure ℝ).integrablePower) *
      profileDerivativeConstant j H CW CF

theorem profileMomentConstant_nonneg (K : ℕ) (L H CW CF : ℝ)
    (hL : 0 ≤ L) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF) :
    0 ≤ profileMomentConstant K L H CW CF := by
  unfold profileMomentConstant
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (by positivity)
    (profileDerivativeConstant_nonneg j H CW CF hCW hCF)

theorem profileMomentConstant_dominates (K j : ℕ) (L H CW CF : ℝ)
    (hL : 0 ≤ L) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF) (hj : j ≤ K) :
    (1 + L ^ (volume : Measure ℝ).integrablePower) *
      profileDerivativeConstant j H CW CF ≤
      profileMomentConstant K L H CW CF := by
  unfold profileMomentConstant
  apply Finset.single_le_sum
    (f := fun i : ℕ =>
      (1 + L ^ (volume : Measure ℝ).integrablePower) *
        profileDerivativeConstant i H CW CF)
    (a := j)
  · intro i hi
    exact mul_nonneg (by positivity)
      (profileDerivativeConstant_nonneg i H CW CF hCW hCF)
  · exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj)

theorem uniform_logProfile_source_pair
    (W F : ℝ → ℂ) (R a m H L CW CF C : ℝ) (A K n : ℕ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W) (hFs : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hH : 1 ≤ H) (ha : |a| ≤ H)
    (hL : 0 ≤ L) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hn : n ≤ K)
    (hWderiv : ∀ i ≤ K, ∀ y,
      ‖iteratedFDeriv ℝ i W y‖ ≤ CW)
    (hwindow : ∀ y,
      (∃ i ≤ K, ‖iteratedFDeriv ℝ i W y‖ ≠ 0) →
        m ≤ Real.exp (a * y) ∧
        Real.exp (a * y) ≤ H ∧ |y| ≤ L)
    (hFdecay : ∀ j ≤ K, ∀ i ≤ j, ∀ u, 0 ≤ u →
      (1 + u) ^ (A + j) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF)
    (hCbound : ∀ j ≤ K,
      (1 + L ^ (volume : Measure ℝ).integrablePower) *
        profileDerivativeConstant j H CW CF ≤ C) :
    (m ^ (A + K) * (1 + R) ^ A) *
      ((SchwartzMap.seminorm ℝ 0 n)
          (logProfile W F R a hWc hWs hFs) +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower n)
          (logProfile W F R a hWc hWs hFs)) ≤ C := by
  let p := (volume : Measure ℝ).integrablePower
  let D : ℝ := profileDerivativeConstant n H CW CF
  let g := logProfile W F R a hWc hWs hFs
  have hWderiv_n : ∀ i ≤ n, ∀ y,
      ‖iteratedFDeriv ℝ i W y‖ ≤ CW := by
    intro i hi y
    exact hWderiv i (hi.trans hn) y
  have hwindow_n : ∀ y,
      (∃ i ≤ n, ‖iteratedFDeriv ℝ i W y‖ ≠ 0) →
        m ≤ Real.exp (a * y) ∧
        Real.exp (a * y) ≤ H ∧ |y| ≤ L := by
    intro y hy
    obtain ⟨i, hi, hnonzero⟩ := hy
    exact hwindow y ⟨i, hi.trans hn, hnonzero⟩
  have hFdecay_n : ∀ i ≤ n, ∀ u, 0 ≤ u →
      (1 + u) ^ (A + n) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF :=
    hFdecay n hn
  have hzero := logProfile_uniform_seminorm W F R a m H L CW CF A n 0
    hWc hWs hFs hR hm hm1 hH ha hL hCW hCF
    hWderiv_n hwindow_n hFdecay_n
  have hp := logProfile_uniform_seminorm W F R a m H L CW CF A n p
    hWc hWs hFs hR hm hm1 hH ha hL hCW hCF
    hWderiv_n hwindow_n hFdecay_n
  have hscale : m ^ (A + K) * (1 + R) ^ A ≤
      m ^ (A + n) * (1 + R) ^ A :=
    mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one hm.le hm1 (by omega)) (by positivity)
  have hsemi0 : 0 ≤ (SchwartzMap.seminorm ℝ 0 n) g := by positivity
  have hsemip : 0 ≤ (SchwartzMap.seminorm ℝ p n) g := by positivity
  have hzero' : (m ^ (A + K) * (1 + R) ^ A) *
      (SchwartzMap.seminorm ℝ 0 n) g ≤ D := by
    calc
      _ ≤ (m ^ (A + n) * (1 + R) ^ A) *
          (SchwartzMap.seminorm ℝ 0 n) g :=
        mul_le_mul_of_nonneg_right hscale hsemi0
      _ ≤ D := by simpa [D, profileDerivativeConstant, g] using hzero
  have hp' : (m ^ (A + K) * (1 + R) ^ A) *
      (SchwartzMap.seminorm ℝ p n) g ≤ L ^ p * D := by
    calc
      _ ≤ (m ^ (A + n) * (1 + R) ^ A) *
          (SchwartzMap.seminorm ℝ p n) g :=
        mul_le_mul_of_nonneg_right hscale hsemip
      _ ≤ L ^ p * D := by simpa [D, profileDerivativeConstant, g, p] using hp
  calc
    (m ^ (A + K) * (1 + R) ^ A) *
        ((SchwartzMap.seminorm ℝ 0 n) g +
          (SchwartzMap.seminorm ℝ p n) g) =
        (m ^ (A + K) * (1 + R) ^ A) *
          (SchwartzMap.seminorm ℝ 0 n) g +
        (m ^ (A + K) * (1 + R) ^ A) *
          (SchwartzMap.seminorm ℝ p n) g := by ring
    _ ≤ D + L ^ p * D := add_le_add hzero' hp'
    _ = (1 + L ^ p) * D := by ring
    _ ≤ C := by simpa [D, p] using hCbound n hn

theorem uniform_logProfile_coefficient_moment
    (W F : ℝ → ℂ) (R a m H L CW CF C : ℝ) (A J : ℕ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W) (hFs : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hH : 1 ≤ H) (ha : |a| ≤ H)
    (hL : 0 ≤ L) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF) (hC : 0 ≤ C)
    (hWderiv : ∀ i ≤ J + (volume : Measure ℝ).integrablePower, ∀ y,
      ‖iteratedFDeriv ℝ i W y‖ ≤ CW)
    (hwindow : ∀ y,
      (∃ i ≤ J + (volume : Measure ℝ).integrablePower,
        ‖iteratedFDeriv ℝ i W y‖ ≠ 0) →
        m ≤ Real.exp (a * y) ∧
        Real.exp (a * y) ≤ H ∧ |y| ≤ L)
    (hFdecay : ∀ j ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ i ≤ j, ∀ u, 0 ≤ u →
        (1 + u) ^ (A + j) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF)
    (hCbound : ∀ j ≤ J + (volume : Measure ℝ).integrablePower,
      (1 + L ^ (volume : Measure ℝ).integrablePower) *
        profileDerivativeConstant j H CW CF ≤ C) :
    (m ^ (A + (J + (volume : Measure ℝ).integrablePower)) *
      (1 + R) ^ A) *
      (∫ t : ℝ, ‖t‖ ^ J *
        ‖(𝓕 (logProfile W F R a hWc hWs hFs)) t‖) ≤
      (2 ^ (volume : Measure ℝ).integrablePower *
        ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
      ((2 : ℝ) ^ 0 * (0 + 1) *
        (2 ^ (volume : Measure ℝ).integrablePower *
          ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C +
        (2 : ℝ) ^ (J + (volume : Measure ℝ).integrablePower) *
          (J + (volume : Measure ℝ).integrablePower + 1) *
          (2 ^ (volume : Measure ℝ).integrablePower *
            ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C) := by
  apply uniform_fourier_coefficient_moment _ J _ C (by positivity) hC
  intro i hi
  exact uniform_logProfile_source_pair W F R a m H L CW CF C A
    (J + (volume : Measure ℝ).integrablePower) i
    hWc hWs hFs hR hm hm1 hH ha hL hCW hCF hi
    hWderiv hwindow hFdecay hCbound

theorem uniform_logProfile_coefficient_moment_explicit
    (W F : ℝ → ℂ) (R a m H L CW CF : ℝ) (A J : ℕ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W) (hFs : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hH : 1 ≤ H) (ha : |a| ≤ H)
    (hL : 0 ≤ L) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hWderiv : ∀ i ≤ J + (volume : Measure ℝ).integrablePower, ∀ y,
      ‖iteratedFDeriv ℝ i W y‖ ≤ CW)
    (hwindow : ∀ y,
      (∃ i ≤ J + (volume : Measure ℝ).integrablePower,
        ‖iteratedFDeriv ℝ i W y‖ ≠ 0) →
        m ≤ Real.exp (a * y) ∧
        Real.exp (a * y) ≤ H ∧ |y| ≤ L)
    (hFdecay : ∀ j ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ i ≤ j, ∀ u, 0 ≤ u →
        (1 + u) ^ (A + j) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    (m ^ (A + (J + (volume : Measure ℝ).integrablePower)) *
      (1 + R) ^ A) *
      (∫ t : ℝ, ‖t‖ ^ J *
        ‖(𝓕 (logProfile W F R a hWc hWs hFs)) t‖) ≤
      (2 ^ (volume : Measure ℝ).integrablePower *
        ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
      ((2 : ℝ) ^ 0 * (0 + 1) *
        (2 ^ (volume : Measure ℝ).integrablePower *
          ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
          profileMomentConstant (J + (volume : Measure ℝ).integrablePower)
            L H CW CF +
        (2 : ℝ) ^ (J + (volume : Measure ℝ).integrablePower) *
          (J + (volume : Measure ℝ).integrablePower + 1) *
          (2 ^ (volume : Measure ℝ).integrablePower *
            ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
          profileMomentConstant (J + (volume : Measure ℝ).integrablePower)
            L H CW CF) := by
  apply uniform_logProfile_coefficient_moment W F R a m H L CW CF
    (profileMomentConstant (J + (volume : Measure ℝ).integrablePower)
      L H CW CF) A J
    hWc hWs hFs hR hm hm1 hH ha hL hCW hCF
    (profileMomentConstant_nonneg _ L H CW CF hL hCW hCF)
    hWderiv hwindow hFdecay
  intro j hj
  exact profileMomentConstant_dominates _ j L H CW CF hL hCW hCF hj

noncomputable def coefficientMomentBound (J : ℕ) (C : ℝ) : ℝ :=
  let p := (volume : Measure ℝ).integrablePower
  let V : ℝ := 2 ^ p * ∫ t : ℝ, (1 + ‖t‖) ^ (-(p : ℝ))
  V * (V * C + (2 : ℝ) ^ (J + p) * (J + p + 1) * V * C)

theorem coefficientMomentBound_nonneg (J : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ coefficientMomentBound J C := by
  unfold coefficientMomentBound
  positivity

theorem uniform_fourier_one_plus_moment
    (g : 𝓢(ℝ, ℂ)) (J : ℕ) (S C : ℝ)
    (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hsource : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      S * ((SchwartzMap.seminorm ℝ 0 i) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) ≤ C) :
    S * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖(𝓕 g) t‖) ≤
      (2 : ℝ) ^ J *
        (coefficientMomentBound 0 C + coefficientMomentBound J C) := by
  let b := 𝓕 g
  have hI0 : Integrable (fun t : ℝ => ‖b t‖) volume := by
    simpa using b.integrable_pow_mul volume 0
  have hIJ : Integrable (fun t : ℝ => ‖t‖ ^ J * ‖b t‖) volume :=
    b.integrable_pow_mul volume J
  have hIrhs : Integrable
      (fun t : ℝ => (2 : ℝ) ^ J *
        (‖b t‖ + ‖t‖ ^ J * ‖b t‖)) volume :=
    (hI0.add hIJ).const_mul _
  have hpoint (t : ℝ) :
      (1 + ‖t‖) ^ J * ‖b t‖ ≤
        (2 : ℝ) ^ J * (‖b t‖ + ‖t‖ ^ J * ‖b t‖) := by
    have hpow := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (norm_nonneg t) J
    have htwo : (2 : ℝ) ^ (J - 1) ≤ (2 : ℝ) ^ J :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le J 1)
    calc
      (1 + ‖t‖) ^ J * ‖b t‖ ≤
          (2 : ℝ) ^ (J - 1) * (1 ^ J + ‖t‖ ^ J) * ‖b t‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ ≤ (2 : ℝ) ^ J * (1 ^ J + ‖t‖ ^ J) * ‖b t‖ := by
        gcongr
      _ = (2 : ℝ) ^ J * (‖b t‖ + ‖t‖ ^ J * ‖b t‖) := by
        simp; ring
  have hintegral :
      (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤
        (2 : ℝ) ^ J *
          ((∫ t : ℝ, ‖b t‖) +
            (∫ t : ℝ, ‖t‖ ^ J * ‖b t‖)) := by
    calc
      _ ≤ ∫ t : ℝ, (2 : ℝ) ^ J *
          (‖b t‖ + ‖t‖ ^ J * ‖b t‖) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (by intro t; positivity))
          hIrhs (Filter.Eventually.of_forall hpoint)
      _ = (2 : ℝ) ^ J *
          ((∫ t : ℝ, ‖b t‖) +
            (∫ t : ℝ, ‖t‖ ^ J * ‖b t‖)) := by
        rw [integral_const_mul, integral_add hI0 hIJ]
  have hbound0 := uniform_fourier_coefficient_moment g 0 S C hS hC
    (by intro i hi; exact hsource i (by omega))
  have hboundJ := uniform_fourier_coefficient_moment g J S C hS hC hsource
  calc
    S * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤
        S * ((2 : ℝ) ^ J *
          ((∫ t : ℝ, ‖b t‖) +
            (∫ t : ℝ, ‖t‖ ^ J * ‖b t‖))) :=
      mul_le_mul_of_nonneg_left hintegral hS
    _ = (2 : ℝ) ^ J *
        (S * (∫ t : ℝ, ‖b t‖) +
          S * (∫ t : ℝ, ‖t‖ ^ J * ‖b t‖)) := by ring
    _ ≤ (2 : ℝ) ^ J *
        (coefficientMomentBound 0 C + coefficientMomentBound J C) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add
      · simpa [coefficientMomentBound, b] using hbound0
      · simpa [coefficientMomentBound, b] using hboundJ

noncomputable def logPhase (t y : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t * y : ℝ) : ℂ) * Complex.I)

theorem logPhase_add (t u v : ℝ) :
    logPhase t (u + v) = logPhase t u * logPhase t v := by
  unfold logPhase
  convert! Complex.exp_add _ _ using 1 ; push_cast ; ring_nf

theorem logPhase_zero (t : ℝ) : logPhase t 0 = 1 := by
  simp [logPhase]

theorem logPhase_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ℝ) (z : ι → ℝ) :
    logPhase t (∑ i ∈ s, z i) = ∏ i ∈ s, logPhase t (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [logPhase_zero]
  | @insert i s hi ih => simp [hi, logPhase_add, ih]

theorem coupled_cutoff_active
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (V : ℝ → ℂ) (a y M : ι → ℝ)
    (hwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (hVone : ∀ s,
      |s| ≤ ∑ j : ι, |a j| * M j → V s = 1)
    (hprod : (∏ j : ι, W j (y j)) ≠ 0) :
    V (∑ j : ι, a j * y j) = 1 := by
  classical
  apply hVone
  calc
    |∑ j : ι, a j * y j| ≤ ∑ j : ι, |a j * y j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : ι, |a j| * M j := by
      apply Finset.sum_le_sum
      intro j hj
      have hnonzero : W j (y j) ≠ 0 :=
        (Finset.prod_ne_zero_iff.mp hprod) j (Finset.mem_univ j)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hwindow j (y j) hnonzero) (abs_nonneg _)

theorem exists_complex_smooth_cutoff (T : ℝ) (hT : 0 ≤ T) :
    ∃ V : ℝ → ℂ, HasCompactSupport V ∧ ContDiff ℝ ∞ V ∧
      (∀ s, |s| ≤ T → V s = 1) ∧
      tsupport V ⊆ Set.Icc (-(T + 1)) (T + 1) ∧ V 0 = 1 := by
  let f : ContDiffBump (0 : ℝ) :=
    { rIn := T + 1 / 2, rOut := T + 1,
      rIn_pos := by linarith, rIn_lt_rOut := by linarith }
  let V : ℝ → ℂ := fun s => (f s : ℂ)
  have hVc : HasCompactSupport V :=
    f.hasCompactSupport.comp_left Complex.ofReal_zero
  have hVs : ContDiff ℝ ∞ V := Complex.ofRealCLM.contDiff.comp f.contDiff
  have hone : ∀ s, |s| ≤ T → V s = 1 := by
    intro s hs
    have hm : s ∈ Metric.closedBall (0 : ℝ) f.rIn := by
      simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      dsimp [f]
      linarith
    simp [V, f.one_of_mem_closedBall hm]
  refine ⟨V, hVc, hVs, hone, ?_, hone 0 (by simpa using hT)⟩
  intro s hs
  have hm : s ∈ tsupport f :=
    tsupport_comp_subset (g := Complex.ofReal) Complex.ofReal_zero f hs
  rw [f.tsupport_eq] at hm
  simpa [f, Metric.mem_closedBall, Real.dist_eq, abs_le] using hm


theorem exists_complex_smooth_cutoff_with_derivative_bounds
    (T : ℝ) (K : ℕ) (hT : 0 ≤ T) :
    ∃ (V : ℝ → ℂ) (CW : ℝ),
      HasCompactSupport V ∧ ContDiff ℝ ∞ V ∧
      (∀ s, |s| ≤ T → V s = 1) ∧
      0 ≤ CW ∧
      (∀ i ≤ K, ∀ y, ‖iteratedFDeriv ℝ i V y‖ ≤ CW) ∧
      (∀ y,
        (∃ i ≤ K, ‖iteratedFDeriv ℝ i V y‖ ≠ 0) →
          Real.exp (-(T + 1)) ≤ Real.exp y ∧
          Real.exp y ≤ Real.exp (T + 1) ∧ |y| ≤ T + 1) := by
  obtain ⟨V, hVc, hVs, hVone, hVsupport, _⟩ :=
    exists_complex_smooth_cutoff T hT
  have each (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖iteratedFDeriv ℝ i V y‖ ≤ C := by
    have hb : BddAbove (Set.range (fun y => ‖iteratedFDeriv ℝ i V y‖)) :=
      (hVs.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm.bddAbove_range_of_hasCompactSupport
        ((hVc.iteratedFDeriv i).comp_left norm_zero)
    obtain ⟨C, hC⟩ := hb
    exact ⟨max C 0, le_max_right _ _, fun y =>
      (hC (Set.mem_range_self y)).trans (le_max_left _ _)⟩
  choose C hC0 hC using each
  let CW : ℝ := ∑ i ∈ Finset.range (K + 1), C i
  have hCW : 0 ≤ CW := Finset.sum_nonneg (fun i _ => hC0 i)
  have hVderiv : ∀ i ≤ K, ∀ y, ‖iteratedFDeriv ℝ i V y‖ ≤ CW := by
    intro i hi y
    exact (hC i y).trans (Finset.single_le_sum (fun j _ => hC0 j)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))
  refine ⟨V, CW, hVc, hVs, hVone, hCW, hVderiv, ?_⟩
  intro y hy
  obtain ⟨i, hi, hnonzero⟩ := hy
  have hyderiv : y ∈ Function.support (iteratedFDeriv ℝ i V) := by
    simpa [Function.mem_support] using hnonzero
  have hysupport : y ∈ tsupport V :=
    (support_iteratedFDeriv_subset i) hyderiv
  have hyinterval := hVsupport hysupport
  have hylower : -(T + 1) ≤ y := hyinterval.1
  have hyupper : y ≤ T + 1 := hyinterval.2
  constructor
  · exact Real.exp_le_exp.mpr hylower
  constructor
  · exact Real.exp_le_exp.mpr hyupper
  · exact abs_le.mpr ⟨hylower, hyupper⟩

noncomputable def schwartzDerivativeDecayConstant
    (F : 𝓢(ℝ, ℂ)) (M K : ℕ) : ℝ :=
  (2 : ℝ) ^ M *
    ∑ i ∈ Finset.range (K + 1),
      ((SchwartzMap.seminorm ℝ 0 i) F +
        (SchwartzMap.seminorm ℝ M i) F)

theorem schwartzDerivativeDecayConstant_nonneg
    (F : 𝓢(ℝ, ℂ)) (M K : ℕ) :
    0 ≤ schwartzDerivativeDecayConstant F M K := by
  unfold schwartzDerivativeDecayConstant
  positivity

theorem schwartz_derivative_decay_finite
    (F : 𝓢(ℝ, ℂ)) (A K j i : ℕ) (u : ℝ)
    (hj : j ≤ K) (hi : i ≤ j) (hu : 0 ≤ u) :
    (1 + u) ^ (A + j) * ‖iteratedFDeriv ℝ i F u‖ ≤
      schwartzDerivativeDecayConstant F (A + K) K := by
  let M := A + K
  let T : ℝ := (SchwartzMap.seminorm ℝ 0 i) F +
    (SchwartzMap.seminorm ℝ M i) F
  let N : ℝ := ‖iteratedFDeriv ℝ i F u‖
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hpow : (1 + u) ^ (A + j) ≤ (1 + u) ^ M :=
    pow_le_pow_right₀ (by linarith) (by dsimp [M]; omega)
  have hadd := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) hu M
  have htwo : (2 : ℝ) ^ (M - 1) ≤ (2 : ℝ) ^ M :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le M 1)
  have hsum : (1 + u) ^ M * N ≤ (2 : ℝ) ^ M *
      (N + u ^ M * N) := by
    calc
      (1 + u) ^ M * N ≤
          (2 : ℝ) ^ (M - 1) * (1 ^ M + u ^ M) * N :=
        mul_le_mul_of_nonneg_right hadd hN
      _ ≤ (2 : ℝ) ^ M * (1 ^ M + u ^ M) * N := by
        gcongr
      _ = (2 : ℝ) ^ M * (N + u ^ M * N) := by
        simp; ring
  have h0 : N ≤ (SchwartzMap.seminorm ℝ 0 i) F := by
    simpa [N] using SchwartzMap.le_seminorm ℝ 0 i F u
  have hM : u ^ M * N ≤ (SchwartzMap.seminorm ℝ M i) F := by
    simpa [N, Real.norm_eq_abs, abs_of_nonneg hu] using
      SchwartzMap.le_seminorm ℝ M i F u
  have hT : N + u ^ M * N ≤ T := add_le_add h0 hM
  have hTnonneg : 0 ≤ T := by dsimp [T]; positivity
  have hTsum : T ≤ ∑ k ∈ Finset.range (K + 1),
      ((SchwartzMap.seminorm ℝ 0 k) F +
        (SchwartzMap.seminorm ℝ M k) F) := by
    apply Finset.single_le_sum
      (f := fun k : ℕ =>
        (SchwartzMap.seminorm ℝ 0 k) F +
          (SchwartzMap.seminorm ℝ M k) F)
      (a := i)
    · intro k hk
      positivity
    · exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (hi.trans hj))
  calc
    (1 + u) ^ (A + j) * N ≤ (1 + u) ^ M * N :=
      mul_le_mul_of_nonneg_right hpow hN
    _ ≤ (2 : ℝ) ^ M * (N + u ^ M * N) := hsum
    _ ≤ (2 : ℝ) ^ M * T :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    _ ≤ (2 : ℝ) ^ M *
        (∑ k ∈ Finset.range (K + 1),
          ((SchwartzMap.seminorm ℝ 0 k) F +
            (SchwartzMap.seminorm ℝ M k) F)) :=
      mul_le_mul_of_nonneg_left hTsum (by positivity)
    _ = schwartzDerivativeDecayConstant F (A + K) K := rfl

theorem coupled_log_separation
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F V : ℝ → ℂ) (R : ℝ)
    (a y : ι → ℝ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFs : ContDiff ℝ ∞ F)
    (hactive : (∏ j : ι, W j (y j)) ≠ 0 →
      V (∑ j : ι, a j * y j) = 1) :
    (∏ j : ι, W j (y j)) *
      F (R * Real.exp (∑ j : ι, a j * y j)) =
      ∫ t : ℝ,
        (∏ j : ι, W j (y j) * logPhase t (a j * y j)) *
          (𝓕 (logProfile V F R 1 hVc hVs hFs)) t := by
  classical
  let s : ℝ := ∑ j : ι, a j * y j
  let P : ℂ := ∏ j : ι, W j (y j)
  let b := 𝓕 (logProfile V F R 1 hVc hVs hFs)
  have hsep : V s * F (R * Real.exp s) =
      ∫ t : ℝ, logPhase t s * b t := by
    calc
      V s * F (R * Real.exp s) =
          ∫ t : ℝ, Complex.exp
            ((↑(2 * Real.pi * inner ℝ t s) * Complex.I)) * b t := by
        simpa [b] using
          (smooth_log_separation V F R 1 s hVc hVs hFs)
      _ = ∫ t : ℝ, logPhase t s * b t := by
        apply integral_congr_ae
        filter_upwards [] with t
        congr 1
        simp only [logPhase, Real.inner_apply]
        congr 1
        push_cast
        ring
  have hcut : P * F (R * Real.exp s) =
      P * (V s * F (R * Real.exp s)) := by
    by_cases hP : P = 0
    · simp [hP]
    · rw [hactive (by simpa [P, s] using hP)]
      ring
  calc
    P * F (R * Real.exp s) = P * (V s * F (R * Real.exp s)) := hcut
    _ = P * (∫ t : ℝ, logPhase t s * b t) := by rw [hsep]
    _ = ∫ t : ℝ, P * (logPhase t s * b t) := by
      rw [integral_const_mul]
    _ = ∫ t : ℝ,
          (∏ j : ι, W j (y j) * logPhase t (a j * y j)) * b t := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [show logPhase t s = ∏ j : ι, logPhase t (a j * y j) by
        simpa [s] using logPhase_sum (Finset.univ : Finset ι) t
          (fun j => a j * y j)]
      rw [Finset.prod_mul_distrib]
      simp only [P]
      ring

theorem coupled_log_coefficient_bound
    (V F : ℝ → ℂ) (R m H L CW CF : ℝ) (A J : ℕ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V) (hFs : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hH : 1 ≤ H) (hL : 0 ≤ L)
    (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hVderiv : ∀ i ≤ J + (volume : Measure ℝ).integrablePower, ∀ y,
      ‖iteratedFDeriv ℝ i V y‖ ≤ CW)
    (hwindow : ∀ y,
      (∃ i ≤ J + (volume : Measure ℝ).integrablePower,
        ‖iteratedFDeriv ℝ i V y‖ ≠ 0) →
        m ≤ Real.exp y ∧ Real.exp y ≤ H ∧ |y| ≤ L)
    (hFdecay : ∀ j ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ i ≤ j, ∀ u, 0 ≤ u →
        (1 + u) ^ (A + j) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    (m ^ (A + (J + (volume : Measure ℝ).integrablePower)) *
      (1 + R) ^ A) *
      (∫ t : ℝ, (1 + ‖t‖) ^ J *
        ‖(𝓕 (logProfile V F R 1 hVc hVs hFs)) t‖) ≤
      (2 : ℝ) ^ J *
        (coefficientMomentBound 0
          (profileMomentConstant (J + (volume : Measure ℝ).integrablePower)
            L H CW CF) +
        coefficientMomentBound J
          (profileMomentConstant (J + (volume : Measure ℝ).integrablePower)
            L H CW CF)) := by
  apply uniform_fourier_one_plus_moment _ J _ _ (by positivity)
    (profileMomentConstant_nonneg _ L H CW CF hL hCW hCF)
  intro i hi
  exact uniform_logProfile_source_pair V F R 1 m H L CW CF
    (profileMomentConstant (J + (volume : Measure ℝ).integrablePower)
      L H CW CF) A
    (J + (volume : Measure ℝ).integrablePower) i
    hVc hVs hFs hR hm hm1 hH (by simpa using hH)
    hL hCW hCF hi hVderiv
    (by simpa only [one_mul] using hwindow)
    hFdecay
    (by intro j hj
        exact profileMomentConstant_dominates _ j L H CW CF
          hL hCW hCF hj)

theorem coupled_log_separation_schwartz
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F : 𝓢(ℝ, ℂ)) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hWwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (A J : ℕ) :
    ∃ (b : ℝ → ℝ → ℂ) (C : ℝ), 0 ≤ C ∧
      ∀ R : ℝ, 0 ≤ R →
        (∀ y : ι → ℝ,
          (∏ j : ι, W j (y j)) *
            F (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, W j (y j) * logPhase t (a j * y j)) *
              b R t) ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b R t‖) ≤ C := by
  classical
  let T : ℝ := ∑ j : ι, |a j| * M j
  have hT : 0 ≤ T := by
    dsimp [T]
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (abs_nonneg _) (hM j)
  let K : ℕ := J + (volume : Measure ℝ).integrablePower
  let L : ℝ := T + 1
  let m : ℝ := Real.exp (-L)
  let H : ℝ := Real.exp L
  let CF : ℝ := schwartzDerivativeDecayConstant F (A + K) K
  have hL : 0 ≤ L := by dsimp [L]; linarith
  have hm : 0 < m := Real.exp_pos _
  have hm1 : m ≤ 1 := by
    dsimp [m]
    simpa using (Real.exp_le_exp.mpr (show -L ≤ 0 by linarith))
  have hH : 1 ≤ H := by
    dsimp [H]
    simpa using (Real.exp_le_exp.mpr hL)
  have hCF : 0 ≤ CF := schwartzDerivativeDecayConstant_nonneg F (A + K) K
  obtain ⟨V, CW, hVc, hVs, hVone, hCW, hVderiv, hwindow⟩ :=
    exists_complex_smooth_cutoff_with_derivative_bounds T K hT
  let b : ℝ → ℝ → ℂ :=
    fun R t => (𝓕 (logProfile V F R 1 hVc hVs (F.smooth ⊤))) t
  let P : ℝ := profileMomentConstant K L H CW CF
  let B : ℝ := (2 : ℝ) ^ J *
    (coefficientMomentBound 0 P + coefficientMomentBound J P)
  let C : ℝ := B / m ^ (A + K)
  have hP : 0 ≤ P :=
    profileMomentConstant_nonneg K L H CW CF hL hCW hCF
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by positivity)
      (add_nonneg
        (coefficientMomentBound_nonneg 0 P hP)
        (coefficientMomentBound_nonneg J P hP))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨b, C, hC, ?_⟩
  intro R hR
  constructor
  · intro y
    have hactive : (∏ j : ι, W j (y j)) ≠ 0 →
        V (∑ j : ι, a j * y j) = 1 :=
      coupled_cutoff_active W V a y M hWwindow
        (by simpa [T] using hVone)
    simpa [b] using coupled_log_separation W F V R a y
      hVc hVs (F.smooth ⊤) hactive
  · have hbound := coupled_log_coefficient_bound V F R m H L CW CF A J
      hVc hVs (F.smooth ⊤) hR hm hm1 hH hL hCW hCF
      (by simpa [K] using hVderiv)
      (by simpa [m, H, L, K] using hwindow)
      (by intro j hj i hi u hu
          exact schwartz_derivative_decay_finite F A K j i u
            (by simpa [K] using hj) hi hu)
    have hmPow : 0 < m ^ (A + K) := pow_pos hm _
    dsimp [C]
    apply (le_div_iff₀ hmPow).mpr
    simpa [B, P, b, K, m, H, L, CF,
      mul_comm, mul_left_comm, mul_assoc] using hbound

end FourierBridge

end OAI

end


