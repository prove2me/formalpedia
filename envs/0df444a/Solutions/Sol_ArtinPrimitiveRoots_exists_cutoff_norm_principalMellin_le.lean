-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_norm_principalMellin_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T13:03:22.146167+00:00
-- url     : https://prove2.me/submissions/c24f8686-2e8c-455c-baf5-c005d0c439b2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_nonempty_allowedGen
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_tsum_norm_sq_additiveFactor_le
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_tsum_norm_sq_thetaSum_le
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_weights_hasSum_rowIntegral
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_norm_rowIntegral_principalFreq_sub_le
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_norm_tsum_rowIntegral_ne_principalFreq_le

section
namespace ArtinPrimitiveRoots

open NumberField

/-! T12L2: the analytic sub-lemmas of the reduction (8.22) ⇐ layer-2 cuts: the bump `W₁` and
Prop 7.2 by Cauchy–Schwarz (p. 44). -/

/-- A smooth bump `W₁` with compact support in `(0, ∞)` and `Ŵ₁(1) = ∫ W₁ ≠ 0`. -/
lemma L2_bump : ∃ W₁ : ℝ → ℝ, IsProbeWeight W₁ ∧ mellin (fun t => (W₁ t : ℂ)) 1 ≠ 0 := by
  let f : ContDiffBump (2 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  refine ⟨f, ⟨f.contDiff, f.hasCompactSupport, ?_⟩, ?_⟩
  · rw [f.tsupport_eq]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
    show 0 < x
    have : f.rOut = 1 := rfl
    linarith [hx.1]
  · have hsupp : ∀ x, x ∉ Set.Ioi (0 : ℝ) → f x = 0 := by
      intro x hx
      apply f.zero_of_le_dist
      rw [Real.dist_eq]
      simp only [Set.mem_Ioi, not_lt] at hx
      have : f.rOut = 1 := rfl
      rw [this, abs_of_neg (by linarith)]
      linarith
    have hI : ∫ t in Set.Ioi (0 : ℝ), f t = ∫ t, f t :=
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp
    have hpos : 0 < ∫ t, f t := f.integral_pos
    have hm : mellin (fun t => (f t : ℂ)) 1 = ((∫ t in Set.Ioi (0 : ℝ), f t : ℝ) : ℂ) := by
      rw [mellin, integral_complex_ofReal.symm]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
      simp
    rw [hm, hI]
    exact_mod_cast hpos.ne'

/-- A probe weight is supported in a compact interval `[a, b]` with `a > 0`. -/
lemma L2_supp {W : ℝ → ℝ} (h : IsProbeWeight W) :
    ∃ a b : ℝ, 0 < a ∧ ∀ t, W t ≠ 0 → a ≤ t ∧ t ≤ b := by
  rcases (tsupport W).eq_empty_or_nonempty with he | hne
  · refine ⟨1, 1, one_pos, fun t ht => ?_⟩
    have : t ∈ tsupport W := subset_tsupport W ht
    rw [he] at this; exact absurd this (Set.notMem_empty t)
  · obtain ⟨a, haK, hmin⟩ := h.2.1.isCompact.exists_isMinOn hne continuousOn_id
    obtain ⟨b, hb⟩ := h.2.1.isCompact.bddAbove
    refine ⟨a, b, h.2.2 haK, fun t ht => ?_⟩
    have htK : t ∈ tsupport W := subset_tsupport W ht
    exact ⟨hmin htK, hb htK⟩

/-- The additive factor vanishes unless `a₁a₂XY ≤ N𝔟 ≤ b₁b₂XY`. -/
lemma L2_additiveFactor_eq_zero {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ}
    {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) (W₁ V : ℝ → ℝ) {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : 0 < a₁)
    (ha₂ : 0 < a₂) (hW : ∀ t, W₁ t ≠ 0 → a₁ ≤ t ∧ t ≤ b₁)
    (hV : ∀ t, V t ≠ 0 → a₂ ≤ t ∧ t ≤ b₂) {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (r : RowClass 𝔪)
    (hr : ¬ (a₁ * a₂ * (X * Y) ≤ Ideal.absNorm r.1.1 ∧
      (Ideal.absNorm r.1.1 : ℝ) ≤ b₁ * b₂ * (X * Y))) :
    additiveFactor g W₁ V X Y r = 0 := by
  unfold additiveFactor
  convert tsum_zero with 𝔰
  set s : ℝ := (Ideal.absNorm 𝔰.1 : ℝ)
  set B : ℝ := (Ideal.absNorm r.1.1 : ℝ)
  by_cases h1 : W₁ (s / Y) = 0
  · simp [h1]
  by_cases h2 : V (B / (s * X)) = 0
  · simp [h2]
  exfalso
  obtain ⟨l1, u1⟩ := hW _ h1
  obtain ⟨l2, u2⟩ := hV _ h2
  have hab2 : a₂ ≤ b₂ := l2.trans u2
  have hs : 0 < s := by
    have : 0 < s / Y := lt_of_lt_of_le ha₁ l1
    exact (div_pos_iff_of_pos_right hY).mp this
  have hsX : 0 < s * X := mul_pos hs hX
  rw [le_div_iff₀ hY] at l1
  rw [div_le_iff₀ hY] at u1
  rw [le_div_iff₀ hsX] at l2
  rw [div_le_iff₀ hsX] at u2
  have hb2 : 0 ≤ b₂ := by linarith
  apply hr
  constructor
  · calc a₁ * a₂ * (X * Y) = a₂ * ((a₁ * Y) * X) := by ring
      _ ≤ a₂ * (s * X) := by gcongr
      _ ≤ B := by linarith
  · calc B ≤ b₂ * (s * X) := by linarith
      _ ≤ b₂ * ((b₁ * Y) * X) := by gcongr
      _ = b₁ * b₂ * (X * Y) := by ring

/-- Prop 7.2 from the two mass bounds by Cauchy–Schwarz (p. 44). -/
lemma L2_probe_le {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}
    (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) (W₁ V : ℝ → ℝ) (hW₁ : IsProbeWeight W₁)
    (hV : IsProbeWeight V)
    (hA : ∃ C : ℝ, ∀ X Y : ℝ, 1 ≤ Y → Y ≤ X →
      ∃ σ : ℝ, HasSum (fun r : RowClass 𝔪 => ‖additiveFactor g W₁ V X Y r‖ ^ 2) σ ∧ σ ≤ C / Y)
    (hB : ∀ c₁ c₂ ε : ℝ, 0 < c₁ → 0 < ε → ∃ C : ℝ, ∀ Z : ℝ, 2 ≤ Z →
      ∃ σ : ℝ, HasSum (fun r : {r : RowClass 𝔪 //
          c₁ * Z ^ ((1033 : ℝ) / 1000) ≤ Ideal.absNorm r.1.1 ∧
          (Ideal.absNorm r.1.1 : ℝ) ≤ c₂ * Z ^ ((1033 : ℝ) / 1000)} =>
            ‖χ.thetaSum g (rowElt g r.1) Z‖ ^ 2) σ ∧
        σ ≤ C * Z ^ (2 * ((1033 : ℝ) / 1000) - 1 + ε)) :
    ∃ C : ℝ, ∀ Z : ℝ, 2 ≤ Z →
      ‖χ.probe g W₁ V (Z ^ ((9 : ℝ) / 10)) (Z ^ ((133 : ℝ) / 1000)) Z‖ ≤
        C * Z ^ ((933 : ℝ) / 2000 + 1 / 100000) := by
  obtain ⟨CA, hA⟩ := hA
  obtain ⟨a₁, b₁, ha₁, hW⟩ := L2_supp hW₁
  obtain ⟨a₂, b₂, ha₂, hVs⟩ := L2_supp hV
  obtain ⟨CB, hB⟩ := hB (a₁ * a₂) (b₁ * b₂) (2 / 100000) (mul_pos ha₁ ha₂) (by norm_num)
  refine ⟨Real.sqrt (|CA| * |CB|), fun Z hZ => ?_⟩
  have hZ0 : 0 < Z := by linarith
  have hZ1 : (1 : ℝ) ≤ Z := by linarith
  set X := Z ^ ((9 : ℝ) / 10) with hXdef
  set Y := Z ^ ((133 : ℝ) / 1000) with hYdef
  have hX : 0 < X := Real.rpow_pos_of_pos hZ0 _
  have hY : 0 < Y := Real.rpow_pos_of_pos hZ0 _
  have hXY : X * Y = Z ^ ((1033 : ℝ) / 1000) := by
    rw [hXdef, hYdef, ← Real.rpow_add hZ0]; norm_num
  have h1Y : 1 ≤ Y := Real.one_le_rpow hZ1 (by norm_num)
  have hYX : Y ≤ X := Real.rpow_le_rpow_of_exponent_le hZ1 (by norm_num)
  obtain ⟨σA, hσA, hσA'⟩ := hA X Y h1Y hYX
  obtain ⟨σB, hσB, hσB'⟩ := hB Z hZ
  set p : RowClass 𝔪 → Prop := fun r => a₁ * a₂ * Z ^ ((1033 : ℝ) / 1000) ≤ Ideal.absNorm r.1.1 ∧
    (Ideal.absNorm r.1.1 : ℝ) ≤ b₁ * b₂ * Z ^ ((1033 : ℝ) / 1000) with hp
  set s : Set (RowClass 𝔪) := {r | p r}
  set A : RowClass 𝔪 → ℂ := fun r => additiveFactor g W₁ V X Y r
  set B : RowClass 𝔪 → ℂ := fun r => χ.thetaSum g (rowElt g r) Z
  have hAs : ∀ r, A r ≠ 0 → r ∈ s := by
    intro r hr
    by_contra hn
    apply hr
    refine L2_additiveFactor_eq_zero g W₁ V ha₁ ha₂ hW hVs hX hY r ?_
    rw [hXY]; exact hn
  have hsupp : Function.support (fun r => A r * B r) ⊆ s := by
    intro r hr
    exact hAs r (left_ne_zero_of_mul hr)
  have hprobe : χ.probe g W₁ V X Y Z = ∑' r : s, A r * B r := by
    rw [tsum_subtype_eq_of_support_subset hsupp]; rfl
  -- Cauchy–Schwarz on `s`
  have hfA : Summable fun r : s => ‖A r‖ ^ (2 : ℝ) := by
    simp_rw [Real.rpow_two]; exact hσA.summable.subtype s
  have hfB : Summable fun r : s => ‖B r‖ ^ (2 : ℝ) := by
    simp_rw [Real.rpow_two]; exact hσB.summable
  obtain ⟨hsum, hle⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    Real.HolderConjugate.two_two (fun r : s => norm_nonneg (A r)) (fun r : s => norm_nonneg (B r))
    hfA hfB
  have hSA : ∑' r : s, ‖A r‖ ^ (2 : ℝ) ≤ σA := by
    simp_rw [Real.rpow_two]
    rw [← hσA.tsum_eq]
    exact hσA.summable.tsum_subtype_le _ s (fun _ => by positivity)
  have hSB : ∑' r : s, ‖B r‖ ^ (2 : ℝ) = σB := by
    simp_rw [Real.rpow_two]; exact hσB.tsum_eq
  have hA0 : 0 ≤ ∑' r : s, ‖A r‖ ^ (2 : ℝ) := tsum_nonneg (fun _ => by positivity)
  have hB0 : 0 ≤ σB := hσB.nonneg (fun _ => by positivity)
  have hnorm : ‖χ.probe g W₁ V X Y Z‖ ≤ ∑' r : s, ‖A r‖ * ‖B r‖ := by
    rw [hprobe]
    refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
    · simpa [norm_mul] using hsum
    · simp
  have hE : ((1033 : ℝ) / 1000 * 2 - 1 + 2 / 100000) = 2 * ((1033 : ℝ) / 1000) - 1 + 2 / 100000 :=
    by ring
  refine hnorm.trans (hle.trans ?_)
  rw [hSB]
  set eB := Z ^ (2 * ((1033 : ℝ) / 1000) - 1 + 2 / 100000)
  have heB : 0 ≤ eB := Real.rpow_nonneg hZ0.le _
  have hA1 : ∑' r : s, ‖A r‖ ^ (2 : ℝ) ≤ |CA| / Y :=
    hSA.trans (hσA'.trans (div_le_div_of_nonneg_right (le_abs_self _) hY.le))
  have hB1 : σB ≤ |CB| * eB := hσB'.trans (mul_le_mul_of_nonneg_right (le_abs_self _) heB)
  calc (∑' r : s, ‖A r‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * σB ^ (1 / (2 : ℝ))
      ≤ (|CA| / Y) ^ (1 / (2 : ℝ)) * (|CB| * eB) ^ (1 / (2 : ℝ)) := by
        gcongr
    _ = (|CA| * |CB| * (eB / Y)) ^ (1 / (2 : ℝ)) := by
        rw [← Real.mul_rpow (by positivity) (by positivity)]; congr 1; ring
    _ = Real.sqrt (|CA| * |CB|) * Z ^ ((933 : ℝ) / 2000 + 1 / 100000) := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.sqrt_eq_rpow]
        congr 1
        rw [hYdef, ← Real.rpow_sub hZ0, ← Real.rpow_mul hZ0.le]
        norm_num

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField

/-! T12L2: the reduction (8.22) ⇐ layer-2 cuts C0–C4. -/

lemma L2_constant_ne_zero {F : Type*} [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥)
    (W₁ : ℝ → ℝ) (M : ℂ → ℂ) (hW : mellin (fun t => (W₁ t : ℂ)) 1 ≠ 0) (hM : M (1 / 6) ≠ 0) :
    principalConstant 𝔪 W₁ M ≠ 0 := by
  have hR : 0 < sZetaResidue 𝔪 := by
    unfold sZetaResidue
    refine mul_pos (dedekindZeta_residue_pos F) ?_
    apply finprod_mem_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos)
    intro P hP
    have h2 : (2 : ℝ) ≤ Ideal.absNorm P := by
      have := hP.1
      have hne : P ≠ ⊤ := this.ne_top
      have h1 : Ideal.absNorm P ≠ 1 := fun h => hne (Ideal.absNorm_eq_one_iff.mp h)
      have h0 : Ideal.absNorm P ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hP.2.1
      exact_mod_cast (by omega : 2 ≤ Ideal.absNorm P)
    have : (Ideal.absNorm P : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) h2
    linarith
  unfold principalConstant
  refine mul_ne_zero (mul_ne_zero ?_ hM) hW
  exact_mod_cast (by positivity : sZetaResidue 𝔪 ^ 2 / 6 ≠ 0)


/-- Final algebra: from the three bounds and `c₀ ≠ 0`. -/
lemma L2_final {f I J₁ Jr : ℝ → ℂ} {c₀ : ℂ} (hc₀ : c₀ ≠ 0) {C₁ C₂ C₃ Z₂ Z₃ : ℝ}
    (hI : ∀ Z : ℝ, 2 ≤ Z → ‖I Z‖ ≤ C₁ * Z ^ ((933 : ℝ) / 2000 + 1 / 100000))
    (hsplit : ∀ Z : ℝ, 2 ≤ Z → I Z = J₁ Z + Jr Z)
    (h₁ : ∀ Z : ℝ, Z₂ ≤ Z → ‖J₁ Z - c₀ * f Z‖ ≤ C₂ * Z ^ ((7 : ℝ) / 15 - 1 / 2000))
    (h₂ : ∀ Z : ℝ, Z₃ ≤ Z → ‖Jr Z‖ ≤ C₃ * Z ^ ((7 : ℝ) / 15 - 1 / 2500)) :
    ∃ C Z₀ : ℝ, ∀ Z : ℝ, Z₀ ≤ Z → ‖f Z‖ ≤ C * Z ^ ((7 : ℝ) / 15 - 1 / 20000) := by
  refine ⟨(|C₁| + |C₂| + |C₃|) / ‖c₀‖, max 2 (max Z₂ Z₃), fun Z hZ => ?_⟩
  have h2 : 2 ≤ Z := le_trans (le_max_left _ _) hZ
  have hZ2 : Z₂ ≤ Z := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hZ
  have hZ3 : Z₃ ≤ Z := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hZ
  have h1Z : (1 : ℝ) ≤ Z := by linarith
  have hc : 0 < ‖c₀‖ := norm_pos_iff.mpr hc₀
  set E := Z ^ ((7 : ℝ) / 15 - 1 / 20000)
  have hE0 : 0 ≤ E := Real.rpow_nonneg (by linarith) _
  have e1 : Z ^ ((933 : ℝ) / 2000 + 1 / 100000) ≤ E :=
    Real.rpow_le_rpow_of_exponent_le h1Z (by norm_num)
  have e2 : Z ^ ((7 : ℝ) / 15 - 1 / 2000) ≤ E := Real.rpow_le_rpow_of_exponent_le h1Z (by norm_num)
  have e3 : Z ^ ((7 : ℝ) / 15 - 1 / 2500) ≤ E := Real.rpow_le_rpow_of_exponent_le h1Z (by norm_num)
  have key : c₀ * f Z = I Z - (J₁ Z - c₀ * f Z) - Jr Z := by rw [hsplit Z h2]; ring
  have hb : ‖c₀ * f Z‖ ≤ (|C₁| + |C₂| + |C₃|) * E := by
    rw [key]
    have a1 := hI Z h2; have a2 := h₁ Z hZ2; have a3 := h₂ Z hZ3
    have p1 : 0 ≤ Z ^ ((933 : ℝ) / 2000 + 1 / 100000) := Real.rpow_nonneg (by linarith) _
    have p2 : 0 ≤ Z ^ ((7 : ℝ) / 15 - 1 / 2000) := Real.rpow_nonneg (by linarith) _
    have p3 : 0 ≤ Z ^ ((7 : ℝ) / 15 - 1 / 2500) := Real.rpow_nonneg (by linarith) _
    calc ‖I Z - (J₁ Z - c₀ * f Z) - Jr Z‖ ≤ ‖I Z‖ + ‖J₁ Z - c₀ * f Z‖ + ‖Jr Z‖ := by
          refine (norm_sub_le _ _).trans ?_; gcongr; exact norm_sub_le _ _
      _ ≤ |C₁| * E + |C₂| * E + |C₃| * E := by
          gcongr
          · exact a1.trans (mul_le_mul (le_abs_self _) e1 p1 (abs_nonneg _))
          · exact a2.trans (mul_le_mul (le_abs_self _) e2 p2 (abs_nonneg _))
          · exact a3.trans (mul_le_mul (le_abs_self _) e3 p3 (abs_nonneg _))
      _ = (|C₁| + |C₂| + |C₃|) * E := by ring
  rw [norm_mul] at hb
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  linarith [mul_comm ‖c₀‖ ‖f Z‖]

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open NumberField
theorem solution (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → ∀ χ : HeckeChar F 𝔪,
      ∃ C Z₀ : ℝ, ∀ Z : ℝ, Z₀ ≤ Z →
        ‖χ.principalMellin ι Z‖ ≤ C * Z ^ ((7 : ℝ) / 15 - 1 / 20000) := by
  obtain ⟨N0, h0⟩ := exists_cutoff_nonempty_allowedGen n hn0 hn F ι
  obtain ⟨Na, ha⟩ := exists_cutoff_tsum_norm_sq_additiveFactor_le n hn0 hn F ι
  obtain ⟨Nb, hb⟩ := exists_cutoff_tsum_norm_sq_thetaSum_le n hn0 hn F ι
  obtain ⟨N2, h2⟩ := exists_cutoff_exists_weights_hasSum_rowIntegral n hn0 hn F ι
  obtain ⟨N3, h3⟩ := exists_cutoff_norm_rowIntegral_principalFreq_sub_le n hn0 hn F ι
  obtain ⟨N4, h4⟩ := exists_cutoff_norm_tsum_rowIntegral_ne_principalFreq_le n hn0 hn F ι
  refine ⟨max N0 (max Na (max Nb (max N2 (max N3 N4)))), fun 𝔪 h𝔪 hS χ => ?_⟩
  have mono : ∀ N, N ≤ max N0 (max Na (max Nb (max N2 (max N3 N4)))) → SmallPrimesDvd N 𝔪 :=
    fun N hN P hP hP0 hPN => hS P hP hP0 (hPN.trans hN)
  obtain ⟨g⟩ := h0 𝔪 h𝔪 (mono _ (by omega))
  obtain ⟨W₁, hW₁, hW₁1⟩ := L2_bump
  obtain ⟨V, M, hV, hM, hM6, hsum⟩ := h2 𝔪 h𝔪 (mono _ (by omega)) χ g W₁ hW₁
  have hA := ha 𝔪 h𝔪 (mono _ (by omega)) g W₁ V hW₁ hV
  have hB : ∀ c₁ c₂ ε : ℝ, 0 < c₁ → 0 < ε → ∃ C : ℝ, ∀ Z : ℝ, 2 ≤ Z →
      ∃ σ : ℝ, HasSum (fun r : {r : RowClass 𝔪 //
          c₁ * Z ^ ((1033 : ℝ) / 1000) ≤ Ideal.absNorm r.1.1 ∧
          (Ideal.absNorm r.1.1 : ℝ) ≤ c₂ * Z ^ ((1033 : ℝ) / 1000)} =>
            ‖χ.thetaSum g (rowElt g r.1) Z‖ ^ 2) σ ∧
        σ ≤ C * Z ^ (2 * ((1033 : ℝ) / 1000) - 1 + ε) := by
    intro c₁ c₂ ε hc₁ hε
    obtain ⟨C, hC⟩ := hb 𝔪 h𝔪 (mono _ (by omega)) χ g c₁ c₂ ε hc₁ hε
    exact ⟨C, fun Z hZ => (hC Z hZ).2⟩
  obtain ⟨C₁, hI⟩ := L2_probe_le χ g W₁ V hW₁ hV hA hB
  obtain ⟨C₂, Z₂, hJ₁⟩ := h3 𝔪 h𝔪 (mono _ (by omega)) χ g W₁ M hW₁ hM
  obtain ⟨C₃, Z₃, hJr⟩ := h4 𝔪 h𝔪 (mono _ (by omega)) χ g W₁ M hW₁ hM
  have hc₀ := L2_constant_ne_zero 𝔪 h𝔪 W₁ M hW₁1 hM6
  refine L2_final (I := fun Z => χ.probe g W₁ V (Z ^ ((9 : ℝ) / 10)) (Z ^ ((133 : ℝ) / 1000)) Z)
    (J₁ := fun Z => χ.rowIntegral g W₁ M (principalFreq 𝔪) (Z ^ ((9 : ℝ) / 10))
      (Z ^ ((133 : ℝ) / 1000)) Z)
    (Jr := fun Z => ∑' r : {r : FreqClass 𝔪 // r ≠ principalFreq 𝔪},
      χ.rowIntegral g W₁ M r.1 (Z ^ ((9 : ℝ) / 10)) (Z ^ ((133 : ℝ) / 1000)) Z)
    hc₀ hI ?_ hJ₁ hJr
  intro Z hZ
  have hZ0 : 0 < Z := by linarith
  have hs := hsum (Z ^ ((9 : ℝ) / 10)) (Z ^ ((133 : ℝ) / 1000)) Z (Real.rpow_pos_of_pos hZ0 _)
    (Real.rpow_pos_of_pos hZ0 _) hZ0
  rw [← hs.tsum_eq, ← hs.summable.tsum_subtype_add_tsum_subtype_compl {principalFreq 𝔪}]
  congr 1
  exact tsum_singleton (α := ℂ) (principalFreq 𝔪) (fun r => χ.rowIntegral g W₁ M r
    (Z ^ ((9 : ℝ) / 10)) (Z ^ ((133 : ℝ) / 1000)) Z)
end
