-- Prove2me | Definitions.Def_RPLib_S3_EllW2H
-- name    : RPLib_S3_EllW2H
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:17:48.07751+00:00
-- url     : https://prove2.me/theorems/608b7f34-8092-45f8-ba7d-fadff268aedf
-- title:
--   The Eichler-Selberg trace formula in weight two: split/parabolic and non-split parts of `KtilS`, `s → 0+` on `𝒟_Y`
-- statement:
--   Split/parabolic and non-split parts of `KtilS`, `s → 0+` on `𝒟_Y`.
--
--   * `termP`, `SPS` (`IsSP`), `NHS` (`¬ IsSP`); `summable_termP` (`s > 0`), `KtilS_split`.
--   * `norm_termSP_le`: on `InK Y`, `‖termP IsSP s z g‖ ≤ C_Y · [det g = n ∧ IsSP g] N(g)⁻¹` for `s ≥ 0`.
--   * `tendsto_SPS`, **`tendsto_trunc_SPS`** (DCT): `∫_{𝒟_Y} SPS_s → ∫_{𝒟_Y} SPS_0`.
--   * **`tendsto_trunc_NHS`**: `∫_{𝒟_Y} NHS_s → Σ_c ∫_{𝒟_Y} restPart0 (c.out⁻¹ τ) - ∫_{𝒟_Y} SPS_0`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2F
import Definitions.Def_RPLib_S3_EllW2G2

/-!
# S3-ES-Wt2 (O6, part H): split/parabolic and non-split parts of `KtilS`, `s → 0+` on `𝒟_Y`

* `termP`, `SPS` (`IsSP`), `NHS` (`¬ IsSP`); `summable_termP` (`s > 0`), `KtilS_split`.
* `norm_termSP_le`: on `InK Y`, `‖termP IsSP s z g‖ ≤ C_Y · [det g = n ∧ IsSP g] N(g)⁻¹` for `s ≥ 0`.
* `tendsto_SPS`, **`tendsto_trunc_SPS`** (DCT): `∫_{𝒟_Y} SPS_s → ∫_{𝒟_Y} SPS_0`.
* **`tendsto_trunc_NHS`**: `∫_{𝒟_Y} NHS_s → Σ_c ∫_{𝒟_Y} restPart0 (c.out⁻¹ τ) - ∫_{𝒟_Y} SPS_0`.
-/

open MeasureTheory Metric Set Filter Complex UpperHalfPlane CongruenceSubgroup
open scoped Real ComplexConjugate NNReal ENNReal Manifold MatrixGroups Topology Modular Pointwise
  RamanujanPetersson.S3.Conj

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Bergman RamanujanPetersson.Kernel RP.FundDomain RP.Petersson
  RamanujanPetersson.EllTerm RamanujanPetersson.KernelSD

attribute [local instance] measurableConstSMul_pgl smulInvariantMeasure_pgl

variable {M : ℕ}

open Classical in
/-- The `P`-part of the `KtilS` summand. -/
def termP (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (P : S3.Conj.Mat → Prop) (s : ℝ) (z : ℍ)
    (g : S3.Conj.Mat) : ℂ :=
  if g.det = n ∧ HypPar.IsRest g ∧ P g then ((S3.levelCount M δ' g : ℂ) / 2) * phiGS 2 s g z else 0

/-- Split and parabolic part of `KtilS`. -/
def SPS (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (s : ℝ) (z : ℍ) : ℂ :=
  ∑' g : S3.Conj.Mat, termP M n δ' IsSP s z g

/-- Non-split hyperbolic part of `KtilS`. -/
def NHS (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (s : ℝ) (z : ℍ) : ℂ :=
  ∑' g : S3.Conj.Mat, termP M n δ' (fun g => ¬ IsSP g) s z g

lemma summable_norm_phiGS_det {s : ℝ} (hs : 0 < s) {n : ℤ} (hn : 0 < n) (z : ℍ) :
    Summable ({g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n}.indicator fun g => ‖phiGS 2 s g z‖) := by
  have hσ : 1 < ((2 : ℕ) : ℝ) / 2 + s := by norm_num; linarith
  have h := summable_phiGS (M := 1) 2 hσ hn (0 : ZMod 1) z
  haveI : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.2 rfl
  have hD : DeltaSet 1 n 0 = {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n} := by
    ext g
    show g.det = n ∧ _ ∧ _ ↔ g.det = n
    exact ⟨fun h => h.1, fun h => ⟨h, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  rw [← hD, ← summable_subtype_iff_indicator]
  exact summable_norm_iff.2 h

lemma summable_termP [NeZero M] {s : ℝ} (hs : 0 < s) {n : ℤ} (hn : 0 < n) (δ' : ZMod M)
    (P : S3.Conj.Mat → Prop) (z : ℍ) : Summable (termP M n δ' P s z) := by
  refine Summable.of_norm_bounded
    ((summable_norm_phiGS_det hs hn z).mul_left (Fintype.card (Fin 2 → ZMod M) : ℝ)) (fun g => ?_)
  unfold termP
  split_ifs with h
  · rw [Set.indicator_of_mem (show g ∈ {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n} from h.1), norm_mul]
    have hw := HypPar.norm_wt_le (M := M) n δ' g
    rw [HypPar.wt, if_pos (show g.det = n ∧ HypPar.IsRest g from ⟨h.1, h.2.1⟩)] at hw
    exact mul_le_mul_of_nonneg_right hw (norm_nonneg _)
  · rw [norm_zero]
    exact mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)

lemma KtilS_split [NeZero M] {s : ℝ} (hs : 0 < s) {n : ℤ} (hn : 0 < n) (δ' : ZMod M) (z : ℍ) :
    KtilS M n δ' s z = SPS M n δ' s z + NHS M n δ' s z := by
  rw [SPS, NHS, ← (summable_termP hs hn δ' IsSP z).tsum_add (summable_termP hs hn δ' _ z), KtilS]
  refine tsum_congr fun g => ?_
  unfold termP
  by_cases h : g.det = n ∧ HypPar.IsRest g
  · by_cases hp : IsSP g
    · have h1 : g.det = n ∧ HypPar.IsRest g ∧ IsSP g := ⟨h.1, h.2, hp⟩
      have h2 : ¬ (g.det = n ∧ HypPar.IsRest g ∧ ¬ IsSP g) := fun h' => h'.2.2 hp
      rw [if_pos h, if_pos h1, if_neg h2, add_zero]
    · have h1 : ¬ (g.det = n ∧ HypPar.IsRest g ∧ IsSP g) := fun h' => hp h'.2.2
      have h2 : g.det = n ∧ HypPar.IsRest g ∧ ¬ IsSP g := ⟨h.1, h.2, hp⟩
      rw [if_pos h, if_neg h1, if_pos h2, zero_add]
  · have h1 : ¬ (g.det = n ∧ HypPar.IsRest g ∧ IsSP g) := fun h' => h ⟨h'.1, h'.2.1⟩
    have h2 : ¬ (g.det = n ∧ HypPar.IsRest g ∧ ¬ IsSP g) := fun h' => h ⟨h'.1, h'.2.1⟩
    rw [if_neg h, if_neg h1, if_neg h2, add_zero]

lemma measurable_SPS [NeZero M] {s : ℝ} (hs : 0 < s) {n : ℤ} (hn : 0 < n) (δ' : ZMod M) :
    Measurable (SPS M n δ' s) := by
  have : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  show Measurable fun z => ∑' g : S3.Conj.Mat, termP M n δ' IsSP s z g
  refine measurable_tsum_of_summable (f := fun g z => termP M n δ' IsSP s z g) (fun g => ?_)
    (fun z => summable_termP hs hn δ' IsSP z)
  unfold termP
  exact Measurable.ite (MeasurableSet.const _) ((measurable_phiGS 2 s g).const_mul _) measurable_const

lemma norm_termSP_le [NeZero M] {s : ℝ} (hs : 0 ≤ s) {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {Y : ℝ}
    (hY : 1 ≤ Y) (z : ℍ) (hz : HypPar.InK Y (z : ℂ)) (g : S3.Conj.Mat) :
    ‖termP M n δ' IsSP s z g‖ ≤ (Fintype.card (Fin 2 → ZMod M) : ℝ) * (Y ^ 2 * (144 * Y ^ 4) ^ 2) *
      {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n ∧ IsSP g}.indicator (HypPar.Eg 2) g := by
  unfold termP
  split_ifs with h
  · rw [Set.indicator_of_mem (show g ∈ {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n ∧ IsSP g} from
      ⟨h.1, h.2.2⟩), norm_mul]
    have hw := HypPar.norm_wt_le (M := M) n δ' g
    rw [HypPar.wt, if_pos (show g.det = n ∧ HypPar.IsRest g from ⟨h.1, h.2.1⟩)] at hw
    have hdet : 0 < g.det := by rw [h.1]; exact hn
    have hp := (norm_phiGS_le 2 hs hdet z).trans (HypPar.norm_phiG_le_K hdet 2 hY z hz)
    calc _ ≤ (Fintype.card (Fin 2 → ZMod M) : ℝ) * (Y ^ 2 * (144 * Y ^ 4) ^ 2 * HypPar.Eg 2 g) :=
          mul_le_mul hw hp (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · rw [norm_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (Set.indicator_nonneg (fun g _ => HypPar.Eg_nonneg 2 g) g)

lemma volume_trunc_ne_top (Y : ℝ) : volume (𝒟 ∩ {z : ℍ | z.im ≤ Y}) ≠ ∞ :=
  (lt_of_le_of_lt (measure_mono inter_subset_left) volume_fd_lt_top).ne

lemma inK_of_trunc {Y : ℝ} {τ : ℍ} (hτ : τ ∈ 𝒟 ∩ {z : ℍ | z.im ≤ Y}) : HypPar.InK Y (τ : ℂ) :=
  ⟨(fd_subset_strip hτ.1).1, (fd_subset_strip hτ.1).2, hτ.2⟩

lemma SPS_bound [NeZero M] {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {Y : ℝ} (hY : 1 ≤ Y) :
    ∃ K : ℝ, ∀ s : ℝ, 0 ≤ s → ∀ τ ∈ 𝒟 ∩ {z : ℍ | z.im ≤ Y}, ‖SPS M n δ' s τ‖ ≤ K :=
  ⟨∑' g : Matrix (Fin 2) (Fin 2) ℤ, (Fintype.card (Fin 2 → ZMod M) : ℝ) * (Y ^ 2 * (144 * Y ^ 4) ^ 2) *
      {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n ∧ IsSP g}.indicator (HypPar.Eg 2) g,
    fun s hs τ hτ => by
      unfold SPS
      exact tsum_of_norm_bounded ((summable_SP hn).mul_left
        ((Fintype.card (Fin 2 → ZMod M) : ℝ) * (Y ^ 2 * (144 * Y ^ 4) ^ 2))).hasSum
        (fun g => norm_termSP_le hs hn δ' hY τ (inK_of_trunc hτ) g)⟩

lemma integrableOn_SPS [NeZero M] {s : ℝ} (hs : 0 < s) {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {Y : ℝ}
    (hY : 1 ≤ Y) : IntegrableOn (SPS M n δ' s) (𝒟 ∩ {z : ℍ | z.im ≤ Y}) := by
  obtain ⟨K, hK⟩ := SPS_bound hn δ' hY
  exact Integrable.mono' (integrableOn_const (C := K) (volume_trunc_ne_top Y) enorm_ne_top)
    (measurable_SPS hs hn δ').aestronglyMeasurable
    ((ae_restrict_mem (measurableSet_trunc Y)).mono fun τ hτ => hK s hs.le τ hτ)

lemma tendsto_SPS [NeZero M] {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {Y : ℝ} (hY : 1 ≤ Y) (z : ℍ)
    (hz : HypPar.InK Y (z : ℂ)) :
    Tendsto (fun s => SPS M n δ' s z) (𝓝[>] 0) (𝓝 (SPS M n δ' 0 z)) := by
  unfold SPS
  refine tendsto_tsum_of_dominated_convergence
    ((summable_SP hn).mul_left ((Fintype.card (Fin 2 → ZMod M) : ℝ) * (Y ^ 2 * (144 * Y ^ 4) ^ 2)))
    (fun g => ?_) ?_
  · unfold termP
    split_ifs with h
    · have hdet : 0 < g.det := by rw [h.1]; exact hn
      rw [phiGS_zero]
      exact (tendsto_phiGS 2 hdet z).const_mul _
    · exact tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs g
    exact norm_termSP_le (le_of_lt hs) hn δ' hY z hz g

/-- **DCT on `𝒟_Y`**: `∫_{𝒟 ∩ {Im ≤ Y}} SPS_s → ∫_{𝒟 ∩ {Im ≤ Y}} SPS_0` as `s → 0+`. -/
theorem tendsto_trunc_SPS [NeZero M] {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {Y : ℝ} (hY : 1 ≤ Y) :
    Tendsto (fun s => ∫ τ in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, SPS M n δ' s τ) (𝓝[>] 0)
      (𝓝 (∫ τ in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, SPS M n δ' 0 τ)) := by
  have hmT := measurableSet_trunc Y
  obtain ⟨K, hK⟩ := SPS_bound hn δ' hY
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => K) ?_ ?_
    (integrableOn_const (C := K) (volume_trunc_ne_top Y) enorm_ne_top) ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact (measurable_SPS hs hn δ').aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact (ae_restrict_mem hmT).mono fun τ hτ => hK s (le_of_lt hs) τ hτ
  · exact (ae_restrict_mem hmT).mono fun τ hτ => tendsto_SPS hn δ' hY τ (inK_of_trunc hτ)

/-- **The non-split limit on `𝒟_Y`** (by subtraction). -/
theorem tendsto_trunc_NHS [NeZero M] (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M)
    (δ : (ZMod M)ˣ) [Fintype (SL(2, ℤ) ⧸ pmSL (Gamma1 M))] {Y : ℝ} (hY : 1 ≤ Y) :
    Tendsto (fun s => ∫ τ in 𝒟 ∩ {z : ℍ | z.im ≤ Y},
        NHS M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) s τ) (𝓝[>] 0)
      (𝓝 ((∑ c : SL(2, ℤ) ⧸ pmSL (Gamma1 M),
        ∫ τ in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, restPart0 M n δ (c.out⁻¹ • τ)) -
          ∫ τ in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, SPS M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) 0 τ)) := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  refine ((tendsto_trunc_KtilS hM hn hnM δ Y).sub (tendsto_trunc_SPS hn' _ hY)).congr' ?_
  filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with s hs
  have hKi := (integral_trunc_KtilS hM hn hnM δ Y hs.1 hs.2).1
  have hSi := integrableOn_SPS hs.1 hn' ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) hY
  rw [← integral_sub hKi hSi]
  refine setIntegral_congr_fun₀ (measurableSet_trunc Y).nullMeasurableSet fun τ _ => ?_
  show KtilS M n _ s τ - SPS M n _ s τ = NHS M n _ s τ
  rw [KtilS_split hs.1 hn' _ τ]
  ring

end RamanujanPetersson.EllW2


