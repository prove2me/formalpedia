-- Prove2me | Definitions.Def_RPLib_S3_EllW2RU2
-- name    : RPLib_S3_EllW2RU2
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:29:08.29819+00:00
-- url     : https://prove2.me/theorems/ee488a86-41d4-40b2-b3a7-46e06f11dcb4
-- title:
--   The Eichler-Selberg trace formula in weight two: unfolding the lattice count against `SL(2, ℤ)`-invariant functions
-- statement:
--   Unfolding the lattice count against `SL(2, ℤ)`-invariant functions.
--
--   For `F ≥ 0` measurable and `SL(2, ℤ)`-invariant:
--   * `lintegral_fd_mul_cp`: `∫_𝒟 F · #{(c, d) coprime : Y |c z + d|² ≤ im z} = 2 ∫_{S_Y} F`;
--   * `eCnt y0 z = #{(c, d) ≠ 0 : y0 |c z + d|² ≤ im z}` and `eCnt_eq_tsum`: `eCnt y0 = Σ_{m ≥ 1} cp(m² y0)`;
--   * `lintegral_fd_mul_eCnt`: `∫_𝒟 F · eCnt y0 = Σ_{m ≥ 1} 2 ∫_{S_{m² y0}} F`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; H. Iwaniec, Spectral Methods of Automorphic Forms, 2nd ed., Graduate Studies in Mathematics 53, AMS 2002, Chapter 2

import Mathlib
import Definitions.Def_RPLib_S3_EllW2RU1

/-!
# S3-ES-Wt2 (RU2): unfolding the lattice count against `SL(2, ℤ)`-invariant functions

For `F ≥ 0` measurable and `SL(2, ℤ)`-invariant:
* `lintegral_fd_mul_cp`: `∫_𝒟 F · #{(c, d) coprime : Y |c z + d|² ≤ im z} = 2 ∫_{S_Y} F`;
* `eCnt y0 z = #{(c, d) ≠ 0 : y0 |c z + d|² ≤ im z}` and `eCnt_eq_tsum`: `eCnt y0 = Σ_{m ≥ 1} cp(m² y0)`;
* `lintegral_fd_mul_eCnt`: `∫_𝒟 F · eCnt y0 = Σ_{m ≥ 1} 2 ∫_{S_{m² y0}} F`.
-/

set_option autoImplicit false

open MeasureTheory UpperHalfPlane ModularGroup RP.FundDomain Function
open scoped MatrixGroups ENNReal Pointwise Modular

attribute [local instance] measurableConstSMul_pgl smulInvariantMeasure_pgl
  smulInvariantMeasure_subgroup

noncomputable section

namespace RamanujanPetersson.EllW2

lemma measurableSet_stripH (Y : ℝ) : MeasurableSet (stripH Y) := by
  have hre : Measurable (fun w : ℍ => w.re) := UpperHalfPlane.continuous_re.measurable
  have him : Measurable (fun w : ℍ => w.im) := UpperHalfPlane.continuous_im.measurable
  exact (measurableSet_le measurable_const hre).inter
    ((measurableSet_lt hre measurable_const).inter (measurableSet_le measurable_const him))

lemma measurable_cpInd (Y : ℝ) (p : ℤ × ℤ) : Measurable fun z : ℍ => cpInd Y z p := by
  unfold cpInd
  by_cases hp : IsCoprime p.1 p.2
  · simp only [hp, true_and]
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_le (continuous_const.mul (Complex.continuous_normSq.comp
      ((continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const))).measurable
      UpperHalfPlane.continuous_im.measurable
  · simp only [hp, false_and, ↓reduceIte]
    exact measurable_const

/-- **Unfolding**: `∫_𝒟 F · #{(c, d) coprime : Y |c z + d|² ≤ im z} = 2 ∫_{S_Y} F`. -/
theorem lintegral_fd_mul_cp {F : ℍ → ℝ≥0∞} (hF : Measurable F)
    (hinv : ∀ (γ : SL(2, ℤ)) (z : ℍ), F (γ • z) = F z) (Y : ℝ) :
    ∫⁻ z in 𝒟, F z * ∑' p : ℤ × ℤ, cpInd Y z p = 2 * ∫⁻ z in stripH Y, F z := by
  have := countable_PSL2Z
  have hS := measurableSet_stripH Y
  have hinvG : ∀ (g : PSL2Z) (z : ℍ), F ((g : PGL(2, ℝ)) • z) = F z := by
    intro g z
    obtain ⟨γ, hγ⟩ := mem_PSL2Z.1 g.2
    rw [← hγ, toPGLR_smul, hinv]
  have hterm : ∀ (g : PSL2Z) (z : ℍ), (stripH Y).indicator F (g • z) =
      F z * (stripH Y).indicator 1 ((g : PGL(2, ℝ)) • z) := by
    intro g z
    by_cases h : (g : PGL(2, ℝ)) • z ∈ stripH Y
    · rw [Set.indicator_of_mem (show g • z ∈ stripH Y from h), Set.indicator_of_mem h,
        Pi.one_apply, mul_one]
      exact hinvG g z
    · rw [Set.indicator_of_notMem (show g • z ∉ stripH Y from h), Set.indicator_of_notMem h,
        mul_zero]
  have hmeas : ∀ g : PSL2Z,
      Measurable fun z : ℍ => F z * (stripH Y).indicator 1 ((g : PGL(2, ℝ)) • z) := fun g =>
    hF.mul ((measurable_one.indicator hS).comp (measurable_const_smul (g : PGL(2, ℝ))))
  calc ∫⁻ z in 𝒟, F z * ∑' p : ℤ × ℤ, cpInd Y z p
      = ∫⁻ z in 𝒟, 2 * ∑' g : PSL2Z, F z * (stripH Y).indicator 1 ((g : PGL(2, ℝ)) • z) := by
        refine lintegral_congr fun z => ?_
        rw [← two_mul_tsum_PSL_strip, ENNReal.tsum_mul_left]; ring
    _ = 2 * ∑' g : PSL2Z, ∫⁻ z in 𝒟, F z * (stripH Y).indicator 1 ((g : PGL(2, ℝ)) • z) := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_tsum fun g => (hmeas g).aemeasurable]
    _ = 2 * ∫⁻ z in stripH Y, F z := by
        rw [← lintegral_indicator hS,
          isFundamentalDomain_fd.lintegral_eq_tsum'' ((stripH Y).indicator F)]
        congr 1
        refine tsum_congr fun g => lintegral_congr fun z => ?_
        exact (hterm g z).symm

/-- `E_{y0}(z) = #{(c, d) ≠ 0 : y0 |c z + d|² ≤ im z}`. -/
def eCnt (y0 : ℝ) (z : ℍ) : ℝ≥0∞ :=
  ∑' q : ℤ × ℤ, if q ≠ 0 ∧ y0 * Complex.normSq ((q.1 : ℂ) * (z : ℂ) + q.2) ≤ z.im then 1 else 0

lemma normSq_scale (k : ℤ) (p : ℤ × ℤ) (z : ℍ) :
    Complex.normSq (((k * p.1 : ℤ) : ℂ) * (z : ℂ) + ((k * p.2 : ℤ) : ℂ)) =
      (k : ℝ) ^ 2 * Complex.normSq ((p.1 : ℂ) * (z : ℂ) + p.2) := by
  have h : (((k * p.1 : ℤ) : ℂ) * (z : ℂ) + ((k * p.2 : ℤ) : ℂ)) =
      ((k : ℝ) : ℂ) * ((p.1 : ℂ) * (z : ℂ) + p.2) := by push_cast; ring
  rw [h, Complex.normSq_mul, Complex.normSq_ofReal]; ring

lemma cpInd_ne_zero {Y : ℝ} {z : ℍ} {p : ℤ × ℤ} (h : cpInd Y z p ≠ 0) :
    IsCoprime p.1 p.2 ∧ Y * Complex.normSq ((p.1 : ℂ) * (z : ℂ) + p.2) ≤ z.im := by
  unfold cpInd at h
  split_ifs at h with h'
  · exact h'
  · exact absurd rfl h

/-- The scaling map `(m, p) ↦ (m + 1) p`. -/
def scl (x : ℕ × (ℤ × ℤ)) : ℤ × ℤ := (((x.1 : ℤ) + 1) * x.2.1, ((x.1 : ℤ) + 1) * x.2.2)

/-- **`E_{y0} = Σ_{m ≥ 1} #{(c, d) coprime : m² y0 |c z + d|² ≤ im z}`.** -/
theorem eCnt_eq_tsum (y0 : ℝ) (z : ℍ) :
    eCnt y0 z = ∑' m : ℕ, ∑' p : ℤ × ℤ, cpInd (((m : ℝ) + 1) ^ 2 * y0) z p := by
  rw [← ENNReal.tsum_prod]
  unfold eCnt
  have hk : ∀ m : ℕ, (((m : ℤ) + 1 : ℤ) : ℝ) = (m : ℝ) + 1 := fun m => by push_cast; ring
  refine tsum_eq_tsum_of_ne_zero_bij (fun x => scl x.1) ?_ ?_ ?_
  · rintro ⟨⟨m, p⟩, hx⟩ ⟨⟨m', p'⟩, hx'⟩ hxx
    have hc := (cpInd_ne_zero hx).1
    have hc' := (cpInd_ne_zero hx').1
    simp only [scl, Prod.mk.injEq] at hxx
    obtain ⟨h1, h2⟩ := hxx
    have hg : Int.gcd (((m : ℤ) + 1) * p.1) (((m : ℤ) + 1) * p.2) =
        Int.gcd (((m' : ℤ) + 1) * p'.1) (((m' : ℤ) + 1) * p'.2) := by rw [h1, h2]
    rw [Int.gcd_mul_left, Int.gcd_mul_left, Int.isCoprime_iff_gcd_eq_one.1 hc,
      Int.isCoprime_iff_gcd_eq_one.1 hc'] at hg
    have hmm : m = m' := by omega
    subst hmm
    have hne : ((m : ℤ) + 1) ≠ 0 := by omega
    have e1 : p.1 = p'.1 := mul_left_cancel₀ hne h1
    have e2 : p.2 = p'.2 := mul_left_cancel₀ hne h2
    exact Subtype.ext (Prod.ext rfl (Prod.ext e1 e2))
  · intro q hq
    have hq' : q ≠ 0 ∧ y0 * Complex.normSq ((q.1 : ℂ) * (z : ℂ) + q.2) ≤ z.im := by
      by_contra hc; exact hq (if_neg hc)
    have hq0 : q.1 ≠ 0 ∨ q.2 ≠ 0 := by
      by_contra hc; push_neg at hc; exact hq'.1 (Prod.ext hc.1 hc.2)
    obtain ⟨d, hd⟩ : ∃ d : ℕ, d = Int.gcd q.1 q.2 := ⟨_, rfl⟩
    have hdpos : 0 < d := hd ▸ Int.gcd_pos_iff.2 hq0
    have hdk : (((d - 1 : ℕ) : ℤ) + 1) = (d : ℤ) := by omega
    subst hd
    obtain ⟨p, hp⟩ : ∃ p : ℤ × ℤ, p = (q.1 / (Int.gcd q.1 q.2 : ℤ), q.2 / (Int.gcd q.1 q.2 : ℤ)) :=
      ⟨_, rfl⟩
    have hpc : IsCoprime p.1 p.2 := by
      rw [hp]; exact Int.isCoprime_iff_gcd_eq_one.2 (Int.gcd_div_gcd_div_gcd hdpos)
    have hq1 : ((Int.gcd q.1 q.2 : ℕ) : ℤ) * p.1 = q.1 := by
      rw [hp]; exact Int.mul_ediv_cancel' (Int.gcd_dvd_left ..)
    have hq2 : ((Int.gcd q.1 q.2 : ℕ) : ℤ) * p.2 = q.2 := by
      rw [hp]; exact Int.mul_ediv_cancel' (Int.gcd_dvd_right ..)
    have hsc : scl (Int.gcd q.1 q.2 - 1, p) = q := by
      simp only [scl]; rw [hdk, hq1, hq2]
    have hmem : cpInd ((((Int.gcd q.1 q.2 - 1 : ℕ) : ℝ) + 1) ^ 2 * y0) z p ≠ 0 := by
      unfold cpInd
      rw [if_pos]
      · exact one_ne_zero
      refine ⟨hpc, ?_⟩
      have h3 := hq'.2
      rw [← hsc, scl, normSq_scale, hk] at h3
      simp only at h3
      linarith
    exact ⟨⟨(Int.gcd q.1 q.2 - 1, p), hmem⟩, hsc⟩
  · rintro ⟨⟨m, p⟩, hx⟩
    have hc := cpInd_ne_zero hx
    simp only
    rw [cpInd, if_pos hc, if_pos]
    refine ⟨?_, ?_⟩
    · intro h0
      have h1 := congrArg Prod.fst h0
      have h2 := congrArg Prod.snd h0
      simp only [scl, Prod.fst_zero, Prod.snd_zero, mul_eq_zero] at h1 h2
      have hne : ((m : ℤ) + 1) ≠ 0 := by omega
      have hp1 : p.1 = 0 := h1.resolve_left hne
      have hp2 : p.2 = 0 := h2.resolve_left hne
      have := hc.1
      rw [hp1, hp2] at this
      exact not_isCoprime_zero_zero this
    · have h3 := hc.2
      rw [scl, normSq_scale, hk]
      linarith

/-- **`∫_𝒟 F · E_{y0} = Σ_{m ≥ 1} 2 ∫_{S_{m² y0}} F`.** -/
theorem lintegral_fd_mul_eCnt {F : ℍ → ℝ≥0∞} (hF : Measurable F)
    (hinv : ∀ (γ : SL(2, ℤ)) (z : ℍ), F (γ • z) = F z) (y0 : ℝ) :
    ∫⁻ z in 𝒟, F z * eCnt y0 z =
      ∑' m : ℕ, 2 * ∫⁻ z in stripH (((m : ℝ) + 1) ^ 2 * y0), F z := by
  have h1 : ∀ z, F z * eCnt y0 z =
      ∑' m : ℕ, F z * ∑' p : ℤ × ℤ, cpInd (((m : ℝ) + 1) ^ 2 * y0) z p := by
    intro z; rw [eCnt_eq_tsum, ENNReal.tsum_mul_left]
  have hm : ∀ m : ℕ, Measurable fun z : ℍ =>
      F z * ∑' p : ℤ × ℤ, cpInd (((m : ℝ) + 1) ^ 2 * y0) z p := fun m =>
    hF.mul (Measurable.ennreal_tsum fun p => measurable_cpInd _ p)
  rw [lintegral_congr h1, lintegral_tsum fun m => (hm m).aemeasurable]
  exact tsum_congr fun m => lintegral_fd_mul_cp hF hinv _

end RamanujanPetersson.EllW2


