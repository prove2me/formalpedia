-- Prove2me | Definitions.Def_RPLib_S3_EllW2B
-- name    : RPLib_S3_EllW2B
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:30:59.436024+00:00
-- url     : https://prove2.me/theorems/a9d35c3b-30f7-4b9e-b960-ee0f909564f4
-- title:
--   The Eichler-Selberg trace formula in weight two: the Hecke-regularised diagonal near `s = 0`
-- statement:
--   The Hecke-regularised diagonal near `s = 0`.
--
--   The diagonal of the Hecke-trick kernel `ω_s` is `Σ_{g ∈ Δ} φ_g(z) ratQ(g; z, -z̄)^s` with `0 < ratQ ≤ 1/4`.
--
--   * `ratio_le_quarter`, `ratQ_diag_pos`, `ratQ_diag_le`, `ratQ_scal` (`= 1/4` on scalar matrices).
--   * `phiGS`, `phiGS_zero`, `norm_phiGS_le` (`s ≥ 0`), `tendsto_phiGS` (`s → 0+`), `diagS_eq`.
--   * `scalPartS`, `ellPartS`, `restPartS`, `scalPartS_eq`, `diagS_split` (`1 < k/2 + s`).
--   * `ellDom`, `integrableOn_ellDom`, `EllSum`, `ae_ellSum`, `ellPartS_split`, `norm_ellPartS_le`,
--     `tendsto_ellPartS` (dominated convergence family by family), `tendsto_ellPartS_ae`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2A
import Definitions.Def_RPLib_S3_KernelSB

/-!
# S3-ES-Wt2 (O5, part B): the Hecke-regularised diagonal near `s = 0`

The diagonal of the Hecke-trick kernel `ω_s` is `Σ_{g ∈ Δ} φ_g(z) ratQ(g; z, -z̄)^s` with `0 < ratQ ≤ 1/4`.

* `ratio_le_quarter`, `ratQ_diag_pos`, `ratQ_diag_le`, `ratQ_scal` (`= 1/4` on scalar matrices).
* `phiGS`, `phiGS_zero`, `norm_phiGS_le` (`s ≥ 0`), `tendsto_phiGS` (`s → 0+`), `diagS_eq`.
* `scalPartS`, `ellPartS`, `restPartS`, `scalPartS_eq`, `diagS_split` (`1 < k/2 + s`).
* `ellDom`, `integrableOn_ellDom`, `EllSum`, `ae_ellSum`, `ellPartS_split`, `norm_ellPartS_le`,
  `tendsto_ellPartS` (dominated convergence family by family), `tendsto_ellPartS_ae`.
-/

open MeasureTheory Metric Set Filter Complex UpperHalfPlane CongruenceSubgroup
open scoped Real ComplexConjugate NNReal ENNReal Manifold MatrixGroups Topology

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Bergman RamanujanPetersson.Kernel RP.FundDomain RP.Petersson
  RamanujanPetersson.EllTerm

variable {M : ℕ}

/-! ## Part 1: the point-pair ratio on the diagonal -/

lemma ratio_le_quarter {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) : BergmanS.ratio z w ≤ 1 / 4 := by
  have e : (z - conj w).im = z.im + w.im := by simp
  have h := Complex.abs_im_le_norm (z - conj w)
  rw [e] at h
  have hle : (z.im + w.im) ^ 2 ≤ ‖z - conj w‖ ^ 2 := by
    calc (z.im + w.im) ^ 2 = |z.im + w.im| ^ 2 := (sq_abs _).symm
      _ ≤ ‖z - conj w‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  have hpos : 0 < ‖z - conj w‖ ^ 2 := lt_of_lt_of_le (by positivity) hle
  rw [BergmanS.ratio, div_le_iff₀ hpos]
  nlinarith [sq_nonneg (z.im - w.im)]

lemma ratQ_diag_pos {g : Matrix (Fin 2) (Fin 2) ℤ} (h : 0 < g.det) (z : ℍ) :
    0 < KernelS.ratQ g z (-conj (z : ℂ)) := by
  rw [KernelS.ratQ_negConj h z z]
  exact BergmanS.ratio_pos z.im_pos (adjPt g z).im_pos

lemma ratQ_diag_le {g : Matrix (Fin 2) (Fin 2) ℤ} (h : 0 < g.det) (z : ℍ) :
    KernelS.ratQ g z (-conj (z : ℂ)) ≤ 1 / 4 := by
  rw [KernelS.ratQ_negConj h z z]
  exact ratio_le_quarter z.im_pos (adjPt g z).im_pos

lemma ratQ_scal {g : Matrix (Fin 2) (Fin 2) ℤ} (hS : g 1 0 = 0 ∧ g 0 1 = 0 ∧ g 0 0 = g 1 1)
    (h : 0 < g.det) (z : ℍ) : KernelS.ratQ g z (-conj (z : ℂ)) = 1 / 4 := by
  obtain ⟨h10, h01, hd⟩ := hS
  have ha : (g 0 0 : ℝ) ≠ 0 := by
    rw [Matrix.det_fin_two, h10, h01, ← hd] at h
    have : g 0 0 ≠ 0 := by
      rintro h0
      rw [h0] at h
      simp at h
    exact_mod_cast this
  have hy : (z : ℂ).im ≠ 0 := z.im_pos.ne'
  have hQ : Q g (z : ℂ) (-conj (z : ℂ)) = ((2 * (g 0 0 : ℝ) * (z : ℂ).im : ℝ) : ℂ) * Complex.I := by
    rw [Q_neg_conj, h10, h01, ← hd]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have hv : (-conj (z : ℂ)).im = (z : ℂ).im := by simp
  rw [KernelS.ratQ, hQ, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Matrix.det_fin_two, h10, h01, ← hd, hv]
  push_cast
  field_simp
  ring

/-! ## Part 2: the regularised per-matrix integrand -/

/-- `φ_g(z) · ratQ(g; z, -z̄)^s`. -/
def phiGS (k : ℕ) (s : ℝ) (g : Matrix (Fin 2) (Fin 2) ℤ) (z : ℍ) : ℂ :=
  phiG k g z * ((KernelS.ratQ g z (-conj (z : ℂ)) ^ s : ℝ) : ℂ)

lemma phiGS_zero (k : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (z : ℍ) : phiGS k 0 g z = phiG k g z := by
  simp [phiGS]

lemma norm_phiGS_le (k : ℕ) {s : ℝ} (hs : 0 ≤ s) {g : Matrix (Fin 2) (Fin 2) ℤ} (h : 0 < g.det) (z : ℍ) :
    ‖phiGS k s g z‖ ≤ ‖phiG k g z‖ := by
  rw [phiGS, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (ratQ_diag_pos h z).le s)]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (Real.rpow_le_one (ratQ_diag_pos h z).le ((ratQ_diag_le h z).trans (by norm_num)) hs)

lemma tendsto_phiGS (k : ℕ) {g : Matrix (Fin 2) (Fin 2) ℤ} (h : 0 < g.det) (z : ℍ) :
    Tendsto (fun s : ℝ => phiGS k s g z) (𝓝[>] 0) (𝓝 (phiG k g z)) := by
  have h1 : Tendsto (fun s : ℝ => KernelS.ratQ g z (-conj (z : ℂ)) ^ s) (𝓝 0) (𝓝 1) := by
    have := (Real.continuousAt_const_rpow (b := 0) (ratQ_diag_pos h z).ne').tendsto
    rwa [Real.rpow_zero] at this
  have h2 := ((Complex.continuous_ofReal.tendsto 1).comp h1).mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have h3 := (tendsto_const_nhds (x := phiG k g z)).mul h2
  simpa [phiGS, Function.comp_def] using h3

/-- The regularised diagonal as a sum over `Δ`. -/
theorem diagS_eq (k : ℕ) {n : ℤ} (δ' : ZMod M) (s : ℝ) (z : ℍ) :
    conj (KernelS.omegaS M k n δ' s z (-conj (z : ℂ))) * ((z.im : ℂ) ^ k) =
      ∑' g : DeltaSet M n δ', phiGS k s g z := by
  rw [KernelS.omegaS, Complex.conj_tsum, ← tsum_mul_right]
  refine tsum_congr fun g => ?_
  rw [phiGS, phiG, map_mul, Complex.conj_ofReal]
  ring

/-! ## Part 3: the scalar / elliptic / rest split at `s > 0` -/

/-- The regularised scalar part. -/
def scalPartS (k M : ℕ) (n : ℤ) (δ' : ZMod M) (s : ℝ) (z : ℍ) : ℂ :=
  ∑' g : DeltaSet M n δ', if (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0 ∧
    (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 then phiGS k s g z else 0

/-- The regularised elliptic part. -/
def ellPartS (k M : ℕ) (n : ℤ) (δ' : ZMod M) (s : ℝ) (z : ℍ) : ℂ :=
  ∑' g : DeltaSet M n δ', if ((g : S3.Conj.Mat) 0 0 + (g : S3.Conj.Mat) 1 1) ^ 2 < 4 * (g : S3.Conj.Mat).det
    then phiGS k s g z else 0

/-- The regularised hyperbolic + parabolic part. -/
def restPartS (k M : ℕ) (n : ℤ) (δ' : ZMod M) (s : ℝ) (z : ℍ) : ℂ :=
  ∑' g : DeltaSet M n δ', if ¬ (((g : S3.Conj.Mat) 1 0 = 0 ∧ (g : S3.Conj.Mat) 0 1 = 0 ∧
      (g : S3.Conj.Mat) 0 0 = (g : S3.Conj.Mat) 1 1) ∨
      ((g : S3.Conj.Mat) 0 0 + (g : S3.Conj.Mat) 1 1) ^ 2 < 4 * (g : S3.Conj.Mat).det)
    then phiGS k s g z else 0

theorem scalPartS_eq (k M : ℕ) (δ' : ZMod M) {n : ℕ} (hn : 0 < n) (s : ℝ) (z : ℍ) :
    scalPartS k M n δ' s z = scalVal k M n δ' * (((1 / 4 : ℝ) ^ s : ℝ) : ℂ) := by
  rw [← scalPart_eq k M δ' hn z, scalPart, ← tsum_mul_right, scalPartS]
  refine tsum_congr fun g => ?_
  have hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℤ).det := by
    rw [(mem_DeltaSet.1 g.2).1]
    exact_mod_cast hn
  split_ifs with hS
  · rw [phiGS, ratQ_scal hS hg z]
  · rw [zero_mul]

lemma summable_phiGS (k : ℕ) {s : ℝ} (hσ : 1 < (k : ℝ) / 2 + s) {n : ℤ} (hn : 0 < n) (δ' : ZMod M)
    (z : ℍ) : Summable fun g : DeltaSet M n δ' => phiGS k s g z := by
  have hv : 0 < (-conj (z : ℂ)).im := by simpa using z.im_pos
  have h := (Complex.summable_conj.2 (KernelS.summable_omegaS M k hn δ' hσ (z := (z : ℂ))
    (w := -conj (z : ℂ)) z.im_pos hv)).mul_right ((z.im : ℂ) ^ k)
  refine h.congr fun g => ?_
  rw [phiGS, phiG, map_mul, Complex.conj_ofReal]
  ring

lemma summable_iteS (k : ℕ) {s : ℝ} (hσ : 1 < (k : ℝ) / 2 + s) {n : ℤ} (hn : 0 < n) (δ' : ZMod M)
    (z : ℍ) (P : S3.Conj.Mat → Prop) [DecidablePred P] :
    Summable fun g : DeltaSet M n δ' => if P g then phiGS k s g z else 0 := by
  have h := (summable_phiGS k hσ hn δ' z).indicator {g : DeltaSet M n δ' | P g}
  refine h.congr fun g => ?_
  by_cases hP : P g
  · rw [indicator_of_mem (show g ∈ {g : DeltaSet M n δ' | P g} from hP), if_pos hP]
  · rw [indicator_of_notMem (show g ∉ {g : DeltaSet M n δ' | P g} from hP), if_neg hP]

lemma not_ell_of_scal' {g : S3.Conj.Mat} (h : g 1 0 = 0 ∧ g 0 1 = 0 ∧ g 0 0 = g 1 1) :
    ¬ (g 0 0 + g 1 1) ^ 2 < 4 * g.det := by
  obtain ⟨h10, h01, hd⟩ := h
  rw [Matrix.det_fin_two, h10, h01, ← hd]
  nlinarith

/-- **The split of the regularised diagonal** (`1 < k/2 + s`; at `k = 2` this is `s > 0`). -/
theorem diagS_split {k : ℕ} {s : ℝ} (hσ : 1 < (k : ℝ) / 2 + s) {n : ℤ} (hn : 0 < n) (δ' : ZMod M)
    (z : ℍ) :
    conj (KernelS.omegaS M k n δ' s z (-conj (z : ℂ))) * ((z.im : ℂ) ^ k) =
      scalPartS k M n δ' s z + ellPartS k M n δ' s z + restPartS k M n δ' s z := by
  have h1 := summable_iteS k hσ hn δ' z (fun g : S3.Conj.Mat => g 1 0 = 0 ∧ g 0 1 = 0 ∧ g 0 0 = g 1 1)
  have h2 := summable_iteS k hσ hn δ' z (fun g : S3.Conj.Mat => (g 0 0 + g 1 1) ^ 2 < 4 * g.det)
  have h3 := summable_iteS k hσ hn δ' z (fun g : S3.Conj.Mat => ¬ ((g 1 0 = 0 ∧ g 0 1 = 0 ∧ g 0 0 = g 1 1) ∨
      (g 0 0 + g 1 1) ^ 2 < 4 * g.det))
  rw [diagS_eq, scalPartS, ellPartS, restPartS]
  refine (tsum_congr fun g => ?_).trans (((h1.add h2).tsum_add h3).trans
    (congrArg (· + _) (h1.tsum_add h2)))
  try dsimp only
  by_cases hS : (g : S3.Conj.Mat) 1 0 = 0 ∧ (g : S3.Conj.Mat) 0 1 = 0 ∧
      (g : S3.Conj.Mat) 0 0 = (g : S3.Conj.Mat) 1 1
  · rw [if_pos hS, if_neg (not_ell_of_scal' hS), if_neg (fun h => h (Or.inl hS))]
    ring
  · by_cases hE : ((g : S3.Conj.Mat) 0 0 + (g : S3.Conj.Mat) 1 1) ^ 2 < 4 * (g : S3.Conj.Mat).det
    · rw [if_neg hS, if_pos hE, if_neg (fun h => h (Or.inr hE))]
      ring
    · rw [if_neg hS, if_neg hE, if_pos (fun h => h.elim hS hE)]
      ring

/-! ## Part 4: domination and convergence of the elliptic part as `s → 0+` -/

lemma det_pos_of_ell {g : S3.Conj.Mat} (h : (g 0 0 + g 1 1) ^ 2 < 4 * g.det) : 0 < g.det := by
  nlinarith [sq_nonneg (g 0 0 + g 1 1)]

/-- The dominating function: the elliptic family sums of `‖φ_g‖`. -/
def ellDom (m M n : ℕ) (δ' : ZMod M) (z : ℍ) : ℝ :=
  ∑ i ∈ Finset.range (4 * n + 1),
    (∑' x : S3.Conj.EllPos M δ' ((i : ℤ) - 2 * n) n, ‖phiG (m + 2) x z‖ +
      ∑' x : S3.Conj.EllNeg M δ' ((i : ℤ) - 2 * n) n, ‖phiG (m + 2) x z‖)

theorem integrableOn_ellDom [NeZero M] (hM : 3 ≤ M) (m : ℕ) (δ' : ZMod M) (n : ℕ) :
    IntegrableOn (ellDom m M n δ') (fdom (Gamma1 M)) := by
  unfold ellDom
  exact integrable_finsetSum _ fun i _ =>
    (ellPos_norm_int hM m δ' _ n).add (ellNeg_norm_int hM m δ' _ n)

/-- Summability of every elliptic family at `z` (true for a.e. `z` in the fundamental domain). -/
def EllSum (m M n : ℕ) (δ' : ZMod M) (z : ℍ) : Prop :=
  ∀ i : ℕ, Summable (fun x : S3.Conj.EllPos M δ' ((i : ℤ) - 2 * n) n => ‖phiG (m + 2) x z‖) ∧
    Summable (fun x : S3.Conj.EllNeg M δ' ((i : ℤ) - 2 * n) n => ‖phiG (m + 2) x z‖)

theorem ae_ellSum [NeZero M] (hM : 3 ≤ M) (m : ℕ) (δ' : ZMod M) (n : ℕ) :
    ∀ᵐ z ∂(volume.restrict (fdom (Gamma1 M))), EllSum m M n δ' z := by
  have hP := ae_all_iff.2 fun i : ℕ => (ellPos_unfold' hM m δ' ((i : ℤ) - 2 * n) n).1
  have hN := ae_all_iff.2 fun i : ℕ => (ellNeg_unfold' hM m δ' ((i : ℤ) - 2 * n) n).1
  filter_upwards [hP, hN] with z hzP hzN
  exact fun i => ⟨hzP i, hzN i⟩

theorem ellPartS_split {m n : ℕ} (hn : 0 < n) (δ' : ZMod M) {z : ℍ} (hz : EllSum m M n δ' z)
    {s : ℝ} (hs : 0 ≤ s) :
    ellPartS (m + 2) M n δ' s z = ∑ i ∈ Finset.range (4 * n + 1),
      (∑' x : S3.Conj.EllPos M δ' ((i : ℤ) - 2 * n) n, phiGS (m + 2) s x z +
        ∑' x : S3.Conj.EllNeg M δ' ((i : ℤ) - 2 * n) n, phiGS (m + 2) s x z) := by
  rw [ellPartS]
  exact tsum_ell_split δ' hn (fun g => phiGS (m + 2) s g z)
    (fun i => Summable.of_norm_bounded (hz i).1 fun x =>
      norm_phiGS_le _ hs (det_pos_of_ell (of_EllPos x.2).2.1) z)
    (fun i => Summable.of_norm_bounded (hz i).2 fun x =>
      norm_phiGS_le _ hs (det_pos_of_ell (of_EllNeg x.2).2.1) z)

theorem norm_ellPartS_le {m n : ℕ} (hn : 0 < n) (δ' : ZMod M) {z : ℍ} (hz : EllSum m M n δ' z)
    {s : ℝ} (hs : 0 ≤ s) : ‖ellPartS (m + 2) M n δ' s z‖ ≤ ellDom m M n δ' z := by
  rw [ellPartS_split hn δ' hz hs, ellDom]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact tsum_of_norm_bounded (hz i).1.hasSum fun x =>
      norm_phiGS_le _ hs (det_pos_of_ell (of_EllPos x.2).2.1) z
  · exact tsum_of_norm_bounded (hz i).2.hasSum fun x =>
      norm_phiGS_le _ hs (det_pos_of_ell (of_EllNeg x.2).2.1) z

theorem tendsto_ellPartS {m n : ℕ} (hn : 0 < n) (δ' : ZMod M) {z : ℍ} (hz : EllSum m M n δ' z) :
    Tendsto (fun s => ellPartS (m + 2) M n δ' s z) (𝓝[>] 0) (𝓝 (ellPart (m + 2) M n δ' z)) := by
  have hE : ellPart (m + 2) M n δ' z = ∑ i ∈ Finset.range (4 * n + 1),
      (∑' x : S3.Conj.EllPos M δ' ((i : ℤ) - 2 * n) n, phiG (m + 2) x z +
        ∑' x : S3.Conj.EllNeg M δ' ((i : ℤ) - 2 * n) n, phiG (m + 2) x z) := by
    rw [ellPart]
    exact tsum_ell_split δ' hn (fun g => phiG (m + 2) g z) (fun i => (hz i).1.of_norm)
      (fun i => (hz i).2.of_norm)
  rw [hE]
  have hev : (fun s => ∑ i ∈ Finset.range (4 * n + 1),
      (∑' x : S3.Conj.EllPos M δ' ((i : ℤ) - 2 * n) n, phiGS (m + 2) s x z +
        ∑' x : S3.Conj.EllNeg M δ' ((i : ℤ) - 2 * n) n, phiGS (m + 2) s x z)) =ᶠ[𝓝[>] 0]
      fun s => ellPartS (m + 2) M n δ' s z := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (ellPartS_split hn δ' hz (Set.mem_Ioi.1 hs).le).symm
  refine Tendsto.congr' hev (tendsto_finsetSum _ fun i _ => Tendsto.add ?_ ?_)
  · exact tendsto_tsum_of_dominated_convergence
      (f := fun (s : ℝ) (x : S3.Conj.EllPos M δ' ((i : ℤ) - 2 * n) n) => phiGS (m + 2) s x z) (hz i).1
      (fun x => tendsto_phiGS _ (det_pos_of_ell (of_EllPos x.2).2.1) z)
      (eventually_nhdsWithin_of_forall fun s hs => fun x =>
        norm_phiGS_le _ (Set.mem_Ioi.1 hs).le (det_pos_of_ell (of_EllPos x.2).2.1) z)
  · exact tendsto_tsum_of_dominated_convergence
      (f := fun (s : ℝ) (x : S3.Conj.EllNeg M δ' ((i : ℤ) - 2 * n) n) => phiGS (m + 2) s x z) (hz i).2
      (fun x => tendsto_phiGS _ (det_pos_of_ell (of_EllNeg x.2).2.1) z)
      (eventually_nhdsWithin_of_forall fun s hs => fun x =>
        norm_phiGS_le _ (Set.mem_Ioi.1 hs).le (det_pos_of_ell (of_EllNeg x.2).2.1) z)

theorem tendsto_ellPartS_ae [NeZero M] (hM : 3 ≤ M) (m : ℕ) (δ' : ZMod M) {n : ℕ} (hn : 0 < n) :
    ∀ᵐ z ∂(volume.restrict (fdom (Gamma1 M))),
      Tendsto (fun s => ellPartS (m + 2) M n δ' s z) (𝓝[>] 0) (𝓝 (ellPart (m + 2) M n δ' z)) :=
  (ae_ellSum hM m δ' n).mono fun _ hz => tendsto_ellPartS hn δ' hz

theorem norm_ellPartS_le_ae [NeZero M] (hM : 3 ≤ M) (m : ℕ) (δ' : ZMod M) {n : ℕ} (hn : 0 < n) :
    ∀ᵐ z ∂(volume.restrict (fdom (Gamma1 M))),
      ∀ s : ℝ, 0 ≤ s → ‖ellPartS (m + 2) M n δ' s z‖ ≤ ellDom m M n δ' z :=
  (ae_ellSum hM m δ' n).mono fun _ hz _ hs => norm_ellPartS_le hn δ' hz hs

end RamanujanPetersson.EllW2


