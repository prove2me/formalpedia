-- Prove2me | Definitions.Def_RPLib_S3_HypParEB
-- name    : RPLib_S3_HypParEB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T21:22:36.41204+00:00
-- url     : https://prove2.me/theorems/f999d249-42e1-4501-9894-949f947e57ff
-- title:
--   The Eichler-Selberg trace formula, hyperbolic part EB: the split hyperbolic top-edge sums
-- statement:
--   For $g = \begin{pmatrix} a & b \\ 0 & d \end{pmatrix}$ with $ad > 0$, $a \ne d$, the sum over $b \in \mathbb{Z}$ of the weighted top-edge integrals is independent of the truncation height and equals the sum over $0 \le r < |a - d|$ of the weights times an explicit constant.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976 (with the Correction in later printings)

import Mathlib
import Definitions.Def_RPLib_S3_HypParT
import Definitions.Def_RPLib_S3_HypParEA

/-!
# S3-HypParTerms, part EB (O6): the `c = 0` hyperbolic top-edge sums

For `g = ut a b d = [[a, b], [0, d]]` with `a d > 0`, `a ≠ d`, the sum over `b ∈ ℤ` of
`wt g · topI g m Y` is independent of `Y`:
`hasSum_hyp : HasSum (fun b => wt (ut a b d) * topI (ut a b d) m Y)
   ((∑ r ∈ Ico 0 |a - d|, wt (ut a r d)) * hypC a d m)`.
The `b`-translates of `[-1/2, 1/2]` tile `ℝ` (weights are `|a - d|`-periodic in `b` by `T`-conjugation),
and the real-line integral is `HypEA.integral_rat`.
-/

open Complex MeasureTheory Set Filter
open UpperHalfPlane hiding I
open scoped ComplexConjugate MatrixGroups Modular Topology Real

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.HypPar

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

/-- The upper triangular integer matrix `[[a, b], [0, d]]`. -/
def ut (a b d : ℤ) : S3.Conj.Mat := !![a, b; 0, d]

@[simp] lemma ut_00 (a b d : ℤ) : ut a b d 0 0 = a := by simp [ut]
@[simp] lemma ut_01 (a b d : ℤ) : ut a b d 0 1 = b := by simp [ut]
@[simp] lemma ut_10 (a b d : ℤ) : ut a b d 1 0 = 0 := by simp [ut]
@[simp] lemma ut_11 (a b d : ℤ) : ut a b d 1 1 = d := by simp [ut]

lemma det_ut (a b d : ℤ) : (ut a b d).det = a * d := by
  simp [ut, Matrix.det_fin_two]

lemma conj_T_ut (a b d : ℤ) :
    S3.Conj.conj ModularGroup.T (ut a b d) = ut a (b + -(a - d)) d := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [S3.Conj.conj, ut, ModularGroup.coe_T, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

variable {M : ℕ} [NeZero M]

lemma wt_ut_periodic (n : ℤ) (δ' : ZMod M) (a d : ℤ) :
    Function.Periodic (fun b : ℤ => wt M n δ' (ut a b d)) (-(a - d)) := by
  intro b
  show wt M n δ' (ut a (b + -(a - d)) d) = wt M n δ' (ut a b d)
  rw [← conj_T_ut, wt_conj]

lemma wt_ut_sub_mul (n : ℤ) (δ' : ZMod M) (a d r j : ℤ) :
    wt M n δ' (ut a (r - (a - d) * j) d) = wt M n δ' (ut a r d) := by
  have h : wt M n δ' (ut a (r + j * -(a - d)) d) = wt M n δ' (ut a r d) :=
    (wt_ut_periodic n δ' a d).int_mul j r
  rw [← h]
  congr 2
  ring

/-- The real-line integrand of the `c = 0` top edge. -/
def fR (a d : ℤ) (m : ℕ) (Y s : ℝ) : ℂ :=
  ((HypEA.u (((a : ℝ) + d) * Y) s) ^ m * HypEA.u (((a : ℝ) - d) * Y) s)⁻¹

lemma VG_ut (a b d : ℤ) (m : ℕ) (x Y : ℝ) :
    VG (ut a b d) m ((x : ℂ) + Y * I) =
      -((Y : ℂ) ^ m / m) * fR a d m Y (((a : ℝ) - d) * x + b) := by
  have hz : conj ((x : ℂ) + Y * I) = (x : ℂ) - Y * I := by
    rw [map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]; ring
  have hYf : Yf ((x : ℂ) + Y * I) ((x : ℂ) - Y * I) = Y := by
    unfold Yf
    rw [show (x : ℂ) + Y * I - (x - Y * I) = 2 * I * Y by ring]
    exact mul_div_cancel_left₀ _ (mul_ne_zero two_ne_zero I_ne_zero)
  have e1 : Cf (ut a b d) ((x : ℂ) + Y * I) ((x : ℂ) - Y * I) =
      HypEA.u (((a : ℝ) + d) * Y) (((a : ℝ) - d) * x + b) := by
    simp only [Cf, ut_00, ut_01, ut_10, ut_11, HypEA.u]; push_cast; ring
  have e2 : qf (ut a b d) ((x : ℂ) - Y * I) =
      -HypEA.u (((a : ℝ) - d) * Y) (((a : ℝ) - d) * x + b) := by
    simp only [qf, ut_00, ut_01, ut_10, ut_11, HypEA.u]; push_cast; ring
  unfold VG uf fR
  rw [hz, hYf, e1, e2, mul_neg, div_neg]
  ring

lemma topI_ut (a b d : ℤ) (m : ℕ) (Y : ℝ) :
    topI (ut a b d) m Y = -((Y : ℂ) ^ m / m) *
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2), fR a d m Y (((a : ℝ) - d) * x + b) := by
  unfold topI
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr (fun x _ => VG_ut a b d m x Y)

/-- Tiling: the translates `γ [-1/2, 1/2] + (r - γ j)` cover `ℝ` once. -/
lemma hasSum_tile {f : ℝ → ℂ} (hf : Integrable f) {γ : ℝ} (hγ : γ ≠ 0) (r : ℝ) :
    HasSum (fun j : ℤ => ∫ x in (-(1 / 2 : ℝ))..(1 / 2), f (γ * x + (r - γ * j)))
      (((|γ⁻¹| : ℝ) : ℂ) * ∫ s, f s) := by
  set F : ℝ → ℂ := fun x => f (γ * x + r) with hF
  have hFi : Integrable F := (hf.comp_add_right r).comp_mul_left' hγ
  have h1 := hFi.hasSum_intervalIntegral (-(1 / 2))
  have h2 : HasSum (fun j : ℤ => ∫ x in (-(1 / 2 : ℝ)) + ((-j : ℤ) : ℝ)..(-(1 / 2 : ℝ)) + ((-j : ℤ) : ℝ) + 1,
      F x) (∫ x, F x) := (Equiv.neg ℤ).hasSum_iff.mpr h1
  have hint : ∫ x, F x = ((|γ⁻¹| : ℝ) : ℂ) * ∫ s, f s := by
    have := Measure.integral_comp_mul_left (fun t => f (t + r)) γ
    rw [hF]
    exact this.trans (by rw [integral_add_right_eq_self, Complex.real_smul])
  rw [hint] at h2
  convert h2 using 1
  funext j
  have h3 := intervalIntegral.integral_comp_add_right F ((-j : ℤ) : ℝ)
    (a := -(1 / 2 : ℝ)) (b := 1 / 2)
  rw [show (-(1 / 2 : ℝ)) + ((-j : ℤ) : ℝ) + 1 = 1 / 2 + ((-j : ℤ) : ℝ) by ring, ← h3]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [hF]
  congr 1
  push_cast
  ring

lemma sign_mul_pos {x Y : ℝ} (hY : 0 < Y) : Real.sign (x * Y) = Real.sign x := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [Real.sign_of_neg h, Real.sign_of_neg (mul_neg_of_neg_of_pos h hY)]
  · rw [h, zero_mul]
  · rw [Real.sign_of_pos h, Real.sign_of_pos (mul_pos h hY)]

/-- The `Y`-independent value of one residue class of the `c = 0` hyperbolic top edge. -/
def hypC (a d : ℤ) (m : ℕ) : ℂ :=
  -(1 / (m : ℂ)) * ((|((a : ℝ) - d)⁻¹| : ℝ) : ℂ) * (((((-2 * d : ℤ)) : ℂ) * I) ^ m)⁻¹ *
    (((π * (Real.sign ((a : ℝ) - d) - Real.sign ((a : ℝ) + d)) : ℝ) : ℂ) * I)

lemma ad_facts {a d : ℤ} (had : 0 < a * d) :
    (a : ℝ) + d ≠ 0 ∧ (d : ℝ) ≠ 0 := by
  have h1 : a + d ≠ 0 := by
    intro h
    have : d = -a := by omega
    subst this
    nlinarith [sq_nonneg a]
  have h2 : d ≠ 0 := by rintro rfl; simp at had
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- The real-line integral of `fR`, `Y`-independent after the prefactor. -/
lemma integral_fR {a d : ℤ} (had : 0 < a * d) (hγ : a ≠ d) {m : ℕ} (hm : 1 ≤ m) {Y : ℝ}
    (hY : 0 < Y) :
    Integrable (fR a d m Y) ∧
    -((Y : ℂ) ^ m / m) * (((|((a : ℝ) - d)⁻¹| : ℝ) : ℂ) * ∫ s, fR a d m Y s) = hypC a d m := by
  obtain ⟨h1, h2⟩ := ad_facts had
  have hγR : (a : ℝ) - d ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hγ)
  have hA : ((a : ℝ) + d) * Y ≠ 0 := mul_ne_zero h1 hY.ne'
  have hB : ((a : ℝ) - d) * Y ≠ 0 := mul_ne_zero hγR hY.ne'
  have hAB : ((a : ℝ) + d) * Y ≠ ((a : ℝ) - d) * Y := by
    intro h
    have : (2 * d : ℝ) * Y = 0 := by linarith
    exact (mul_ne_zero (mul_ne_zero two_ne_zero h2) hY.ne') this
  obtain ⟨hi, he⟩ := HypEA.integral_rat hA hB hAB hm
  refine ⟨hi, ?_⟩
  have hfun : fR a d m Y = fun s => ((HypEA.u (((a : ℝ) + d) * Y) s) ^ m *
      HypEA.u (((a : ℝ) - d) * Y) s)⁻¹ := rfl
  rw [hfun, he, sign_mul_pos hY, sign_mul_pos hY]
  have hBA : (((((a : ℝ) - d) * Y - ((a : ℝ) + d) * Y : ℝ)) : ℂ) * I =
      (Y : ℂ) * ((((-2 * d : ℤ)) : ℂ) * I) := by push_cast; ring
  rw [hBA, mul_pow, mul_inv]
  have hYm : (Y : ℂ) ^ m ≠ 0 := pow_ne_zero _ (ofReal_ne_zero.2 hY.ne')
  unfold hypC
  field_simp

/-- **O6**: the `c = 0` hyperbolic top-edge sum over `b`, for fixed `(a, d)` with `a d > 0`,
`a ≠ d`, is `Y`-independent. -/
theorem hasSum_hyp (n : ℤ) (δ' : ZMod M) {a d : ℤ} (had : 0 < a * d) (hγ : a ≠ d) {m : ℕ}
    (hm : 1 ≤ m) {Y : ℝ} (hY : 0 < Y) :
    HasSum (fun b : ℤ => wt M n δ' (ut a b d) * topI (ut a b d) m Y)
      ((∑ r ∈ Finset.Ico 0 |a - d|, wt M n δ' (ut a r d)) * hypC a d m) := by
  obtain ⟨hfi, hval⟩ := integral_fR had hγ hm hY
  set γ : ℤ := a - d with hγdef
  have hγ0 : γ ≠ 0 := sub_ne_zero.2 hγ
  have hγR : (a : ℝ) - d ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hγ)
  have hN : 0 < |γ| := abs_pos.2 hγ0
  set W : ℤ → ℂ := fun b => wt M n δ' (ut a b d) with hW
  set T : ℤ → ℂ := fun b => topI (ut a b d) m Y with hT
  have hres : ∀ r ∈ Finset.Ico 0 |γ|,
      HasSum (fun b : ℤ => if b % |γ| = r then W b * T b else 0) (W r * hypC a d m) := by
    intro r hr
    obtain ⟨hr0, hrN⟩ := Finset.mem_Ico.1 hr
    have hrr : r % |γ| = r := Int.emod_eq_of_lt hr0 hrN
    have hinj : Function.Injective (fun j : ℤ => r - γ * j) := by
      intro j1 j2 h
      simp only at h
      exact mul_left_cancel₀ hγ0 (by linarith)
    rw [← (hinj.hasSum_iff (fun b hb => ?_))]
    · have hc : ∀ j : ℤ, (r - γ * j) % |γ| = r := by
        intro j
        have : (r - γ * j) ≡ r [ZMOD |γ|] := by
          rw [Int.modEq_iff_dvd]
          have : |γ| ∣ γ * j := ((abs_dvd γ γ).2 dvd_rfl).mul_right j
          simpa using this
        rw [this, hrr]
      have hfun : ((fun b : ℤ => if b % |γ| = r then W b * T b else 0) ∘ fun j : ℤ => r - γ * j) =
          fun j : ℤ => W r * (-((Y : ℂ) ^ m / m) *
            ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
              fR a d m Y (((a : ℝ) - d) * x + ((r : ℝ) - ((a : ℝ) - d) * j))) := by
        funext j
        simp only [Function.comp_apply, hc j, if_true, hW, hT]
        rw [wt_ut_sub_mul, topI_ut]
        congr 4
        funext x
        congr 1
        simp only [hγdef]
        push_cast
        ring
      rw [hfun, ← hval]
      exact ((hasSum_tile hfi hγR (r : ℝ)).mul_left _).mul_left _
    · split_ifs with h
      · exfalso
        apply hb
        have hm' : r ≡ b [ZMOD |γ|] := by
          unfold Int.ModEq; rw [hrr, h]
        obtain ⟨k, hk⟩ := (abs_dvd γ (b - r)).1 (Int.modEq_iff_dvd.1 hm')
        exact ⟨-k, by simp only; linarith⟩
      · rfl
  have hsum := hasSum_sum hres
  rw [Finset.sum_mul]
  convert hsum using 1
  funext b
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_Ico.2 ⟨Int.emod_nonneg b hN.ne', Int.emod_lt_of_pos b hN⟩)]

end RamanujanPetersson.HypPar


