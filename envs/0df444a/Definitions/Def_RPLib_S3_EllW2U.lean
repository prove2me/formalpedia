-- Prove2me | Definitions.Def_RPLib_S3_EllW2U
-- name    : RPLib_S3_EllW2U
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:31:06.698747+00:00
-- url     : https://prove2.me/theorems/31073e0e-dc09-4fa6-8dc6-9d6ddfe46222
-- title:
--   The Eichler-Selberg trace formula in weight two: unfolding over `T`-conjugation orbits (zero modes)
-- statement:
--   Unfolding over `T`-conjugation orbits (zero modes).
--
--   * `tconj k g = T^k g T^(-k)`, `tconj_entries`, `tconj_add`, `tconj_zero`, `tconj_equivariant` (from `k = 1`).
--   * `IsRep g`: `0 ≤ a < |c|`; `repEquiv : Reps × ℤ ≃ {c ≠ 0}`.
--   * **`unfold_T`**: `Σ'_g ∫_{-1/2}^{1/2} f g = Σ'_{r rep} ∫_ℝ f r` for `T`-equivariant `f` vanishing at `c = 0`.
--   * `RcN`, `Rc_eq_RcN`: `R` in the normal form `x' = x + (d - a)/(2c)`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2N2

/-!
# S3-ES-Wt2 (O6, file U): unfolding over `T`-conjugation orbits (zero modes)

* `tconj k g = T^k g T^(-k)`, `tconj_entries`, `tconj_add`, `tconj_zero`, `tconj_equivariant` (from `k = 1`).
* `IsRep g`: `0 ≤ a < |c|`; `repEquiv : Reps × ℤ ≃ {c ≠ 0}`.
* **`unfold_T`**: `Σ'_g ∫_{-1/2}^{1/2} f g = Σ'_{r rep} ∫_ℝ f r` for `T`-equivariant `f` vanishing at `c = 0`.
* `RcN`, `Rc_eq_RcN`: `R` in the normal form `x' = x + (d - a)/(2c)`.
-/

open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

/-- `T^k g T^(-k)`. -/
def tconj (k : ℤ) (g : S3.Conj.Mat) : S3.Conj.Mat := S3.Conj.conj (ModularGroup.T ^ k) g

lemma tconj_entries (k : ℤ) (g : S3.Conj.Mat) :
    tconj k g 0 0 = g 0 0 + k * g 1 0 ∧ tconj k g 0 1 = g 0 1 + k * (g 1 1 - g 0 0) - k ^ 2 * g 1 0 ∧
      tconj k g 1 0 = g 1 0 ∧ tconj k g 1 1 = g 1 1 - k * g 1 0 := by
  obtain ⟨e0, e1, e2, e3⟩ := conj_entries (ModularGroup.T ^ k) g
  have hT : ∀ i j, (ModularGroup.T ^ k) i j = (!![1, k; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j := by
    intro i j; rw [← ModularGroup.coe_T_zpow]
  unfold tconj
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e0]; simp only [hT]; norm_num <;> try ring
  · rw [e1]; simp only [hT]; norm_num <;> try ring
  · rw [e2]; simp only [hT]; norm_num <;> try ring
  · rw [e3]; simp only [hT]; norm_num <;> try ring

lemma tconj_add (j k : ℤ) (g : S3.Conj.Mat) : tconj j (tconj k g) = tconj (j + k) g := by
  unfold tconj; rw [zpow_add, S3.Conj.conj_mul]

lemma tconj_zero (g : S3.Conj.Mat) : tconj 0 g = g := by
  unfold tconj; rw [zpow_zero, S3.Conj.conj_one]

lemma tconj_one (g : S3.Conj.Mat) : tconj 1 g = S3.Conj.conj ModularGroup.T g := by
  unfold tconj; rw [zpow_one]

/-- `T`-equivariance for every `k` from `k = 1`. -/
lemma tconj_equivariant {E : Type*} (f : S3.Conj.Mat → ℝ → E)
    (hf : ∀ g x, f (tconj 1 g) (x + 1) = f g x) (k : ℤ) :
    ∀ g x, f (tconj k g) (x + k) = f g x := by
  have h3 : ∀ h y, f (tconj (-1) h) (y - 1) = f h y := by
    intro h y
    have := hf (tconj (-1) h) (y - 1)
    rw [tconj_add, show (1 : ℤ) + -1 = 0 by norm_num, tconj_zero, sub_add_cancel] at this
    exact this.symm
  refine Int.induction_on k (fun g x => by simp [tconj_zero]) (fun i ih g x => ?_) (fun i ih g x => ?_)
  · have h1 : tconj ((i : ℤ) + 1) g = tconj 1 (tconj (i : ℤ) g) := by rw [tconj_add, add_comm]
    have h2 : x + (((i : ℤ) + 1 : ℤ) : ℝ) = (x + ((i : ℤ) : ℝ)) + 1 := by push_cast; ring
    rw [h1, h2, hf, ih]
  · have h1 : tconj (-(i : ℤ) - 1) g = tconj (-1) (tconj (-(i : ℤ)) g) := by
      rw [tconj_add]; congr 1; ring
    have h2 : x + ((-(i : ℤ) - 1 : ℤ) : ℝ) = (x + ((-(i : ℤ) : ℤ) : ℝ)) - 1 := by push_cast; ring
    rw [h1, h2, h3, ih]

/-- Orbit representatives: `0 ≤ a < |c|`. -/
def IsRep (g : S3.Conj.Mat) : Prop := 0 ≤ g 0 0 ∧ g 0 0 < |g 1 0|

lemma IsRep.ne {g : S3.Conj.Mat} (h : IsRep g) : g 1 0 ≠ 0 := by
  intro h0; have := h.2; rw [h0, abs_zero] at this; linarith [h.1]

lemma isRep_tconj_neg (g : S3.Conj.Mat) (hc : g 1 0 ≠ 0) :
    IsRep (tconj (-(g 0 0 / g 1 0)) g) := by
  obtain ⟨e0, -, e2, -⟩ := tconj_entries (-(g 0 0 / g 1 0)) g
  have hm : g 0 0 + -(g 0 0 / g 1 0) * g 1 0 = g 0 0 % g 1 0 := by rw [Int.emod_def]; ring
  refine ⟨?_, ?_⟩
  · rw [e0, hm]; exact Int.emod_nonneg _ hc
  · rw [e0, e2, hm]; exact Int.emod_lt_abs _ hc

lemma quot_tconj {r : S3.Conj.Mat} (hr : IsRep r) (k : ℤ) : tconj k r 0 0 / tconj k r 1 0 = k := by
  obtain ⟨e0, -, e2, -⟩ := tconj_entries k r
  rw [e0, e2, Int.add_mul_ediv_right _ _ hr.ne, Int.ediv_eq_zero_of_lt_abs hr.1 hr.2, zero_add]

/-- `Reps × ℤ ≃ {c ≠ 0}`, `(r, k) ↦ T^k r T^(-k)`. -/
def repEquiv : {g : S3.Conj.Mat // IsRep g} × ℤ ≃ ↥{g : S3.Conj.Mat | g 1 0 ≠ 0} where
  toFun p := ⟨tconj p.2 p.1.1, by
    show tconj p.2 p.1.1 1 0 ≠ 0
    rw [(tconj_entries _ _).2.2.1]; exact p.1.2.ne⟩
  invFun g := (⟨tconj (-(g.1 0 0 / g.1 1 0)) g.1, isRep_tconj_neg g.1 g.2⟩, g.1 0 0 / g.1 1 0)
  left_inv p := by
    obtain ⟨⟨r, hr⟩, k⟩ := p
    simp only [quot_tconj hr k]
    refine Prod.ext (Subtype.ext ?_) rfl
    show tconj (-k) (tconj k r) = r
    rw [tconj_add, neg_add_cancel, tconj_zero]
  right_inv g := by
    obtain ⟨g, hg⟩ := g
    refine Subtype.ext ?_
    show tconj (g 0 0 / g 1 0) (tconj (-(g 0 0 / g 1 0)) g) = g
    rw [tconj_add, add_neg_cancel, tconj_zero]

/-- **Unfolding over `T`-orbits.** -/
theorem unfold_T {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : S3.Conj.Mat → ℝ → E) (hf : ∀ g x, f (tconj 1 g) (x + 1) = f g x)
    (h0 : ∀ g, g 1 0 = 0 → ∀ x, f g x = 0) (hint : ∀ g, Integrable (f g))
    (hsum : Summable fun g => ∫ x in (-(1 / 2 : ℝ))..(1 / 2), f g x) :
    ∑' g, ∫ x in (-(1 / 2 : ℝ))..(1 / 2), f g x = ∑' r : {g // IsRep g}, ∫ x, f r.1 x := by
  set F : S3.Conj.Mat → E := fun g => ∫ x in (-(1 / 2 : ℝ))..(1 / 2), f g x with hF
  have hsupp : Function.support F ⊆ {g : S3.Conj.Mat | g 1 0 ≠ 0} := by
    intro g hg
    by_contra hc
    apply hg
    have hc' : g 1 0 = 0 := by simpa using hc
    show (∫ x in (-(1 / 2 : ℝ))..(1 / 2), f g x) = 0
    simp [h0 g hc']
  rw [← tsum_subtype_eq_of_support_subset hsupp, ← repEquiv.tsum_eq]
  have hsP : Summable (fun p : {g // IsRep g} × ℤ => F (repEquiv p).1) :=
    repEquiv.summable_iff.2 (hsum.subtype _)
  rw [hsP.tsum_prod]
  congr 1
  funext r
  refine HasSum.tsum_eq ?_
  have hk : ∀ k : ℤ, F (tconj k r.1) =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2), f r.1 (x + ((-k : ℤ) : ℝ)) := by
    intro k
    show (∫ x in (-(1 / 2 : ℝ))..(1 / 2), f (tconj k r.1) x) = _
    congr 1; funext x
    have := tconj_equivariant f hf k r.1 (x + ((-k : ℤ) : ℝ))
    rw [← this]; congr 1; push_cast; ring
  have hH := (hint r.1).hasSum_intervalIntegral (-(1 / 2 : ℝ))
  have hfun : (fun n : ℤ => ∫ x in (-(1 / 2 : ℝ))..(1 / 2), f r.1 (x + (n : ℝ))) =
      fun n : ℤ => ∫ x in (-(1 / 2 : ℝ)) + n..(-(1 / 2 : ℝ)) + n + 1, f r.1 x := by
    funext n
    rw [intervalIntegral.integral_comp_add_right]
    ring_nf
  rw [← hfun] at hH
  have h2 := (Equiv.neg ℤ).hasSum_iff.2 hH
  convert h2 using 1
  funext k
  show F (tconj k r.1) = _
  rw [hk]
  rfl

/-! ## Normal form of `R` -/

/-- `R` in the coordinates `u = x + (d - a)/(2c)`, `D = t² - 4 det`. -/
def RcN (c t D u y : ℝ) : ℝ := ((c * (u ^ 2 + y ^ 2) - D / (4 * c)) / y) ^ 2 + t ^ 2

lemma Rc_eq_RcN (g : Matrix (Fin 2) (Fin 2) ℤ) (hc : g 1 0 ≠ 0) (x y : ℝ) :
    Rc g x y = RcN (g 1 0) (trR g) (trR g ^ 2 - 4 * g.det)
      (x + ((g 1 1 : ℝ) - g 0 0) / (2 * g 1 0)) y := by
  have hc' : (g 1 0 : ℝ) ≠ 0 := by exact_mod_cast hc
  unfold Rc RcN Pc trR
  rw [Matrix.det_fin_two]
  push_cast
  congr 2
  field_simp
  ring

/-- Translation invariance of the `x`-integral. -/
lemma integral_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (φ : ℝ → E) (a : ℝ) :
    ∫ x, φ (x + a) = ∫ x, φ x :=
  integral_add_right_eq_self φ a

end RamanujanPetersson.EllW2


