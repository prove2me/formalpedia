-- Prove2me | Definitions.Def_RPLib_S3_EllW2U2
-- name    : RPLib_S3_EllW2U2
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:32:24.109612+00:00
-- url     : https://prove2.me/theorems/7a2bac5a-6875-44b1-acc2-e6aabb397c12
-- title:
--   The Eichler-Selberg trace formula in weight two: grouping the orbit representatives by `(c, t)`
-- statement:
--   Grouping the orbit representatives by `(c, t)`.
--
--   * `mkT n (c, t) a = !![a, (a(t-a)-n)/c; c, t-a]`, injective in `((c,t),a)`; every representative of determinant `n` is one.
--   * `fib n c t = {a ∈ [0, |c|) : c ∣ a(t-a) - n}` (finite fibres).
--   * **`tsum_reps_ct`**: `Σ'_{r rep} F r = Σ'_{(c,t)} Σ_{a ∈ fib} F (mkT n (c,t) a)` for `F` supported on `det = n`.
--   * **`zero_mode_ct`**: `Σ'_g ∫_{-1/2}^{1/2} w g · V c t (x + (d-a)/(2c)) dx = Σ'_{(c,t)} W_c(t) · ∫_ℝ V c t`,
--     `W_c(t) = Σ_{a ∈ fib} w (mkT n (c,t) a)`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2U

/-!
# S3-ES-Wt2 (O6, file U2): grouping the orbit representatives by `(c, t)`

* `mkT n (c, t) a = !![a, (a(t-a)-n)/c; c, t-a]`, injective in `((c,t),a)`; every representative of determinant `n` is one.
* `fib n c t = {a ∈ [0, |c|) : c ∣ a(t-a) - n}` (finite fibres).
* **`tsum_reps_ct`**: `Σ'_{r rep} F r = Σ'_{(c,t)} Σ_{a ∈ fib} F (mkT n (c,t) a)` for `F` supported on `det = n`.
* **`zero_mode_ct`**: `Σ'_g ∫_{-1/2}^{1/2} w g · V c t (x + (d-a)/(2c)) dx = Σ'_{(c,t)} W_c(t) · ∫_ℝ V c t`,
  `W_c(t) = Σ_{a ∈ fib} w (mkT n (c,t) a)`.
-/

open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

/-- The matrix with `c = ct.1`, trace `t = ct.2`, upper-left entry `a` and determinant `n` (when `c ∣ a(t-a) - n`). -/
def mkT (n : ℤ) (ct : ℤ × ℤ) (a : ℤ) : S3.Conj.Mat :=
  !![a, (a * (ct.2 - a) - n) / ct.1; ct.1, ct.2 - a]

lemma mkT_entries (n : ℤ) (ct : ℤ × ℤ) (a : ℤ) :
    mkT n ct a 0 0 = a ∧ mkT n ct a 0 1 = (a * (ct.2 - a) - n) / ct.1 ∧
      mkT n ct a 1 0 = ct.1 ∧ mkT n ct a 1 1 = ct.2 - a := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [mkT]

/-- `mkT` as a map on `(ℤ × ℤ) × ℤ`. -/
def mkTq (n : ℤ) (q : (ℤ × ℤ) × ℤ) : S3.Conj.Mat := mkT n q.1 q.2

lemma mkTq_injective (n : ℤ) : Function.Injective (mkTq n) := by
  rintro ⟨⟨c, t⟩, a⟩ ⟨⟨c', t'⟩, a'⟩ h
  obtain ⟨p0, -, p2, p3⟩ := mkT_entries n (c, t) a
  obtain ⟨q0, -, q2, q3⟩ := mkT_entries n (c', t') a'
  have h' : mkT n (c, t) a = mkT n (c', t') a' := h
  simp only at p2 p3 q2 q3
  have e0 : a = a' := by rw [← p0, ← q0, h']
  have e2 : c = c' := by rw [← p2, ← q2, h']
  have e3 : t - a = t' - a' := by rw [← p3, ← q3, h']
  subst e0; subst e2
  have : t = t' := by linarith
  subst this; rfl

lemma eq_mkT {n : ℤ} {g : S3.Conj.Mat} (hr : IsRep g) (hd : g.det = n) :
    g = mkT n (g 1 0, g 0 0 + g 1 1) (g 0 0) := by
  have hc := hr.ne
  rw [Matrix.det_fin_two] at hd
  have hb : (g 0 0 * (g 0 0 + g 1 1 - g 0 0) - n) / g 1 0 = g 0 1 := by
    rw [show g 0 0 * (g 0 0 + g 1 1 - g 0 0) - n = g 0 1 * g 1 0 by rw [← hd]; ring]
    exact Int.mul_ediv_cancel _ hc
  obtain ⟨e0, e1, e2, e3⟩ := mkT_entries n (g 1 0, g 0 0 + g 1 1) (g 0 0)
  ext i j
  fin_cases i <;> fin_cases j
  · exact e0.symm
  · exact (e1.trans hb).symm
  · exact e2.symm
  · simp only [Fin.mk_one, Fin.isValue] at e3 ⊢; rw [e3]; ring

lemma det_mkT_iff (n c t a : ℤ) : (mkT n (c, t) a).det = n ↔ c ∣ a * (t - a) - n := by
  rw [Matrix.det_fin_two]
  obtain ⟨e0, e1, e2, e3⟩ := mkT_entries n (c, t) a
  rw [e0, e1, e2, e3]
  constructor
  · intro h
    exact ⟨(a * (t - a) - n) / c, by linarith⟩
  · intro h
    rw [Int.ediv_mul_cancel h]; ring

lemma isRep_mkT_iff (n c t a : ℤ) : IsRep (mkT n (c, t) a) ↔ 0 ≤ a ∧ a < |c| := by
  obtain ⟨e0, -, e2, -⟩ := mkT_entries n (c, t) a
  unfold IsRep; rw [e0, e2]

/-- The fibre over `(c, t)`: `a ∈ [0, |c|)` with `c ∣ a(t-a) - n`. -/
def fib (n c t : ℤ) : Finset ℤ := (Finset.Ico 0 |c|).filter fun a => c ∣ a * (t - a) - n

/-- **Grouping the representatives by `(c, t)`.** -/
theorem tsum_reps_ct {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (n : ℤ) (F : S3.Conj.Mat → E) (hF : ∀ g, g.det ≠ n → F g = 0)
    (hs : Summable fun r : {g // IsRep g} => F r.1) :
    ∑' r : {g // IsRep g}, F r.1 = ∑' ct : ℤ × ℤ, ∑ a ∈ fib n ct.1 ct.2, F (mkT n ct a) := by
  classical
  set H : S3.Conj.Mat → E := {g | IsRep g}.indicator F with hH
  have h1 : ∑' r : {g // IsRep g}, F r.1 = ∑' g, H g := tsum_subtype {g | IsRep g} F
  have hsH : Summable H := summable_subtype_iff_indicator.1 hs
  have hsupp : Function.support H ⊆ Set.range (mkTq n) := by
    intro g hg
    have hr : IsRep g := by
      by_contra h
      exact hg (Set.indicator_of_notMem (show g ∉ {g | IsRep g} from h) F)
    have hd : g.det = n := by
      by_contra h
      apply hg
      show H g = 0
      rw [hH, Set.indicator_of_mem (show g ∈ {g | IsRep g} from hr)]
      exact hF g h
    exact ⟨((g 1 0, g 0 0 + g 1 1), g 0 0), (eq_mkT hr hd).symm⟩
  rw [h1, ← (mkTq_injective n).tsum_eq hsupp]
  have hsC : Summable (H ∘ mkTq n) := hsH.comp_injective (mkTq_injective n)
  rw [show (∑' q, H (mkTq n q)) = ∑' q, (H ∘ mkTq n) q from rfl, hsC.tsum_prod]
  refine tsum_congr fun ct => ?_
  show (∑' a, H (mkT n ct a)) = _
  obtain ⟨c, t⟩ := ct
  rw [tsum_eq_sum (s := Finset.Ico 0 |c|)]
  · unfold fib
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hr : IsRep (mkT n (c, t) a) := by
      rw [isRep_mkT_iff]; exact Finset.mem_Ico.1 ha
    rw [hH, Set.indicator_of_mem (show mkT n (c, t) a ∈ {g | IsRep g} from hr)]
    split_ifs with hdv
    · rfl
    · exact hF _ (fun h => hdv ((det_mkT_iff n c t a).1 h))
  · intro a ha
    have hr : ¬IsRep (mkT n (c, t) a) := by
      rw [isRep_mkT_iff]; exact fun h => ha (Finset.mem_Ico.2 h)
    rw [hH]
    exact Set.indicator_of_notMem (show mkT n (c, t) a ∉ {g | IsRep g} from hr) F

/-! ## Zero modes in `(c, t)` form -/

/-- `w g · V c t (x + (d - a)/(2c))`. -/
def zmF (w : S3.Conj.Mat → ℂ) (V : ℤ → ℤ → ℝ → ℂ) (g : S3.Conj.Mat) (x : ℝ) : ℂ :=
  w g * V (g 1 0) (g 0 0 + g 1 1) (x + ((g 1 1 : ℝ) - g 0 0) / (2 * g 1 0))

lemma zmF_tconj (w : S3.Conj.Mat → ℂ) (V : ℤ → ℤ → ℝ → ℂ) (hw : ∀ g, w (tconj 1 g) = w g)
    (hw0 : ∀ g, g 1 0 = 0 → w g = 0) (g : S3.Conj.Mat) (x : ℝ) :
    zmF w V (tconj 1 g) (x + 1) = zmF w V g x := by
  by_cases hc : g 1 0 = 0
  · have h1 : w (tconj 1 g) = 0 := by rw [hw]; exact hw0 g hc
    unfold zmF; rw [h1, hw0 g hc, zero_mul, zero_mul]
  · obtain ⟨e0, -, e2, e3⟩ := tconj_entries 1 g
    unfold zmF
    rw [hw, e0, e2, e3]
    have hc' : (g 1 0 : ℝ) ≠ 0 := by exact_mod_cast hc
    congr 2
    · ring
    · push_cast
      field_simp
      ring

/-- **Zero modes grouped by `(c, t)`.** -/
theorem zero_mode_ct (n : ℤ) (w : S3.Conj.Mat → ℂ) (V : ℤ → ℤ → ℝ → ℂ)
    (hw : ∀ g, w (tconj 1 g) = w g) (hw0 : ∀ g, g 1 0 = 0 → w g = 0)
    (hwd : ∀ g, g.det ≠ n → w g = 0) (hV : ∀ c t, Integrable (V c t))
    (hsum : Summable fun g => ∫ x in (-(1 / 2 : ℝ))..(1 / 2), zmF w V g x)
    (hsumR : Summable fun r : {g // IsRep g} =>
      w r.1 * ∫ u, V (r.1 1 0) (r.1 0 0 + r.1 1 1) u) :
    ∑' g, ∫ x in (-(1 / 2 : ℝ))..(1 / 2), zmF w V g x =
      ∑' ct : ℤ × ℤ, (∑ a ∈ fib n ct.1 ct.2, w (mkT n ct a)) * ∫ u, V ct.1 ct.2 u := by
  have hint : ∀ g, Integrable (zmF w V g) := fun g =>
    ((hV _ _).comp_add_right _).const_mul (w g)
  have h0 : ∀ g, g 1 0 = 0 → ∀ x, zmF w V g x = 0 := by
    intro g hg x; unfold zmF; rw [hw0 g hg, zero_mul]
  rw [unfold_T (zmF w V) (zmF_tconj w V hw hw0) h0 hint hsum]
  have hr : ∀ r : {g // IsRep g}, ∫ x, zmF w V r.1 x =
      w r.1 * ∫ u, V (r.1 1 0) (r.1 0 0 + r.1 1 1) u := by
    intro r
    unfold zmF
    rw [integral_const_mul, integral_add_right_eq_self]
  rw [tsum_congr hr]
  rw [tsum_reps_ct n (fun g => w g * ∫ u, V (g 1 0) (g 0 0 + g 1 1) u)
    (fun g hg => by show w g * _ = 0; rw [hwd g hg, zero_mul]) hsumR]
  refine tsum_congr fun ct => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  obtain ⟨e0, -, e2, e3⟩ := mkT_entries n ct a
  rw [e0, e2, e3, add_sub_cancel]

end RamanujanPetersson.EllW2


