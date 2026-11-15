-- Prove2me | Definitions.Def_RPLib_S3_DWSIsogE
-- name    : RPLib_S3_DWSIsogE
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:31:52.826191+00:00
-- url     : https://prove2.me/theorems/45439e73-d8b0-487f-8d7d-9ec43a2b8364
-- title:
--   Weight-two Ramanujan-Petersson library: ultrametric `ord`, values, exact pole orders of `x`, `y` at `O`
-- statement:
--   Ultrametric `ord`, values, exact pole orders of `x`, `y` at `O`.
--
--   * `ord_add_ge`, `ord_add_eq_of_lt'` (ultrametric inequality / strict domination, zero-tolerant).
--   * `exists_value` : `ord_P h ≥ 0 ⇒ ∃ c, h = c ∨ ord_P (h - c) ≥ 1` at ANY point `P` (also `O`).
--   * `ord_gx_sub_affine` : the affine divisor of `x - x(P)` is `[P] + [-P]`; **`ord_gx_zero`** : `ord_O x = -2`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSIsogD

/-!
# S3-DWS-Isog, part E: ultrametric `ord`, values, exact pole orders of `x`, `y` at `O`

* `ord_add_ge`, `ord_add_eq_of_lt'` (ultrametric inequality / strict domination, zero-tolerant).
* `exists_value` : `ord_P h ≥ 0 ⇒ ∃ c, h = c ∨ ord_P (h - c) ≥ 1` at ANY point `P` (also `O`).
* `ord_gx_sub_affine` : the affine divisor of `x - x(P)` is `[P] + [-P]`; **`ord_gx_zero`** : `ord_O x = -2`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open IsDedekindDomain
open scoped nonZeroDivisors

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section OrdE

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

lemma log_le_of_le' {a b : WithZero (Multiplicative ℤ)} (ha : a ≠ 0) (hb : b ≠ 0) (h : a ≤ b) :
    WithZero.log a ≤ WithZero.log b := by
  rw [← WithZero.exp_le_exp, WithZero.exp_log ha, WithZero.exp_log hb]; exact h

lemma lt_of_log_lt' {a b : WithZero (Multiplicative ℤ)} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : WithZero.log a < WithZero.log b) : a < b := by
  rw [← WithZero.exp_log ha, ← WithZero.exp_log hb, WithZero.exp_lt_exp]; exact h

lemma nu_tau_ne_zero (S : Pt W L) {f : FF W L} (hf : f ≠ 0) :
    nu W L (base W L) (base_ne W L) (tau W L S f) ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr (tau_ne_zero _ hf)

/-- Ultrametric inequality for `ord`. -/
lemma ord_add_ge {f g : FF W L} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) (P : Pt W L) :
    min (ord W L f P) (ord W L g P) ≤ ord W L (f + g) P := by
  have hle := Valuation.map_add (nu W L (base W L) (base_ne W L))
    (tau W L (P - base W L) f) (tau W L (P - base W L) g)
  rw [← map_add] at hle
  simp only [ord]
  rcases le_total (nu W L (base W L) (base_ne W L) (tau W L (P - base W L) f))
    (nu W L (base W L) (base_ne W L) (tau W L (P - base W L) g)) with hab | hab
  · rw [max_eq_right hab] at hle
    have := log_le_of_le' (nu_tau_ne_zero _ hfg) (nu_tau_ne_zero _ hg) hle
    exact le_trans (min_le_right _ _) (neg_le_neg this)
  · rw [max_eq_left hab] at hle
    have := log_le_of_le' (nu_tau_ne_zero _ hfg) (nu_tau_ne_zero _ hf) hle
    exact le_trans (min_le_left _ _) (neg_le_neg this)

/-- Strict domination: if `g = 0` or `ord_P f < ord_P g`, then `f + g ≠ 0` and `ord_P (f + g) = ord_P f`. -/
lemma ord_add_eq_of_lt' {f g : FF W L} (hf : f ≠ 0) (P : Pt W L)
    (h : g = 0 ∨ ord W L f P < ord W L g P) :
    f + g ≠ 0 ∧ ord W L (f + g) P = ord W L f P := by
  by_cases hg : g = 0
  · subst hg; rw [add_zero]; exact ⟨hf, rfl⟩
  replace h : ord W L f P < ord W L g P := h.resolve_left hg
  simp only [ord] at h
  have hlt : nu W L (base W L) (base_ne W L) (tau W L (P - base W L) g) <
      nu W L (base W L) (base_ne W L) (tau W L (P - base W L) f) :=
    lt_of_log_lt' (nu_tau_ne_zero _ hg) (nu_tau_ne_zero _ hf) (by linarith)
  have heq : nu W L (base W L) (base_ne W L) (tau W L (P - base W L) (f + g)) =
      nu W L (base W L) (base_ne W L) (tau W L (P - base W L) f) := by
    rw [map_add]; exact Valuation.map_add_eq_of_lt_left _ hlt
  refine ⟨fun h0 => ?_, by simp only [ord]; rw [heq]⟩
  rw [h0, map_zero, Valuation.map_zero] at heq
  exact nu_tau_ne_zero _ hf heq.symm

/-- The value of a function regular at any point `P` (also `P = O`). -/
lemma exists_value {h : FF W L} (hh : h ≠ 0) {P : Pt W L} (h0 : 0 ≤ ord W L h P) :
    ∃ c : L, h - algebraMap L (FF W L) c = 0 ∨ 1 ≤ ord W L (h - algebraMap L (FF W L) c) P := by
  set Q := base W L
  have hQ : Q ≠ 0 := base_ne W L
  set T := P - Q
  have hT : ∀ f, ord W L (tau W L T f) Q = ord W L f P := fun f => by
    rw [ord_tau]; congr 1; simp only [T]; abel
  have h1 : 0 ≤ ord W L (tau W L T h) Q := by rw [hT]; exact h0
  rw [ord_eq hQ] at h1
  have hnu : nu W L Q hQ (tau W L T h) ≤ 1 := by
    have hne : nu W L Q hQ (tau W L T h) ≠ 0 := (Valuation.ne_zero_iff _).mpr (tau_ne_zero _ hh)
    rw [← WithZero.exp_log hne, ← WithZero.exp_zero, WithZero.exp_le_exp]; linarith
  obtain ⟨c, hc⟩ := exists_HV hQ hnu
  refine ⟨c, ?_⟩
  by_cases hz : h - algebraMap L (FF W L) c = 0
  · exact Or.inl hz
  right
  rw [← hT, map_sub, AlgEquiv.commutes, ord_eq hQ]
  have hne : nu W L Q hQ (tau W L T h - algebraMap L (FF W L) c) ≠ 0 := by
    rw [← AlgEquiv.commutes (tau W L T) c, ← map_sub]
    exact (Valuation.ne_zero_iff _).mpr (tau_ne_zero _ hz)
  have hlt : nu W L Q hQ (tau W L T h - algebraMap L (FF W L) c) < 1 := hc
  rw [← WithZero.exp_log hne, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  linarith

/-- `(x - x₀) = m_P · m_{-P}` as fractional ideals, for `P = (x₀, y₀)`. -/
lemma span_gx_sub {x y : L} (h : (W.baseChange L).toAffine.Nonsingular x y) :
    FractionalIdeal.spanSingleton (CR W L)⁰ (gx W L - algebraMap L (FF W L) x) =
      ((unitP (-(Point.some x y h : Pt W L)) * unitP (Point.some x y h : Pt W L) :
        (FractionalIdeal (CR W L)⁰ (FF W L))ˣ) : FractionalIdeal (CR W L)⁰ (FF W L)) := by
  have h0 : (Point.some x y h : Pt W L) ≠ 0 := Point.some_ne_zero h
  rw [Units.val_mul, unitP_coe (neg_ne_zero.mpr h0), unitP_coe h0]
  show _ = ((XYIdeal (W.baseChange L).toAffine x (C ((W.baseChange L).toAffine.negY x y)) :
      Ideal (CR W L)) : FractionalIdeal (CR W L)⁰ (FF W L)) *
    ((XYIdeal (W.baseChange L).toAffine x (C y) : Ideal (CR W L)) : FractionalIdeal (CR W L)⁰ (FF W L))
  rw [← FractionalIdeal.coeIdeal_mul, XYIdeal_neg_mul h, XIdeal,
    FractionalIdeal.coeIdeal_span_singleton, XClass, map_sub, map_sub, map_sub, gx, alg_mk_CC]

lemma ord_gx_sub_affine {x y : L} (h : (W.baseChange L).toAffine.Nonsingular x y) {Q : Pt W L}
    (hQ : Q ≠ 0) :
    ord W L (gx W L - algebraMap L (FF W L) x) Q =
      (if Q = -(Point.some x y h : Pt W L) then 1 else 0) + (if Q = (Point.some x y h : Pt W L) then 1 else 0) := by
  have hne : gx W L - algebraMap L (FF W L) x ≠ 0 := sub_ne_zero.mpr (gx_ne W L x)
  rw [← count_hosP hQ hne, span_gx_sub h, Units.val_mul,
    FractionalIdeal.count_mul _ _ (Units.ne_zero _) (Units.ne_zero _)]
  congr 1
  · split_ifs with hq
    · subst hq; exact count_unitP_self hQ
    · exact count_unitP_ne hQ (Ne.symm hq)
  · split_ifs with hq
    · subst hq; exact count_unitP_self hQ
    · exact count_unitP_ne hQ (Ne.symm hq)

/-- **`ord_O x = -2`.** -/
theorem ord_gx_zero : ord W L (gx W L) 0 = -2 := by
  obtain ⟨y, hy⟩ := exists_y_alg (W.baseChange L) (0 : L)
  have h : (W.baseChange L).toAffine.Nonsingular 0 y := equation_iff_nonsingular.mp hy
  set S : Pt W L := Point.some 0 y h
  have hS : S ≠ 0 := Point.some_ne_zero h
  have hnS : -S ≠ 0 := neg_ne_zero.mpr hS
  have hf : gx W L - algebraMap L (FF W L) 0 = gx W L := by rw [map_zero, sub_zero]
  have hne : gx W L ≠ 0 := by rw [← hf]; exact sub_ne_zero.mpr (gx_ne W L 0)
  have hZ : ∀ Q, ord W L (gx W L) Q ≠ 0 → Q ∈ ({0, S, -S} : Finset (Pt W L)) := by
    intro Q hQ
    by_cases hQ0 : Q = 0
    · simp [hQ0]
    rw [← hf, ord_gx_sub_affine h hQ0] at hQ
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases h1 : Q = S
    · exact Or.inr (Or.inl h1)
    by_cases h2 : Q = -S
    · exact Or.inr (Or.inr h2)
    exfalso; apply hQ; rw [if_neg h2, if_neg h1]; rfl
  have hsum := sum_ord_eq_zero hne _ hZ
  have hS' : ord W L (gx W L) S = (if S = -S then 1 else 0) + 1 := by
    rw [← hf, ord_gx_sub_affine h hS, if_pos rfl]
  have hnS' : ord W L (gx W L) (-S) = 1 + (if -S = S then 1 else 0) := by
    rw [← hf, ord_gx_sub_affine h hnS, if_pos rfl]
  by_cases hSS : S = -S
  · have e : ({0, S, -S} : Finset (Pt W L)) = {0, S} := by rw [← hSS]; simp
    rw [e, Finset.sum_pair (Ne.symm hS), hS', if_pos hSS] at hsum
    linarith
  · rw [Finset.sum_insert (by simp [Ne.symm hS, Ne.symm hnS]),
      Finset.sum_pair hSS, hS', hnS', if_neg hSS, if_neg (Ne.symm hSS)] at hsum
    linarith

/-! ### Lower bounds `Ge n g P := g = 0 ∨ n ≤ ord_P g` -/

lemma ord_neg' (g : FF W L) (P : Pt W L) : ord W L (-g) P = ord W L g P := by
  simp only [ord, map_neg, Valuation.map_neg]

/-- `g = 0` or `n ≤ ord_P g`. -/
def Ge (n : ℤ) (g : FF W L) (P : Pt W L) : Prop := g = 0 ∨ n ≤ ord W L g P

lemma Ge.mono {n m : ℤ} {g : FF W L} {P : Pt W L} (h : Ge n g P) (hm : m ≤ n) : Ge m g P :=
  h.imp id (fun h => le_trans hm h)

lemma Ge.zero (n : ℤ) (P : Pt W L) : Ge n (0 : FF W L) P := Or.inl rfl

lemma Ge.add {n : ℤ} {f g : FF W L} {P : Pt W L} (hf : Ge n f P) (hg : Ge n g P) :
    Ge n (f + g) P := by
  by_cases hf0 : f = 0
  · rw [hf0, zero_add]; exact hg
  by_cases hg0 : g = 0
  · rw [hg0, add_zero]; exact hf
  by_cases hfg : f + g = 0
  · exact Or.inl hfg
  exact Or.inr (le_trans (le_min (hf.resolve_left hf0) (hg.resolve_left hg0)) (ord_add_ge hf0 hg0 hfg P))

lemma Ge.neg {n : ℤ} {g : FF W L} {P : Pt W L} (h : Ge n g P) : Ge n (-g) P := by
  rcases h with h | h
  · left; rw [h, neg_zero]
  · right; rwa [ord_neg']

lemma Ge.sub {n : ℤ} {f g : FF W L} {P : Pt W L} (hf : Ge n f P) (hg : Ge n g P) :
    Ge n (f - g) P := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

lemma Ge.mul {n m : ℤ} {f g : FF W L} {P : Pt W L} (hf : Ge n f P) (hg : Ge m g P) :
    Ge (n + m) (f * g) P := by
  by_cases hf0 : f = 0
  · left; rw [hf0, zero_mul]
  by_cases hg0 : g = 0
  · left; rw [hg0, mul_zero]
  right; rw [ord_mul hf0 hg0 P]
  have := hf.resolve_left hf0; have := hg.resolve_left hg0; omega

lemma Ge.pow {n : ℤ} {f : FF W L} {P : Pt W L} (hf : Ge n f P) (k : ℕ) : Ge (k * n) (f ^ k) P := by
  induction k with
  | zero => right; rw [pow_zero, ord_one]; simp
  | succ k ih => rw [pow_succ]; exact (ih.mul hf).mono (le_of_eq (by push_cast; ring))

lemma Ge.const (c : L) (P : Pt W L) : Ge 0 (algebraMap L (FF W L) c) P := by
  by_cases hc : c = 0
  · left; rw [hc, map_zero]
  · right; rw [ord_alg hc]

lemma Ge.sum {ι : Type*} {s : Finset ι} {n : ℤ} {f : ι → FF W L} {P : Pt W L}
    (h : ∀ i ∈ s, Ge n (f i) P) : Ge n (∑ i ∈ s, f i) P :=
  Finset.sum_induction _ (fun g => Ge n g P) (fun _ _ => Ge.add) (Ge.zero _ _) h

lemma Ge.tau {n : ℤ} {f : FF W L} {P S : Pt W L} (h : Ge n f (P + S)) : Ge n (tau W L S f) P := by
  rcases h with h | h
  · left; rw [h, map_zero]
  · right; rwa [ord_tau]

/-- Strict domination in `Ge` form. -/
lemma ge_lead {f g : FF W L} {P : Pt W L} {n : ℤ} (hf : f ≠ 0) (hn : ord W L f P = n)
    (hg : Ge (n + 1) g P) : f + g ≠ 0 ∧ ord W L (f + g) P = n := by
  rw [← hn]; exact ord_add_eq_of_lt' hf P (hg.imp id (fun h => by omega))

lemma ge_CR {P : Pt W L} (hP : P ≠ 0) (r : CR W L) : Ge 0 (algebraMap (CR W L) (FF W L) r) P := by
  by_cases hr : algebraMap (CR W L) (FF W L) r = 0
  · exact Or.inl hr
  right
  refine ord_nonneg_of_nu_le hP hr ?_
  rw [nu_eq_valuation, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_le_one _ _

lemma ge_gx {P : Pt W L} (hP : P ≠ 0) : Ge 0 (gx W L) P := ge_CR hP _
lemma ge_gy {P : Pt W L} (hP : P ≠ 0) : Ge 0 (gy W L) P := ge_CR hP _

/-- **`ord_O y = -3`.** -/
theorem ord_gy_zero : ord W L (gy W L) 0 = -3 := by
  have heq := (equation_iff _ _).mp (gen_equation W L)
  rw [bc_a₁ W L (FF W L), bc_a₂ W L (FF W L), bc_a₃ W L (FF W L), bc_a₄ W L (FF W L),
    bc_a₆ W L (FF W L)] at heq
  set x := gx W L
  set y := gy W L
  set a1 := algebraMap L (FF W L) (W.baseChange L).toAffine.a₁
  set a2 := algebraMap L (FF W L) (W.baseChange L).toAffine.a₂
  set a3 := algebraMap L (FF W L) (W.baseChange L).toAffine.a₃
  set a4 := algebraMap L (FF W L) (W.baseChange L).toAffine.a₄
  set a6 := algebraMap L (FF W L) (W.baseChange L).toAffine.a₆
  have hx0 : x ≠ 0 := gx_ne_zero'
  have hx : ord W L x 0 = -2 := ord_gx_zero
  have hGx : Ge (-2) x 0 := Or.inr hx.ge
  have hx3 : ord W L (x ^ 3) 0 = -6 := by rw [ord_pow, hx]; norm_num
  have hR : Ge (-6 + 1) (a2 * x ^ 2 + a4 * x + a6) 0 := by
    refine ((((Ge.const _ _).mul (hGx.pow 2)).mono ?_).add (((Ge.const _ _).mul hGx).mono ?_)).add
      ((Ge.const _ _).mono ?_) <;> norm_num
  obtain ⟨hv0, hv⟩ := ge_lead (pow_ne_zero 3 hx0) hx3 hR
  have hE : y ^ 2 + (a1 * x * y + a3 * y) = x ^ 3 + (a2 * x ^ 2 + a4 * x + a6) := by
    linear_combination heq
  have hy0 : y ≠ 0 := by
    intro h0; apply hv0; rw [← hE, h0]; ring
  set b := ord W L y 0 with hbdef
  have hGy : Ge b y 0 := Or.inr le_rfl
  rcases (show b ≤ -4 ∨ b = -3 ∨ -2 ≤ b by omega) with hb | hb | hb
  · exfalso
    have hrest : Ge (2 * b + 1) (a1 * x * y + a3 * y) 0 :=
      ((((Ge.const _ _).mul hGx).mul hGy).mono (by omega)).add (((Ge.const _ _).mul hGy).mono (by omega))
    have hy2 : ord W L (y ^ 2) 0 = 2 * b := by rw [ord_pow]; push_cast; ring
    obtain ⟨-, hu⟩ := ge_lead (pow_ne_zero 2 hy0) hy2 hrest
    rw [hE, hv] at hu; omega
  · exact hb
  · exfalso
    have hu : Ge (-5) (y ^ 2 + (a1 * x * y + a3 * y)) 0 :=
      ((hGy.pow 2).mono (by push_cast; omega)).add
        (((((Ge.const _ _).mul hGx).mul hGy).mono (by omega)).add (((Ge.const _ _).mul hGy).mono (by omega)))
    rw [hE] at hu
    rcases hu with hu | hu
    · exact hv0 hu
    · omega

end OrdE

/-! ### The invariant sums `X_G = ∑_{T ∈ G} τ_T x`, `Y_G = ∑_{T ∈ G} τ_T y` -/

section Inv

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable (G : AddSubgroup (Pt W L))

/-- `f` is `G`-invariant. -/
def InvG (f : FF W L) : Prop := ∀ S ∈ G, tau W L S f = f

variable [Fintype G]

/-- The norm-type sum `∑_{T ∈ G} τ_T f`. -/
noncomputable def trG (f : FF W L) : FF W L := ∑ T : G, tau W L T f

variable {G}

lemma invG_trG (f : FF W L) : InvG G (trG G f) := by
  intro S hS
  simp only [trG, map_sum, ← tau_add_apply]
  exact Fintype.sum_equiv (Equiv.addLeft ⟨S, hS⟩) _ _ (fun T => by
    rw [Equiv.coe_addLeft, AddSubgroup.coe_add])

lemma InvG.ord_add {f : FF W L} (hf : InvG G f) {T : Pt W L} (hT : T ∈ G) (P : Pt W L) :
    ord W L f (P + T) = ord W L f P := by
  rw [← ord_tau, hf T hT]

lemma InvG.ord_mem {f : FF W L} (hf : InvG G f) {T : Pt W L} (hT : T ∈ G) :
    ord W L f T = ord W L f 0 := by
  rw [← hf.ord_add hT 0, zero_add]

/-- Off `G`, `τ_T f` is regular for every `T ∈ G` when `f` is regular at affine points. -/
lemma ge_trG_off {f : FF W L} (hf : ∀ Q : Pt W L, Q ≠ 0 → Ge 0 f Q) {P : Pt W L} (hP : P ∉ G) :
    Ge 0 (trG G f) P := by
  refine Ge.sum (fun T _ => Ge.tau (hf _ ?_))
  intro h0
  apply hP
  rw [show P = -(T : Pt W L) by rw [eq_neg_iff_add_eq_zero]; exact h0]
  exact G.neg_mem T.2

/-- At `O`: `trG f - f` is regular when `f` is regular at affine points. -/
lemma ge_trG_sub {f : FF W L} (hf : ∀ Q : Pt W L, Q ≠ 0 → Ge 0 f Q) :
    Ge 0 (trG G f - f) 0 := by
  have e : trG G f - f = ∑ T ∈ (Finset.univ : Finset G).erase 0, tau W L T f := by
    rw [trG, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : G)), AddSubgroup.coe_zero,
      tau_zero_apply, add_sub_cancel_left]
  rw [e]
  refine Ge.sum (fun T hT => Ge.tau (hf _ ?_))
  rw [zero_add]
  intro h0
  exact (Finset.ne_of_mem_erase hT) (Subtype.ext h0)

lemma ord_trG_zero {f : FF W L} (hf : ∀ Q : Pt W L, Q ≠ 0 → Ge 0 f Q) (hf0 : f ≠ 0) {n : ℤ}
    (hn : ord W L f 0 = n) (hneg : n < 0) : trG G f ≠ 0 ∧ ord W L (trG G f) 0 = n := by
  have h := ge_lead hf0 hn ((ge_trG_sub (G := G) hf).mono (by omega))
  rwa [add_sub_cancel] at h

variable (G) in
/-- `X_G`. -/
noncomputable abbrev qx : FF W L := trG G (gx W L)

variable (G) in
/-- `Y_G`. -/
noncomputable abbrev qy : FF W L := trG G (gy W L)

lemma ord_qx_zero : qx G ≠ 0 ∧ ord W L (qx G) 0 = -2 :=
  ord_trG_zero (fun _ hQ => ge_gx hQ) gx_ne_zero' ord_gx_zero (by norm_num)

lemma gy_ne_zero' : gy W L ≠ 0 := by
  intro h; have := ord_gy_zero (W := W) (L := L); rw [h] at this
  simp [ord] at this

lemma ord_qy_zero : qy G ≠ 0 ∧ ord W L (qy G) 0 = -3 :=
  ord_trG_zero (fun _ hQ => ge_gy hQ) gy_ne_zero' ord_gy_zero (by norm_num)

end Inv

end RPLib.DWS


