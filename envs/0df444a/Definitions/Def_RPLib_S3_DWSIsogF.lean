-- Prove2me | Definitions.Def_RPLib_S3_DWSIsogF
-- name    : RPLib_S3_DWSIsogF
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:33:57.648307+00:00
-- url     : https://prove2.me/theorems/75be4a7b-cf39-421b-881b-02d898959b05
-- title:
--   Weight-two Ramanujan-Petersson library: functions invariant under a finite subgroup `G`
-- statement:
--   Functions invariant under a finite subgroup `G`.
--
--   * `GoodQ G f` : `f` is `G`-invariant and regular off `G`.
--   * `GoodQ.eq_const` (no pole at `O` ⇒ constant), `GoodQ.ord_ne_neg_one` (no simple pole at `O`, when
--     `p ∤ #G`), `GoodQ.lead` (leading-coefficient step).
--   * `exists_curve` : `Y² - X³ = c₁ XY + c₂ X² + c₃ Y + c₄ X + c₅` for `X = qx G`, `Y = qy G`;
--     `curve_coeff_unique`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSIsogE

/-!
# S3-DWS-Isog, part F: functions invariant under a finite subgroup `G`

* `GoodQ G f` : `f` is `G`-invariant and regular off `G`.
* `GoodQ.eq_const` (no pole at `O` ⇒ constant), `GoodQ.ord_ne_neg_one` (no simple pole at `O`, when
  `p ∤ #G`), `GoodQ.lead` (leading-coefficient step).
* `exists_curve` : `Y² - X³ = c₁ XY + c₂ X² + c₃ Y + c₄ X + c₅` for `X = qx G`, `Y = qy G`;
  `curve_coeff_unique`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open IsDedekindDomain
open scoped nonZeroDivisors

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section GoodQ

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable {G : AddSubgroup (Pt W L)}

variable (G) in
/-- `f` is `G`-invariant and regular off `G`. -/
def GoodQ (f : FF W L) : Prop := InvG G f ∧ ∀ P : Pt W L, P ∉ G → Ge 0 f P

lemma GoodQ.const (c : L) : GoodQ G (algebraMap L (FF W L) c) :=
  ⟨fun S _ => AlgEquiv.commutes _ c, fun P _ => Ge.const c P⟩

lemma GoodQ.add {f g : FF W L} (hf : GoodQ G f) (hg : GoodQ G g) : GoodQ G (f + g) :=
  ⟨fun S hS => by rw [map_add, hf.1 S hS, hg.1 S hS], fun P hP => (hf.2 P hP).add (hg.2 P hP)⟩

lemma GoodQ.sub {f g : FF W L} (hf : GoodQ G f) (hg : GoodQ G g) : GoodQ G (f - g) :=
  ⟨fun S hS => by rw [map_sub, hf.1 S hS, hg.1 S hS], fun P hP => (hf.2 P hP).sub (hg.2 P hP)⟩

lemma GoodQ.mul {f g : FF W L} (hf : GoodQ G f) (hg : GoodQ G g) : GoodQ G (f * g) :=
  ⟨fun S hS => by rw [map_mul, hf.1 S hS, hg.1 S hS],
    fun P hP => ((hf.2 P hP).mul (hg.2 P hP)).mono (by norm_num)⟩

lemma GoodQ.pow {f : FF W L} (hf : GoodQ G f) (k : ℕ) : GoodQ G (f ^ k) :=
  ⟨fun S hS => by rw [map_pow, hf.1 S hS], fun P hP => ((hf.2 P hP).pow k).mono (by simp)⟩

lemma goodQ_trG [Fintype G] {f : FF W L} (hf : ∀ Q : Pt W L, Q ≠ 0 → Ge 0 f Q) :
    GoodQ G (trG G f) :=
  ⟨invG_trG f, fun _ hP => ge_trG_off hf hP⟩

/-- **L1**: an invariant function with poles only on `G` and no pole at `O` is constant. -/
theorem GoodQ.eq_const [Fintype G] {f : FF W L} (hf : GoodQ G f) (h0 : Ge 0 f 0) :
    ∃ c : L, f = algebraMap L (FF W L) c := by
  by_cases hf0 : f = 0
  · exact ⟨0, by rw [hf0, map_zero]⟩
  by_contra hc
  push Not at hc
  obtain ⟨P, hP⟩ := exists_pole hf0 hc
  by_cases hPG : P ∈ G
  · rw [hf.1.ord_mem hPG] at hP
    have := h0.resolve_left hf0; omega
  · have := (hf.2 P hPG).resolve_left hf0; omega

/-- **L2 (simple-pole lemma)**: if `p ∤ #G`, no invariant function regular off `G` has a simple pole at `O`. -/
theorem GoodQ.ord_ne_neg_one [Fintype G] (hG : (Fintype.card G : L) ≠ 0) {f : FF W L} (hf : GoodQ G f)
    (hf0 : f ≠ 0) : ord W L f 0 ≠ -1 := by
  intro h1
  classical
  haveI : Infinite (Pt W L) := infinite_pt
  have hfin : ({P : Pt W L | Fintype.card G • P = 0} ∪ (G : Set (Pt W L))).Finite :=
    (finite_En _ hG).union (Set.toFinite _)
  obtain ⟨P, hP⟩ := hfin.infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, SetLike.mem_coe, not_or] at hP
  obtain ⟨hnP, hPG⟩ := hP
  obtain ⟨c, hc⟩ := exists_value hf0 ((hf.2 P hPG).resolve_left hf0)
  have hgO := ge_lead hf0 h1 ((Ge.const c 0).neg.mono (by norm_num))
  rw [← sub_eq_add_neg] at hgO
  set g := f - algebraMap L (FF W L) c with hgdef
  have hg0 : g ≠ 0 := hgO.1
  have hgP : 1 ≤ ord W L g P := hc.resolve_left hg0
  have hgG : GoodQ G g := hf.sub (GoodQ.const c)
  set A : Finset (Pt W L) := (Finset.univ : Finset G).map (Function.Embedding.subtype _) with hAdef
  have hA : ∀ Q, Q ∈ A ↔ Q ∈ G := fun Q => by simp [hAdef]
  set B : Finset (Pt W L) := A.map (addLeftEmbedding P) with hBdef
  have hB : ∀ Q, Q ∈ B → ∃ T ∈ G, Q = P + T := fun Q hQ => by
    obtain ⟨T, hT, rfl⟩ := Finset.mem_map.mp hQ
    exact ⟨T, (hA T).mp hT, rfl⟩
  set S := (ord_finite hg0).toFinset
  set Z := A ∪ B ∪ S with hZdef
  have hAZ : A ⊆ Z := fun Q hQ => by simp [hZdef, hQ]
  have hBZ : B ⊆ Z := fun Q hQ => by simp [hZdef, hQ]
  have hSZ : ∀ Q, ord W L g Q ≠ 0 → Q ∈ Z := fun Q hQ => by
    have : Q ∈ S := (ord_finite hg0).mem_toFinset.mpr hQ
    simp [hZdef, this]
  let D : Pt W L → ℤ := fun Q => (if Q ∈ B then 1 else 0) - (if Q ∈ A then 1 else 0)
  have hD : ∀ Q, D Q ≤ ord W L g Q := by
    intro Q
    by_cases hQA : Q ∈ A
    · have hQG := (hA Q).mp hQA
      have hQB : Q ∉ B := fun hQB => by
        obtain ⟨T, hT, hQT⟩ := hB Q hQB
        apply hPG
        rw [show P = Q - T by rw [hQT]; abel]
        exact G.sub_mem hQG hT
      simp only [D, if_pos hQA, if_neg hQB]
      rw [hgG.1.ord_mem hQG, hgO.2]; norm_num
    by_cases hQB : Q ∈ B
    · obtain ⟨T, hT, hQT⟩ := hB Q hQB
      simp only [D, if_pos hQB, if_neg hQA]
      rw [hQT, hgG.1.ord_add hT]; omega
    · simp only [D, if_neg hQB, if_neg hQA, sub_zero]
      exact (hgG.2 Q (fun h => hQA ((hA Q).mpr h))).resolve_left hg0
  have hcard : B.card = A.card := Finset.card_map _
  have hsumD : ∑ Q ∈ Z, D Q = 0 := by
    simp only [D, Finset.sum_sub_distrib, Finset.sum_boole, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr hBZ, Finset.inter_eq_right.mpr hAZ, hcard, sub_self]
  have hsumg : ∑ Q ∈ Z, ord W L g Q = 0 := sum_ord_eq_zero hg0 Z hSZ
  have hEq : ∀ Q ∈ Z, ord W L g Q = D Q := by
    have h0 : ∑ Q ∈ Z, (ord W L g Q - D Q) = 0 := by
      rw [Finset.sum_sub_distrib, hsumg, hsumD, sub_self]
    intro Q hQ
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun Q _ => sub_nonneg.mpr (hD Q))).mp h0 Q hQ
    omega
  have habel := sum_ord_smul hg0 Z (fun Q _ hQ => hSZ Q hQ)
  rw [Finset.sum_congr rfl (fun Q hQ => by rw [hEq Q hQ])] at habel
  simp only [D, sub_smul, ite_smul, one_smul, zero_smul, Finset.sum_sub_distrib, Finset.sum_ite_mem,
    Finset.inter_eq_right.mpr hBZ, Finset.inter_eq_right.mpr hAZ] at habel
  rw [hBdef, Finset.sum_map] at habel
  simp only [addLeftEmbedding_apply] at habel
  apply hnP
  simpa [hAdef, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ] using habel

/-- Leading-coefficient step. -/
theorem GoodQ.lead {f M : FF W L} (hf : GoodQ G f) (hM : GoodQ G M) (hM0 : M ≠ 0) {n : ℤ}
    (hMn : ord W L M 0 = n) (hfn : Ge n f 0) :
    ∃ c : L, GoodQ G (f - algebraMap L (FF W L) c * M) ∧
      Ge (n + 1) (f - algebraMap L (FF W L) c * M) 0 := by
  have hgood : ∀ c : L, GoodQ G (f - algebraMap L (FF W L) c * M) :=
    fun c => hf.sub ((GoodQ.const c).mul hM)
  by_cases hf0 : f = 0
  · exact ⟨0, hgood 0, Or.inl (by rw [hf0, map_zero, zero_mul, sub_zero])⟩
  have hfn' := hfn.resolve_left hf0
  rcases hfn'.lt_or_eq with hlt | heq
  · exact ⟨0, hgood 0, Or.inr (by rw [map_zero, zero_mul, sub_zero]; omega)⟩
  have hh0 : f / M ≠ 0 := div_ne_zero hf0 hM0
  have hh : ord W L (f / M) 0 = 0 := by rw [ord_div hf0 hM0, hMn, ← heq, sub_self]
  obtain ⟨c, hc⟩ := exists_value hh0 hh.ge
  refine ⟨c, hgood c, ?_⟩
  have e : f - algebraMap L (FF W L) c * M = M * (f / M - algebraMap L (FF W L) c) := by
    rw [mul_sub, mul_comm M (f / M), div_mul_cancel₀ f hM0]; ring
  rw [e]
  exact Ge.mul (n := n) (m := 1) (Or.inr hMn.ge) hc

lemma coeff_eq_zero_of_lead {M r : FF W L} (hM0 : M ≠ 0) {n : ℤ} (hMn : ord W L M 0 = n)
    (hr : Ge (n + 1) r 0) {c : L} (h : algebraMap L (FF W L) c * M + r = 0) : c = 0 := by
  by_contra hc
  have hc' : algebraMap L (FF W L) c ≠ 0 := (_root_.map_ne_zero _).mpr hc
  have hcMn : ord W L (algebraMap L (FF W L) c * M) 0 = n := by
    rw [ord_mul hc' hM0, ord_alg hc, hMn, zero_add]
  exact (ge_lead (mul_ne_zero hc' hM0) hcMn hr).1 h

lemma Ge.ofNat (k : ℕ) [k.AtLeastTwo] (P : Pt W L) : Ge 0 (OfNat.ofNat k : FF W L) P := by
  rw [← map_ofNat (algebraMap L (FF W L)) k]; exact Ge.const _ _

end GoodQ

/-! ### The quotient curve equation -/

section Curve

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable {G : AddSubgroup (Pt W L)} [Fintype G]

lemma goodQ_qx : GoodQ G (qx G) := goodQ_trG (fun _ hQ => ge_gx hQ)
lemma goodQ_qy : GoodQ G (qy G) := goodQ_trG (fun _ hQ => ge_gy hQ)
lemma ge_qx : Ge (-2) (qx G) 0 := Or.inr ord_qx_zero.2.ge
lemma ge_qy : Ge (-3) (qy G) 0 := Or.inr ord_qy_zero.2.ge

/-- `Y² - X³` has a pole of order at most `5` at `O`. -/
lemma ge_qy2_sub_qx3 : Ge (-5) (qy G ^ 2 - qx G ^ 3) 0 := by
  have hu : Ge 0 (qx G - gx W L) 0 := ge_trG_sub (fun _ hQ => ge_gx hQ)
  have hv : Ge 0 (qy G - gy W L) 0 := ge_trG_sub (fun _ hQ => ge_gy hQ)
  have heq := (equation_iff _ _).mp (gen_equation W L)
  rw [bc_a₁ W L (FF W L), bc_a₂ W L (FF W L), bc_a₃ W L (FF W L), bc_a₄ W L (FF W L),
    bc_a₆ W L (FF W L)] at heq
  set x := gx W L
  set y := gy W L
  set u := qx G - x
  set v := qy G - y
  set a1 := algebraMap L (FF W L) (W.baseChange L).toAffine.a₁
  set a2 := algebraMap L (FF W L) (W.baseChange L).toAffine.a₂
  set a3 := algebraMap L (FF W L) (W.baseChange L).toAffine.a₃
  set a4 := algebraMap L (FF W L) (W.baseChange L).toAffine.a₄
  set a6 := algebraMap L (FF W L) (W.baseChange L).toAffine.a₆
  have hx : Ge (-2) x 0 := Or.inr ord_gx_zero.ge
  have hy : Ge (-3) y 0 := Or.inr ord_gy_zero.ge
  have e : qy G ^ 2 - qx G ^ 3 = ((-(a1 * x * y) - a3 * y + a2 * x ^ 2 + a4 * x + a6) +
      (2 * y * v + v ^ 2 - 3 * x ^ 2 * u - 3 * x * u ^ 2 - u ^ 3)) := by
    simp only [u, v]; linear_combination heq
  rw [e]
  have c0 : ∀ c : L, Ge 0 (algebraMap L (FF W L) c) 0 := fun c => Ge.const c 0
  refine Ge.add ?_ ?_
  · refine ((((((c0 _).mul hx).mul hy).neg.mono ?_).sub (((c0 _).mul hy).mono ?_)).add
      (((c0 _).mul (hx.pow 2)).mono ?_)).add (((c0 _).mul hx).mono ?_) |>.add ((c0 _).mono ?_) <;>
      norm_num
  · refine (((((((Ge.ofNat 2 0).mul hy).mul hv).mono ?_).add ((hv.pow 2).mono ?_)).sub
      ((((Ge.ofNat 3 0).mul (hx.pow 2)).mul hu).mono ?_)).sub
      ((((Ge.ofNat 3 0).mul hx).mul (hu.pow 2)).mono ?_)).sub ((hu.pow 3).mono ?_) <;> norm_num

/-- **The quotient curve equation.** -/
theorem exists_curve (hG : (Fintype.card G : L) ≠ 0) :
    ∃ c₁ c₂ c₃ c₄ c₅ : L, qy G ^ 2 - qx G ^ 3 =
      algebraMap L (FF W L) c₁ * (qx G * qy G) + algebraMap L (FF W L) c₂ * qx G ^ 2 +
      algebraMap L (FF W L) c₃ * qy G + algebraMap L (FF W L) c₄ * qx G + algebraMap L (FF W L) c₅ := by
  have hX := goodQ_qx (G := G)
  have hY := goodQ_qy (G := G)
  obtain ⟨hX0, hXo⟩ := ord_qx_zero (G := G)
  obtain ⟨hY0, hYo⟩ := ord_qy_zero (G := G)
  have h5 : ord W L (qx G * qy G) 0 = -5 := by rw [ord_mul hX0 hY0, hXo, hYo]; norm_num
  have h4 : ord W L (qx G ^ 2) 0 = -4 := by rw [ord_pow, hXo]; norm_num
  obtain ⟨c₁, g1, b1⟩ := ((hY.pow 2).sub (hX.pow 3)).lead (hX.mul hY) (mul_ne_zero hX0 hY0) h5
    ge_qy2_sub_qx3
  obtain ⟨c₂, g2, b2⟩ := g1.lead (hX.pow 2) (pow_ne_zero 2 hX0) h4 (b1.mono (by norm_num))
  obtain ⟨c₃, g3, b3⟩ := g2.lead hY hY0 hYo (b2.mono (by norm_num))
  obtain ⟨c₄, g4, b4⟩ := g3.lead hX hX0 hXo (b3.mono (by norm_num))
  have b5 : Ge 0 (qy G ^ 2 - qx G ^ 3 - algebraMap L (FF W L) c₁ * (qx G * qy G) -
      algebraMap L (FF W L) c₂ * qx G ^ 2 - algebraMap L (FF W L) c₃ * qy G -
      algebraMap L (FF W L) c₄ * qx G) 0 := by
    rcases b4 with h | h
    · exact Or.inl h
    · by_cases h0 : qy G ^ 2 - qx G ^ 3 - algebraMap L (FF W L) c₁ * (qx G * qy G) -
          algebraMap L (FF W L) c₂ * qx G ^ 2 - algebraMap L (FF W L) c₃ * qy G -
          algebraMap L (FF W L) c₄ * qx G = 0
      · exact Or.inl h0
      · have := g4.ord_ne_neg_one hG h0
        right; omega
  obtain ⟨c₅, hc5⟩ := g4.eq_const b5
  exact ⟨c₁, c₂, c₃, c₄, c₅, by linear_combination hc5⟩

/-- The coefficients of the quotient curve are unique. -/
theorem curve_coeff_unique {c₁ c₂ c₃ c₄ c₅ : L}
    (h : algebraMap L (FF W L) c₁ * (qx G * qy G) + algebraMap L (FF W L) c₂ * qx G ^ 2 +
      algebraMap L (FF W L) c₃ * qy G + algebraMap L (FF W L) c₄ * qx G +
      algebraMap L (FF W L) c₅ = 0) :
    c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 ∧ c₄ = 0 ∧ c₅ = 0 := by
  obtain ⟨hX0, hXo⟩ := ord_qx_zero (G := G)
  obtain ⟨hY0, hYo⟩ := ord_qy_zero (G := G)
  have hX : Ge (-2) (qx G) 0 := ge_qx
  have hY : Ge (-3) (qy G) 0 := ge_qy
  have c0 : ∀ c : L, Ge 0 (algebraMap L (FF W L) c) 0 := fun c => Ge.const c 0
  have h5 : ord W L (qx G * qy G) 0 = -5 := by rw [ord_mul hX0 hY0, hXo, hYo]; norm_num
  have h4 : ord W L (qx G ^ 2) 0 = -4 := by rw [ord_pow, hXo]; norm_num
  have e1 : c₁ = 0 := coeff_eq_zero_of_lead (mul_ne_zero hX0 hY0) h5
    (r := algebraMap L (FF W L) c₂ * qx G ^ 2 + algebraMap L (FF W L) c₃ * qy G +
      algebraMap L (FF W L) c₄ * qx G + algebraMap L (FF W L) c₅)
    ((((((c0 _).mul (hX.pow 2)).mono (by norm_num)).add (((c0 _).mul hY).mono (by norm_num))).add
      (((c0 _).mul hX).mono (by norm_num))).add ((c0 _).mono (by norm_num)))
    (by rw [← h]; ring)
  subst e1
  have e2 : c₂ = 0 := coeff_eq_zero_of_lead (pow_ne_zero 2 hX0) h4
    (r := algebraMap L (FF W L) c₃ * qy G + algebraMap L (FF W L) c₄ * qx G + algebraMap L (FF W L) c₅)
    (((((c0 _).mul hY).mono (by norm_num)).add (((c0 _).mul hX).mono (by norm_num))).add
      ((c0 _).mono (by norm_num)))
    (by rw [← h, map_zero]; ring)
  subst e2
  have e3 : c₃ = 0 := coeff_eq_zero_of_lead hY0 hYo
    (r := algebraMap L (FF W L) c₄ * qx G + algebraMap L (FF W L) c₅)
    ((((c0 _).mul hX).mono (by norm_num)).add ((c0 _).mono (by norm_num)))
    (by rw [← h, map_zero]; ring)
  subst e3
  have e4 : c₄ = 0 := coeff_eq_zero_of_lead hX0 hXo (r := algebraMap L (FF W L) c₅)
    ((c0 _).mono (by norm_num)) (by rw [← h, map_zero]; ring)
  subst e4
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  simp only [map_zero, zero_mul, zero_add] at h
  exact (map_eq_zero _).mp h

end Curve

end RPLib.DWS


