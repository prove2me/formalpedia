-- Prove2me | Definitions.Def_RPLib_S3_DWSIsogM
-- name    : RPLib_S3_DWSIsogM
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:54:20.682452+00:00
-- url     : https://prove2.me/theorems/58143602-3ec0-4231-b00c-5eab7823dbdd
-- title:
--   Weight-two Ramanujan-Petersson library: the values of the quotient map; surjectivity
-- statement:
--   The values of the quotient map; surjectivity.
--
--   * `pole_alg_Y`, `HV_of_ge_one`, **`HV_add_pole`** : adding a point with a pole at `P` to a point regular at `P`
--     keeps the values of the regular point (refined pole case of the addition law).
--   * **`qmap_val`** : for `S ∉ G`, `qmap S` is the affine point `(X_G(S), Y_G(S))`.
--   * `exists_not_two_torsion`, **`qmap_surjective`**.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSIsogL

/-!
# S3-DWS-Isog, part M: the values of the quotient map; surjectivity

* `pole_alg_Y`, `HV_of_ge_one`, **`HV_add_pole`** : adding a point with a pole at `P` to a point regular at `P`
  keeps the values of the regular point (refined pole case of the addition law).
* **`qmap_val`** : for `S ∉ G`, `qmap S` is the affine point `(X_G(S), Y_G(S))`.
* `exists_not_two_torsion`, **`qmap_surjective`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open IsDedekindDomain
open scoped nonZeroDivisors

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

/-- `addY` near a pole of the first point (pure algebra). -/
lemma pole_alg_Y {K : Type*} [Field K] {a₁ a₂ a₃ a₄ a₆ x₁ y₁ x₂ y₂ : K} (hd : x₁ - x₂ ≠ 0)
    (e : y₁ ^ 2 + a₁ * x₁ * y₁ + a₃ * y₁ = x₁ ^ 3 + a₂ * x₁ ^ 2 + a₄ * x₁ + a₆) :
    -((y₁ - y₂) / (x₁ - x₂) * (((y₁ - y₂) / (x₁ - x₂)) ^ 2 + a₁ * ((y₁ - y₂) / (x₁ - x₂)) - a₂ - x₁ - x₂
        - x₁) + y₁) - a₁ * (((y₁ - y₂) / (x₁ - x₂)) ^ 2 + a₁ * ((y₁ - y₂) / (x₁ - x₂)) - a₂ - x₁ - x₂)
      - a₃ =
    y₂ - ((2 * y₂ + a₁ * x₂ + a₃) * (a₁ * x₁ * y₁ + a₃ * y₁ - a₂ * x₁ ^ 2 - a₄ * x₁ - a₆ -
        3 * x₁ ^ 2 * x₂ + 3 * x₁ * x₂ ^ 2 - x₂ ^ 3 + y₂ * y₁) +
        (x₁ * (3 * x₂ ^ 2 + 2 * a₂ * x₂ + a₄ - a₁ * y₂) +
          (a₆ + y₂ ^ 2 + a₁ * x₂ * y₂ - 2 * x₂ ^ 3 - a₂ * x₂ ^ 2)) * (y₁ - y₂)) * (x₁ - x₂)⁻¹ ^ 3 -
      a₁ * ((-y₁ * (2 * y₂ + a₁ * x₂ + a₃) + x₁ * (3 * x₂ ^ 2 + 2 * a₂ * x₂ + a₄ - a₁ * y₂) +
        (a₆ + y₂ ^ 2 + a₁ * x₂ * y₂ - 2 * x₂ ^ 3 - a₂ * x₂ ^ 2)) * (x₁ - x₂)⁻¹ ^ 2) := by
  have hid : (x₁ - x₂) * (x₁ - x₂)⁻¹ = 1 := mul_inv_cancel₀ hd
  rw [pole_alg hd e, div_eq_mul_inv]
  linear_combination ((y₁ - y₂) + (2 * y₂ + a₁ * x₂ + a₃) * ((x₁ - x₂) ^ 2 * (x₁ - x₂)⁻¹ ^ 2 +
    (x₁ - x₂) * (x₁ - x₂)⁻¹ + 1)) * hid + (2 * y₂ + a₁ * x₂ + a₃) * (x₁ - x₂)⁻¹ ^ 3 * e

section Coords

variable {A : Type*} [CommRing A] {V : WeierstrassCurve.Affine A}

lemma pxV_neg (P : V.Point) : px (-P) = px P := by
  cases P with
  | zero => rfl
  | some x y h => rfl

lemma pyV_neg {P : V.Point} (hP : P ≠ 0) : py (-P) = V.negY (px P) (py P) := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => rfl

end Coords

section Val

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

lemma HV_of_ge_one {P : Pt W L} {hP : P ≠ 0} {f : FF W L} (h : Ge 1 f P) : HV W L P hP f 0 := by
  by_cases hf : f = 0
  · exact (HV_alg (W := W) (P := P) (hP := hP) (0 : L)).congr (by rw [hf, map_zero]) rfl
  have h1 := h.resolve_left hf
  rw [ord_eq hP] at h1
  have hne : nu W L P hP f ≠ 0 := (Valuation.ne_zero_iff _).mpr hf
  apply HV_of_nu_lt
  rw [← WithZero.exp_log hne, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

variable {W' : WeierstrassCurve F}

/-- **Pole case of the addition law, with values.** -/
theorem HV_add_pole {x₁ y₁ x₂ y₂ : FF W L} (h₁ : (W'.baseChange (FF W L)).toAffine.Equation x₁ y₁)
    {P : Pt W L} {hP : P ≠ 0} (hx₁ : x₁ ≠ 0) (ho : ord W L x₁ P = -2) (hy₁ : Ge (-3) y₁ P)
    {a c : L} (hx₂ : HV W L P hP x₂ a) (hy₂ : HV W L P hP y₂ c) :
    HV W L P hP ((W'.baseChange (FF W L)).toAffine.addX x₁ x₂ ((y₁ - y₂) / (x₁ - x₂))) a ∧
      HV W L P hP ((W'.baseChange (FF W L)).toAffine.addY x₁ x₂ y₁ ((y₁ - y₂) / (x₁ - x₂))) c := by
  have gx₂ := ge_of_HV hx₂
  have gy₂ := ge_of_HV hy₂
  obtain ⟨hd0, hdo⟩ : x₁ - x₂ ≠ 0 ∧ ord W L (x₁ - x₂) P = -2 := by
    rw [sub_eq_add_neg]; exact ge_lead hx₁ ho (gx₂.neg.mono (by norm_num))
  have hio : Ge 2 (x₁ - x₂)⁻¹ P := Or.inr (by rw [ord_inv, hdo]; norm_num)
  have hc : ∀ a : L, Ge 0 (algebraMap L (FF W L) a) P := fun a => Ge.const a P
  have hx1 : Ge (-2) x₁ P := Or.inr ho.ge
  have hk2 : Ge 0 (2 * y₂ + algebraMap L (FF W L) (W'.baseChange L).toAffine.a₁ * x₂ +
      algebraMap L (FF W L) (W'.baseChange L).toAffine.a₃) P :=
    (((Ge.ofNat 2 P).mul0 gy₂).add ((hc _).mul0 gx₂)).add (hc _)
  have hk1 : Ge 0 (3 * x₂ ^ 2 + 2 * algebraMap L (FF W L) (W'.baseChange L).toAffine.a₂ * x₂ +
      algebraMap L (FF W L) (W'.baseChange L).toAffine.a₄ -
      algebraMap L (FF W L) (W'.baseChange L).toAffine.a₁ * y₂) P :=
    ((((Ge.ofNat 3 P).mul0 gx₂.sq0).add (((Ge.ofNat 2 P).mul0 (hc _)).mul0 gx₂)).add (hc _)).sub
      ((hc _).mul0 gy₂)
  have hk0 : Ge 0 (algebraMap L (FF W L) (W'.baseChange L).toAffine.a₆ + y₂ ^ 2 +
      algebraMap L (FF W L) (W'.baseChange L).toAffine.a₁ * x₂ * y₂ - 2 * x₂ ^ 3 -
      algebraMap L (FF W L) (W'.baseChange L).toAffine.a₂ * x₂ ^ 2) P :=
    ((((hc _).add gy₂.sq0).add (((hc _).mul0 gx₂).mul0 gy₂)).sub
      ((Ge.ofNat 2 P).mul0 ((gx₂.pow 3).mono (by norm_num)))).sub ((hc _).mul0 gx₂.sq0)
  have hN := (((hy₁.neg.mul hk2).mono (by norm_num : (-3 : ℤ) ≤ -3 + 0)).add
    ((Ge.mul (Or.inr ho.ge) hk1).mono (by norm_num))).add (hk0.mono (by norm_num))
  have hNi := (hN.mul (hio.pow 2)).mono (by norm_num : (1 : ℤ) ≤ -3 + (2 : ℕ) * 2)
  have hB : Ge (-5) (algebraMap L (FF W L) (W'.baseChange L).toAffine.a₁ * x₁ * y₁ +
      algebraMap L (FF W L) (W'.baseChange L).toAffine.a₃ * y₁ -
      algebraMap L (FF W L) (W'.baseChange L).toAffine.a₂ * x₁ ^ 2 -
      algebraMap L (FF W L) (W'.baseChange L).toAffine.a₄ * x₁ -
      algebraMap L (FF W L) (W'.baseChange L).toAffine.a₆ -
      3 * x₁ ^ 2 * x₂ + 3 * x₁ * x₂ ^ 2 - x₂ ^ 3 + y₂ * y₁) P :=
    (((((((((((hc _).mul hx1).mul hy₁).mono (by norm_num)).add (((hc _).mul hy₁).mono (by norm_num))).sub
      (((hc _).mul (hx1.pow 2)).mono (by norm_num))).sub (((hc _).mul hx1).mono (by norm_num))).sub
      ((hc _).mono (by norm_num))).sub ((((Ge.ofNat 3 P).mul (hx1.pow 2)).mul gx₂).mono (by norm_num))).add
      ((((Ge.ofNat 3 P).mul hx1).mul (gx₂.pow 2)).mono (by norm_num))).sub
      ((gx₂.pow 3).mono (by norm_num))).add ((gy₂.mul hy₁).mono (by norm_num))
  have hK := ((hx1.mul hk1).mono (by norm_num : (-2 : ℤ) ≤ -2 + 0)).add (hk0.mono (by norm_num))
  have hyd : Ge (-3) (y₁ - y₂) P := hy₁.sub (gy₂.mono (by norm_num))
  have hNum := ((hk2.mul hB).mono (by norm_num : (-5 : ℤ) ≤ 0 + -5)).add
    ((hK.mul hyd).mono (by norm_num))
  have hNumi := (hNum.mul (hio.pow 3)).mono (by norm_num : (1 : ℤ) ≤ -5 + (3 : ℕ) * 2)
  constructor
  · rw [addX, bc_a₁ W' L (FF W L), bc_a₂ W' L (FF W L), pole_alg hd0 (eqn_FF h₁)]
    exact (hx₂.add (HV_of_ge_one hNi)).congr rfl (add_zero a)
  · rw [addY, negY, negAddY, addX, bc_a₁ W' L (FF W L), bc_a₂ W' L (FF W L), bc_a₃ W' L (FF W L)]
    refine HV.congr ?_ (pole_alg_Y hd0 (eqn_FF h₁)).symm rfl
    exact ((hy₂.sub (HV_of_ge_one hNumi)).sub ((HV_alg (P := P) (hP := hP) _).mul
      (HV_of_ge_one hNi))).congr rfl (by ring)

end Val

section QVal

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable {G : AddSubgroup (Pt W L)} [Fintype G] {W' : WeierstrassCurve F} [W'.IsElliptic]

/-- **Values of the quotient map**: off `G`, `qmap S = (X_G(S), Y_G(S))`. -/
theorem qmap_val (hG : (Fintype.card G : L) ≠ 0)
    (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) {S : Pt W L} (hS : S ∉ G)
    {a c : L} (ha : HV W L S (ne_zero_of_nmem hS) (qx G) a)
    (hc : HV W L S (ne_zero_of_nmem hS) (qy G) c) :
    qmap hG hW' S ≠ 0 ∧ px (qmap hG hW' S) = a ∧ py (qmap hG hW' S) = c := by
  have hSn : -S ∉ G := fun h => hS (by simpa using G.neg_mem h)
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q, Q = Point.map (W' := W'.toAffine) ((tauHom W L (-S)).restrictScalars F)
      (qPt hW') := ⟨_, rfl⟩
  have hQ0 : Q₁ ≠ 0 := by rw [hQ₁, qPt, Point.map_some]; exact Point.some_ne_zero _
  have hQ₁0 : -Q₁ ≠ 0 := neg_ne_zero.mpr hQ0
  have hx₁ : px Q₁ = tau W L (-S) (qx G) := by rw [hQ₁, px_map, tau_apply]; rfl
  have hy₁ : py Q₁ = tau W L (-S) (qy G) := by rw [hQ₁, py_map, tau_apply]; rfl
  have hQ₁e : Q₁ = qPt hW' + ιQ W W' L (qfun hG hW' (-S)) := by rw [hQ₁]; exact qfun_spec hG hW' (-S)
  have hD : ιQ W W' L (qmap hG hW' S) = -Q₁ + qPt hW' := by
    rw [hQ₁e, ← qmap_apply, map_neg, map_neg]; abel
  have hne : px (-Q₁) ≠ px (qPt hW') := by
    rw [pxV_neg, hx₁, px_qPt]; exact tau_qx_ne hSn
  have hx0 : px (-Q₁) ≠ 0 := by rw [pxV_neg, hx₁]; exact tau_ne_zero _ (ord_qx_zero (G := G)).1
  have hox : ord W L (tau W L (-S) (qx G)) S = -2 := by
    rw [ord_tau, add_neg_cancel, (ord_qx_zero (G := G)).2]
  have hoy : ord W L (tau W L (-S) (qy G)) S = -3 := by
    rw [ord_tau, add_neg_cancel, (ord_qy_zero (G := G)).2]
  have ho : ord W L (px (-Q₁)) S = -2 := by rw [pxV_neg, hx₁, hox]
  have hy3 : Ge (-3) (py (-Q₁)) S := by
    rw [pyV_neg hQ0, hx₁, hy₁, negY, bc_a₁ W' L (FF W L), bc_a₃ W' L (FF W L)]
    have gx : Ge (-2) (tau W L (-S) (qx G)) S := Or.inr hox.ge
    have gy : Ge (-3) (tau W L (-S) (qy G)) S := Or.inr hoy.ge
    exact (gy.neg.sub (((Ge.const _ S).mul gx).mono (by norm_num))).sub
      ((Ge.const _ S).mono (by norm_num))
  have e₁ := (nonsingular_px_py hQ₁0).1
  have ha' : HV W L S (ne_zero_of_nmem hS) (px (qPt hW')) a := by rw [px_qPt]; exact ha
  have hc' : HV W L S (ne_zero_of_nmem hS) (py (qPt hW')) c := by rw [py_qPt]; exact hc
  obtain ⟨hX, hY⟩ := HV_add_pole e₁ hx0 ho hy3 ha' hc'
  have hC0 : qmap hG hW' S ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hD
    have h1 : Q₁ = qPt hW' := neg_add_eq_zero.mp hD.symm
    have h2 := congrArg px h1
    rw [hx₁, px_qPt] at h2
    exact tau_qx_ne hSn h2
  have hpx : HV W L S (ne_zero_of_nmem hS) (px (ιQ W W' L (qmap hG hW' S))) a := by
    rw [hD, px_add' hQ₁0 (qPt_ne_zero hW') hne]; exact hX
  have hpy : HV W L S (ne_zero_of_nmem hS) (py (ιQ W W' L (qmap hG hW' S))) c := by
    rw [hD, py_add' hQ₁0 (qPt_ne_zero hW') hne]; exact hY
  rw [ιQ, px_map] at hpx
  rw [ιQ, py_map] at hpy
  exact ⟨hC0, (HV_unique hpx (HV_alg _)).symm, (HV_unique hpy (HV_alg _)).symm⟩

lemma exists_not_two_torsion : ∃ Q : Pt W' L, Q + Q ≠ 0 := by
  by_contra h
  push Not at h
  have h2 : ((2 : ℤ) : AddMonoid.End (Pt W' L)) = 0 := by
    refine AddMonoidHom.ext fun Q => ?_
    show (2 : ℤ) • Q = 0
    rw [two_zsmul, h Q]
  exact two_ne_zero (intCast_eq_zero (W := W') (L := L) h2)

lemma ne_negY_of_two {Q : Pt W' L} (hQ : Q + Q ≠ 0) :
    Q ≠ 0 ∧ py Q ≠ (W'.baseChange L).toAffine.negY (px Q) (py Q) := by
  have hQ0 : Q ≠ 0 := by rintro rfl; exact hQ (add_zero 0)
  refine ⟨hQ0, fun h => hQ ?_⟩
  have e : -Q = Q :=
    eq_of_px_py (neg_ne_zero.mpr hQ0) hQ0 (pxV_neg Q) (by rw [pyV_neg hQ0]; exact h.symm)
  calc Q + Q = -Q + Q := by rw [e]
    _ = 0 := neg_add_cancel Q

/-- **The quotient map is surjective.** -/
theorem qmap_surjective (hG : (Fintype.card G : L) ≠ 0)
    (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) :
    Function.Surjective (qmap hG hW') := by
  have hreg : ∀ Q : Pt W' L, Q + Q ≠ 0 → ∃ P, qmap hG hW' P = Q := by
    intro Q hQ
    obtain ⟨hQ0, h2⟩ := ne_negY_of_two hQ
    obtain ⟨P, hP, ha, hc⟩ := exists_preimage hG hW' (nonsingular_px_py hQ0).1 h2
    obtain ⟨h0, hx, hy⟩ := qmap_val hG hW' hP ha hc
    exact ⟨P, eq_of_px_py h0 hQ0 hx hy⟩
  intro Q
  by_contra hQ
  obtain ⟨R, hR⟩ := exists_not_two_torsion (W' := W') (L := L)
  obtain ⟨P₁, hP₁⟩ := hreg R hR
  have hQQ : Q + Q = 0 := by
    by_contra h
    exact hQ (hreg Q h)
  have hQR : (Q + R) + (Q + R) = 0 := by
    by_contra h
    obtain ⟨P₂, hP₂⟩ := hreg _ h
    exact hQ ⟨P₂ - P₁, by rw [map_sub, hP₂, hP₁]; abel⟩
  exact hR (by rw [show R + R = (Q + R) + (Q + R) - (Q + Q) by abel, hQR, hQQ, sub_zero])

end QVal

end RPLib.DWS


