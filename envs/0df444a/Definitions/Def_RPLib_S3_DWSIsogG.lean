-- Prove2me | Definitions.Def_RPLib_S3_DWSIsogG
-- name    : RPLib_S3_DWSIsogG
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:36:27.148079+00:00
-- url     : https://prove2.me/theorems/655c54d7-8b65-46d4-b29a-5eab118106fb
-- title:
--   Weight-two Ramanujan-Petersson library: the quotient Weierstrass curve over `L` is nonsingular
-- statement:
--   The quotient Weierstrass curve over `L` is nonsingular.
--
--   * `exists_singular` : a Weierstrass curve with `Δ = 0` over an algebraically closed field has a singular
--     affine point (all characteristics).
--   * `exists_qcurve` : `(X_G, Y_G)` satisfies a Weierstrass equation `V` over `L`; `qcurve_unique`.
--   * `qcurve_Δ_ne_zero` : `V.Δ ≠ 0` (a singular point would give an invariant function with a simple pole).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSIsogF

/-!
# S3-DWS-Isog, part G: the quotient Weierstrass curve over `L` is nonsingular

* `exists_singular` : a Weierstrass curve with `Δ = 0` over an algebraically closed field has a singular
  affine point (all characteristics).
* `exists_qcurve` : `(X_G, Y_G)` satisfies a Weierstrass equation `V` over `L`; `qcurve_unique`.
* `qcurve_Δ_ne_zero` : `V.Δ ≠ 0` (a singular point would give an invariant function with a simple pole).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open IsDedekindDomain
open scoped nonZeroDivisors

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section Singular

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- A Weierstrass curve with `Δ = 0` over an algebraically closed field has a singular point. -/
theorem exists_singular (V : WeierstrassCurve K) (hΔ : V.Δ = 0) :
    ∃ x y : K, V.toAffine.Equation x y ∧ ¬ V.toAffine.Nonsingular x y := by
  suffices h : ∃ x y : K, y ^ 2 + V.a₁ * x * y + V.a₃ * y = x ^ 3 + V.a₂ * x ^ 2 + V.a₄ * x + V.a₆ ∧
      V.a₁ * y - (3 * x ^ 2 + 2 * V.a₂ * x + V.a₄) = 0 ∧ 2 * y + V.a₁ * x + V.a₃ = 0 by
    obtain ⟨x, y, hE, hX, hY⟩ := h
    have hE' : V.toAffine.Equation x y := (V.toAffine.equation_iff x y).mpr hE
    refine ⟨x, y, hE', fun hns => ?_⟩
    rcases ((V.toAffine.nonsingular_iff' x y).mp hns).2 with h | h
    · exact h hX
    · exact h hY
  have hD : V.Δ = -V.b₂ ^ 2 * V.b₈ - 8 * V.b₄ ^ 3 - 27 * V.b₆ ^ 2 + 9 * V.b₂ * V.b₄ * V.b₆ := rfl
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈] at hD
  by_cases h2 : (2 : K) = 0
  · by_cases ha1 : V.a₁ = 0
    · have h3 : V.a₃ = 0 := by
        have key : V.a₃ ^ 4 = 0 := by
          rw [hΔ, ha1] at hD
          linear_combination (-hD) - ((-216)*V.a₆^2 + (-32)*V.a₄^3 + (-108)*V.a₃^2*V.a₆ + (-14)*V.a₃^4 +
            (144)*V.a₂*V.a₄*V.a₆ + (36)*V.a₂*V.a₃^2*V.a₄ + (8)*V.a₂^2*V.a₄^2 + (-32)*V.a₂^3*V.a₆ +
            (-8)*V.a₂^3*V.a₃^2) * h2
        exact pow_eq_zero_iff (by norm_num) |>.mp key
      obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (-V.a₄) (by norm_num : 0 < 2)
      obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x ^ 3 + V.a₂ * x ^ 2 + V.a₄ * x + V.a₆)
        (by norm_num : 0 < 2)
      refine ⟨x, y, ?_, ?_, ?_⟩
      · rw [ha1, h3, hy]; ring
      · rw [ha1]; linear_combination (-3) * hx - (V.a₂ * x - V.a₄) * h2
      · rw [ha1, h3]; linear_combination y * h2
    · set x := -V.a₃ / V.a₁ with hxdef
      set y := (3 * x ^ 2 + 2 * V.a₂ * x + V.a₄) / V.a₁ with hydef
      have hx : V.a₁ * x = -V.a₃ := by rw [hxdef, mul_comm]; exact div_mul_cancel₀ _ ha1
      have hy : V.a₁ * y = 3 * x ^ 2 + 2 * V.a₂ * x + V.a₄ := by
        rw [hydef, mul_comm]; exact div_mul_cancel₀ _ ha1
      have hy3 : V.a₁ ^ 3 * y = 3 * V.a₃ ^ 2 - 2 * V.a₁ * V.a₂ * V.a₃ + V.a₁ ^ 2 * V.a₄ := by
        linear_combination V.a₁ ^ 2 * hy + (3 * (V.a₁ * x - V.a₃) + 2 * V.a₂ * V.a₁) * hx
      refine ⟨x, y, ?_, by rw [hy, sub_self], by linear_combination y * h2 + hx⟩
      have e2 : V.a₁ ^ 6 * (y ^ 2 + V.a₁ * x * y + V.a₃ * y - (x ^ 3 + V.a₂ * x ^ 2 + V.a₄ * x + V.a₆)) = 0 := by
        rw [show V.a₁ ^ 6 * (y ^ 2 + V.a₁ * x * y + V.a₃ * y - (x ^ 3 + V.a₂ * x ^ 2 + V.a₄ * x + V.a₆)) =
          (V.a₁ ^ 3 * y) ^ 2 + V.a₁ ^ 3 * (V.a₁ * x) * (V.a₁ ^ 3 * y) + V.a₁ ^ 3 * V.a₃ * (V.a₁ ^ 3 * y) -
            V.a₁ ^ 3 * (V.a₁ * x) ^ 3 - V.a₁ ^ 4 * V.a₂ * (V.a₁ * x) ^ 2 - V.a₁ ^ 5 * V.a₄ * (V.a₁ * x) -
            V.a₁ ^ 6 * V.a₆ by ring, hx, hy3]
        linear_combination hΔ - hD + ((216)*V.a₆^2 + (32)*V.a₄^3 + (108)*V.a₃^2*V.a₆ + (18)*V.a₃^4 +
          (-144)*V.a₂*V.a₄*V.a₆ + (-36)*V.a₂*V.a₃^2*V.a₄ + (-8)*V.a₂^2*V.a₄^2 + (32)*V.a₂^3*V.a₆ +
          (8)*V.a₂^3*V.a₃^2 + (48)*V.a₁*V.a₃*V.a₄^2 + (-72)*V.a₁*V.a₂*V.a₃*V.a₆ +
          (-24)*V.a₁*V.a₂*V.a₃^3 + (-8)*V.a₁*V.a₂^2*V.a₃*V.a₄ + (-36)*V.a₁^2*V.a₄*V.a₆ +
          (18)*V.a₁^2*V.a₃^2*V.a₄ + (-4)*V.a₁^2*V.a₂*V.a₄^2 + (24)*V.a₁^2*V.a₂^2*V.a₆ +
          (6)*V.a₁^2*V.a₂^2*V.a₃^2 + (-18)*V.a₁^3*V.a₃*V.a₆ + (-6)*V.a₁^3*V.a₂*V.a₃*V.a₄ +
          (6)*V.a₁^4*V.a₂*V.a₆) * h2
      rcases mul_eq_zero.mp e2 with h | h
      · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) ha1
      · exact sub_eq_zero.mp h
  · -- characteristic ≠ 2: a double root of the 2-torsion polynomial
    set ψ := V.twoTorsionPolynomial with hψ
    have h4 : (4 : K) ≠ 0 := by
      rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
    have ha : ψ.a ≠ 0 := h4
    obtain ⟨r1, r2, r3, h3⟩ := (Cubic.splits_iff_roots_eq_three (φ := RingHom.id K) ha).mp
      (IsAlgClosed.splits _)
    have hd := Cubic.discr_eq_prod_three_roots ha h3
    have hb := Cubic.b_eq_three_roots ha h3
    have hc := Cubic.c_eq_three_roots ha h3
    have hdd := Cubic.d_eq_three_roots ha h3
    rw [RingHom.id_apply, hψ, V.twoTorsionPolynomial_discr, hΔ, mul_zero] at hd
    simp only [RingHom.id_apply, hψ, WeierstrassCurve.twoTorsionPolynomial] at hd hb hc hdd
    have hprod : (r1 - r2) * (r1 - r3) * (r2 - r3) = 0 := by
      have h' := (pow_eq_zero_iff two_ne_zero).mp hd.symm
      have h'' : (4 * 4 : K) * ((r1 - r2) * (r1 - r3) * (r2 - r3)) = 0 := by linear_combination h'
      exact (mul_eq_zero.mp h'').resolve_left (mul_ne_zero h4 h4)
    have hroot : ∃ r : K, 4 * r ^ 3 + V.b₂ * r ^ 2 + 2 * V.b₄ * r + V.b₆ = 0 ∧
        12 * r ^ 2 + 2 * V.b₂ * r + 2 * V.b₄ = 0 := by
      rcases mul_eq_zero.mp hprod with h | h
      · rcases mul_eq_zero.mp h with h | h
        · obtain rfl := sub_eq_zero.mp h
          exact ⟨r1, by linear_combination r1 ^ 2 * hb + r1 * hc + hdd,
            by linear_combination 2 * r1 * hb + hc⟩
        · obtain rfl := sub_eq_zero.mp h
          exact ⟨r1, by linear_combination r1 ^ 2 * hb + r1 * hc + hdd,
            by linear_combination 2 * r1 * hb + hc⟩
      · obtain rfl := sub_eq_zero.mp h
        exact ⟨r2, by linear_combination r2 ^ 2 * hb + r2 * hc + hdd,
          by linear_combination 2 * r2 * hb + hc⟩
    obtain ⟨r, h0, h1⟩ := hroot
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at h0 h1
    set y := -(V.a₁ * r + V.a₃) / 2 with hydef
    have hy2 : 2 * y = -(V.a₁ * r + V.a₃) := by rw [hydef, mul_comm]; exact div_mul_cancel₀ _ h2
    refine ⟨r, y, ?_, ?_, by linear_combination hy2⟩
    · have e : (4 : K) * ((y ^ 2 + V.a₁ * r * y + V.a₃ * y) - (r ^ 3 + V.a₂ * r ^ 2 + V.a₄ * r + V.a₆)) = 0 := by
        linear_combination (2 * y + (V.a₁ * r + V.a₃)) * hy2 - h0
      exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left h4)
    · have e : (4 : K) * (V.a₁ * y - (3 * r ^ 2 + 2 * V.a₂ * r + V.a₄)) = 0 := by
        linear_combination 2 * V.a₁ * hy2 - h1
      exact (mul_eq_zero.mp e).resolve_left h4

end Singular

section QCurve

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable {G : AddSubgroup (Pt W L)} [Fintype G]

/-- `(X_G, Y_G)` lies on a Weierstrass curve over `L`. -/
theorem exists_qcurve (hG : (Fintype.card G : L) ≠ 0) :
    ∃ V : WeierstrassCurve L, (V.baseChange (FF W L)).toAffine.Equation (qx G) (qy G) := by
  obtain ⟨c₁, c₂, c₃, c₄, c₅, h⟩ := exists_curve (G := G) hG
  refine ⟨⟨-c₁, c₂, -c₃, c₄, c₅⟩, ?_⟩
  rw [equation_iff]
  show qy G ^ 2 + algebraMap L (FF W L) (-c₁) * qx G * qy G + algebraMap L (FF W L) (-c₃) * qy G =
    qx G ^ 3 + algebraMap L (FF W L) c₂ * qx G ^ 2 + algebraMap L (FF W L) c₄ * qx G +
      algebraMap L (FF W L) c₅
  rw [map_neg, map_neg]
  linear_combination h

/-- The quotient curve is unique. -/
theorem qcurve_unique {V V' : WeierstrassCurve L}
    (hV : (V.baseChange (FF W L)).toAffine.Equation (qx G) (qy G))
    (hV' : (V'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) : V = V' := by
  have e := (equation_iff _ _).mp hV
  have e' := (equation_iff _ _).mp hV'
  change qy G ^ 2 + algebraMap L (FF W L) V.a₁ * qx G * qy G + algebraMap L (FF W L) V.a₃ * qy G =
    qx G ^ 3 + algebraMap L (FF W L) V.a₂ * qx G ^ 2 + algebraMap L (FF W L) V.a₄ * qx G +
      algebraMap L (FF W L) V.a₆ at e
  change qy G ^ 2 + algebraMap L (FF W L) V'.a₁ * qx G * qy G + algebraMap L (FF W L) V'.a₃ * qy G =
    qx G ^ 3 + algebraMap L (FF W L) V'.a₂ * qx G ^ 2 + algebraMap L (FF W L) V'.a₄ * qx G +
      algebraMap L (FF W L) V'.a₆ at e'
  obtain ⟨h1, h2, h3, h4, h6⟩ := curve_coeff_unique (G := G) (c₁ := V.a₁ - V'.a₁) (c₂ := V'.a₂ - V.a₂)
    (c₃ := V.a₃ - V'.a₃) (c₄ := V'.a₄ - V.a₄) (c₅ := V'.a₆ - V.a₆)
    (by simp only [map_sub]; linear_combination e - e')
  ext
  · exact (sub_eq_zero.mp h1)
  · exact (sub_eq_zero.mp h2).symm
  · exact (sub_eq_zero.mp h3)
  · exact (sub_eq_zero.mp h4).symm
  · exact (sub_eq_zero.mp h6).symm

lemma ord_quad {s u A c : FF W L} {P : Pt W L} (hA : Ge 0 A P) (hc : Ge 0 c P) (hs0 : s ≠ 0)
    (hk : ord W L s P < 0) (h : u = s ^ 2 + A * s - c) : u ≠ 0 ∧ ord W L u P = 2 * ord W L s P := by
  have hs : Ge (ord W L s P) s P := Or.inr le_rfl
  have hr : Ge (2 * ord W L s P + 1) (A * s - c) P :=
    ((hA.mul hs).mono (by omega)).sub (hc.mono (by omega))
  have h2 : ord W L (s ^ 2) P = 2 * ord W L s P := by rw [ord_pow]; push_cast; ring
  rw [h, add_sub_assoc]
  exact ge_lead (pow_ne_zero 2 hs0) h2 hr

/-- **The quotient curve is nonsingular.** -/
theorem qcurve_Δ_ne_zero (hG : (Fintype.card G : L) ≠ 0) {V : WeierstrassCurve L}
    (hV : (V.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) : V.Δ ≠ 0 := by
  intro hΔ
  obtain ⟨x0, y0, hE, hns⟩ := exists_singular V hΔ
  have hE' := (V.toAffine.equation_iff x0 y0).mp hE
  have hX0 : V.a₁ * y0 - (3 * x0 ^ 2 + 2 * V.a₂ * x0 + V.a₄) = 0 := by
    by_contra h; exact hns ((V.toAffine.nonsingular_iff' x0 y0).mpr ⟨hE, Or.inl h⟩)
  have hY0 : 2 * y0 + V.a₁ * x0 + V.a₃ = 0 := by
    by_contra h; exact hns ((V.toAffine.nonsingular_iff' x0 y0).mpr ⟨hE, Or.inr h⟩)
  have e := (equation_iff _ _).mp hV
  change qy G ^ 2 + algebraMap L (FF W L) V.a₁ * qx G * qy G + algebraMap L (FF W L) V.a₃ * qy G =
    qx G ^ 3 + algebraMap L (FF W L) V.a₂ * qx G ^ 2 + algebraMap L (FF W L) V.a₄ * qx G +
      algebraMap L (FF W L) V.a₆ at e
  have hEF := congrArg (algebraMap L (FF W L)) hE'
  have hXF := congrArg (algebraMap L (FF W L)) hX0
  have hYF := congrArg (algebraMap L (FF W L)) hY0
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero] at hEF hXF hYF
  obtain ⟨hX0', hXo⟩ := ord_qx_zero (G := G)
  have hu := ge_lead hX0' hXo ((Ge.const x0 0).neg.mono (by norm_num))
  rw [← sub_eq_add_neg] at hu
  obtain ⟨hu0, huo⟩ := hu
  have hgu : GoodQ G (qx G - algebraMap L (FF W L) x0) := goodQ_qx.sub (GoodQ.const x0)
  have hgw : GoodQ G (qy G - algebraMap L (FF W L) y0) := goodQ_qy.sub (GoodQ.const y0)
  set A1 := algebraMap L (FF W L) V.a₁
  set A2 := algebraMap L (FF W L) V.a₂
  set X0 := algebraMap L (FF W L) x0
  set Y0 := algebraMap L (FF W L) y0
  set u := qx G - X0 with hudef
  set w := qy G - Y0 with hwdef
  have key : w ^ 2 + A1 * u * w = u ^ 3 + (3 * X0 + A2) * u ^ 2 := by
    rw [hudef, hwdef]; linear_combination e - hEF - (qx G - X0) * hXF - (qy G - Y0) * hYF
  set s := w / u with hsdef
  have hsu : s * u = w := div_mul_cancel₀ w hu0
  have hquad : u = s ^ 2 + A1 * s - (3 * X0 + A2) := by
    have h0 : u ^ 2 * (s ^ 2 + A1 * s - (3 * X0 + A2) - u) = 0 := by
      linear_combination key + (s * u + w + A1 * u) * hsu
    exact (sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left (pow_ne_zero 2 hu0))).symm
  have hA1 : ∀ P, Ge 0 A1 P := fun P => Ge.const _ P
  have hc : ∀ P, Ge 0 (3 * X0 + A2) P := fun P =>
    (((Ge.ofNat 3 P).mul (Ge.const x0 P)).mono (by norm_num)).add (Ge.const _ P)
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0] at hquad
    have : Ge 0 u 0 := by
      rw [hquad]
      exact ((((Ge.zero 0 0).pow 2).mono (by norm_num)).add (((hA1 0).mul (Ge.zero 0 0)).mono
        (by norm_num))).sub (hc 0)
    rcases this with h | h
    · exact hu0 h
    · omega
  have hgs : GoodQ G s := by
    refine ⟨fun S hS => by rw [hsdef, map_div₀, hgw.1 S hS, hgu.1 S hS], fun Q hQ => ?_⟩
    by_contra hneg
    have hk : ord W L s Q < 0 := by
      by_contra h; exact hneg (Or.inr (by omega))
    obtain ⟨-, h2⟩ := ord_quad (hA1 Q) (hc Q) hs0 hk hquad
    have := (hgu.2 Q hQ).resolve_left hu0
    omega
  have hk : ord W L s 0 < 0 := by
    by_contra h
    have hs0' : Ge 0 s 0 := Or.inr (by omega)
    have : Ge 0 u 0 := by
      rw [hquad]
      exact ((((hs0'.pow 2).mono (by norm_num)).add
        (((hA1 0).mul hs0').mono (by norm_num))).sub (hc 0))
    rcases this with h' | h'
    · exact hu0 h'
    · omega
  obtain ⟨-, h2⟩ := ord_quad (hA1 0) (hc 0) hs0 hk hquad
  exact hgs.ord_ne_neg_one hG hs0 (by omega)

end QCurve

end RPLib.DWS


