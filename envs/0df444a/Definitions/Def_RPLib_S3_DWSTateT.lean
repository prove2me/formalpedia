-- Prove2me | Definitions.Def_RPLib_S3_DWSTateT
-- name    : RPLib_S3_DWSTateT
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:04:51.81163+00:00
-- url     : https://prove2.me/theorems/effc7ab3-b331-4ba8-8837-35da8bd8fea1
-- title:
--   Weight-two Ramanujan-Petersson library: the place formula for an algebra map between the function fields of two curves
-- statement:
--   The place formula for an algebra map between the function fields of two curves.
--
--   `ψ : L(E') →ₐ[L] L(E)` (two different curves over the same finite field). Copy of S2 `IsogenyDegB` with the domain
--   curve `W'` distinct from the codomain curve `W`.
--
--   * `GoodG2`, `GoodG2_all` : residues along `ψ`.
--   * `nu_le_one_iff2` : `ψ` maps the valuation ring at `Q ∈ E'` onto the one at `P ∈ E`.
--   * **`ord_comap2`** : `ord_P (ψ f) = e * ord_Q f` for a fixed `e ≥ 1`.
--   * `nu_py_le2`, `exists_res2` : the residue point of `Φ ∈ W'(L(E))` at a point where `x(Φ)` is regular.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSIsogO

/-!
# S3-DWS-Tate, part T: the place formula for an algebra map between the function fields of two curves

`ψ : L(E') →ₐ[L] L(E)` (two different curves over the same finite field). Copy of S2 `IsogenyDegB` with the domain
curve `W'` distinct from the codomain curve `W`.

* `GoodG2`, `GoodG2_all` : residues along `ψ`.
* `nu_le_one_iff2` : `ψ` maps the valuation ring at `Q ∈ E'` onto the one at `P ∈ E`.
* **`ord_comap2`** : `ord_P (ψ f) = e * ord_Q f` for a fixed `e ≥ 1`.
* `nu_py_le2`, `exists_res2` : the residue point of `Φ ∈ W'(L(E))` at a point where `x(Φ)` is regular.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section Place2

variable {F : Type*} [Field F] [Fintype F] {W W' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

/-- `r` (on `E'`) has value `c` at `Q`, and `ψ r ≡ c` at `P` (on `E`). -/
def GoodG2 (ψ : CR W' L →ₐ[L] FF W L) (P : Pt W L) (Q : Pt W' L) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (r : CR W' L) : Prop :=
  ∃ c : L, r - algebraMap L (CR W' L) c ∈ (hosP W' L Q hQ).asIdeal ∧ HV W L P hP (ψ r) c

section GoodG2

variable {ψ : CR W' L →ₐ[L] FF W L} {P : Pt W L} {Q : Pt W' L} {hP : P ≠ 0} {hQ : Q ≠ 0}

lemma GoodG2_add {r s : CR W' L} (hr : GoodG2 ψ P Q hP hQ r) (hs : GoodG2 ψ P Q hP hQ s) :
    GoodG2 ψ P Q hP hQ (r + s) := by
  obtain ⟨c, hc, hc'⟩ := hr
  obtain ⟨d, hd, hd'⟩ := hs
  refine ⟨c + d, ?_, ?_⟩
  · rw [map_add, show r + s - (algebraMap L (CR W' L) c + algebraMap L (CR W' L) d) =
      (r - algebraMap L (CR W' L) c) + (s - algebraMap L (CR W' L) d) by ring]
    exact Ideal.add_mem _ hc hd
  · rw [map_add]; exact hc'.add hd'

lemma GoodG2_mul {r s : CR W' L} (hr : GoodG2 ψ P Q hP hQ r) (hs : GoodG2 ψ P Q hP hQ s) :
    GoodG2 ψ P Q hP hQ (r * s) := by
  obtain ⟨c, hc, hc'⟩ := hr
  obtain ⟨d, hd, hd'⟩ := hs
  refine ⟨c * d, ?_, ?_⟩
  · rw [map_mul, show r * s - algebraMap L (CR W' L) c * algebraMap L (CR W' L) d =
      (r - algebraMap L (CR W' L) c) * s + algebraMap L (CR W' L) c * (s - algebraMap L (CR W' L) d) by
      ring]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hc) (Ideal.mul_mem_left _ _ hd)
  · rw [map_mul]; exact hc'.mul hd'

lemma GoodG2_alg (a : L) : GoodG2 ψ P Q hP hQ (algebraMap L (CR W' L) a) :=
  ⟨a, by rw [sub_self]; exact Ideal.zero_mem _, by rw [AlgHom.commutes]; exact HV_alg a⟩

lemma GoodG2_pow {r : CR W' L} (hr : GoodG2 ψ P Q hP hQ r) (n : ℕ) : GoodG2 ψ P Q hP hQ (r ^ n) := by
  induction n with
  | zero => rw [pow_zero, ← map_one (algebraMap L (CR W' L))]; exact GoodG2_alg 1
  | succ n ih => rw [pow_succ]; exact GoodG2_mul ih hr

lemma GoodG2.nu_eq_one {b : CR W' L} (hg : GoodG2 ψ P Q hP hQ b) (hb : b ∉ (hosP W' L Q hQ).asIdeal) :
    nu W L P hP (ψ b) = 1 := by
  obtain ⟨c, hc, hc'⟩ := hg
  refine hc'.nu_eq_one ?_
  rintro rfl
  apply hb; simpa using hc

lemma GoodG2.nu_lt_one {a : CR W' L} (hg : GoodG2 ψ P Q hP hQ a) (ha : a ∈ (hosP W' L Q hQ).asIdeal) :
    nu W L P hP (ψ a) < 1 := by
  obtain ⟨c, hc, hc'⟩ := hg
  have hc0 : c = 0 := by
    by_contra hc0
    have hmem : algebraMap L (CR W' L) c ∈ (hosP W' L Q hQ).asIdeal := by
      have := Ideal.sub_mem _ ha hc
      rwa [sub_sub_cancel] at this
    exact (hosP W' L Q hQ).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hmem ((IsUnit.mk0 c hc0).map _))
  subst hc0
  have := hc'
  unfold HV at this
  rwa [map_zero, sub_zero] at this

end GoodG2

lemma GoodG2_all (ψ : CR W' L →ₐ[L] FF W L) {P : Pt W L} {Q : Pt W' L} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hx : HV W L P hP (ψ (mk (W'.baseChange L).toAffine (C X))) (px Q))
    (hy : HV W L P hP (ψ (mk (W'.baseChange L).toAffine Y)) (py Q)) (r : CR W' L) :
    GoodG2 ψ P Q hP hQ r := by
  have gX : GoodG2 ψ P Q hP hQ (mk (W'.baseChange L).toAffine (C X)) := by
    refine ⟨px Q, ?_, hx⟩
    rw [algebraMap_Rg, ← map_sub, ← C_sub]
    exact XClass_mem_XYIdeal _ _ _
  have gY : GoodG2 ψ P Q hP hQ (mk (W'.baseChange L).toAffine Y) := by
    refine ⟨py Q, ?_, hy⟩
    rw [algebraMap_Rg, ← map_sub]
    exact YClass_mem_XYIdeal _ _ _
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective r
  refine Polynomial.induction_on' p (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add]; exact GoodG2_add hp hq
  · rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
    refine GoodG2_mul ?_ (GoodG2_pow gY n)
    refine Polynomial.induction_on' a (fun p q hp hq => ?_) (fun m b => ?_)
    · rw [map_add, map_add]; exact GoodG2_add hp hq
    · rw [← C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow]
      exact GoodG2_mul (GoodG2_alg b) (GoodG2_pow gX m)

/-- If `ψ x' ≡ x(Q)` and `ψ y' ≡ y(Q)` at `P`, then `ψ` maps the valuation ring at `Q` onto the one at `P`. -/
lemma nu_le_one_iff2 (ψ : FF W' L →ₐ[L] FF W L) {P : Pt W L} {Q : Pt W' L} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hx : HV W L P hP (ψ (gx W' L)) (px Q)) (hy : HV W L P hP (ψ (gy W' L)) (py Q)) (f : FF W' L) :
    nu W L P hP (ψ f) ≤ 1 ↔ nu W' L Q hQ f ≤ 1 := by
  have hG := GoodG2_all (ψ.comp (IsScalarTower.toAlgHom L (CR W' L) (FF W' L))) hP hQ hx hy
  constructor
  · intro hf
    by_contra hQf
    push_neg at hQf
    have hf0 : f ≠ 0 := by
      rintro rfl; rw [map_zero] at hQf; exact (not_lt.mpr zero_le') hQf
    have hinv : nu W' L Q hQ f⁻¹ ≤ 1 := ((Valuation.one_lt_val_iff _ hf0).mp hQf).le
    rw [nu_eq_valuation] at hinv
    obtain ⟨a, b, hb, hab⟩ := (valuation_le_one_iff_exists _ f⁻¹).mp hinv
    have hb1 : (hosP W' L Q hQ).valuation (FF W' L) (algebraMap (CR W' L) (FF W' L) b) = 1 :=
      le_antisymm (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _)
        (not_lt.mp (fun h' => hb
          ((IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ _).mp h')))
    have ha : a ∈ (hosP W' L Q hQ).asIdeal := by
      refine (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := FF W' L) _ a).mp ?_
      change (hosP W' L Q hQ).valuation (FF W' L) (algebraMap (CR W' L) (FF W' L) a) < 1
      rw [← hab, map_mul, hb1, mul_one]
      exact (Valuation.one_lt_val_iff _ hf0).mp hQf
    have h1 : nu W L P hP (ψ (algebraMap (CR W' L) (FF W' L) b)) = 1 := (hG b).nu_eq_one hb
    have h2 : nu W L P hP (ψ (algebraMap (CR W' L) (FF W' L) a)) < 1 := (hG a).nu_lt_one ha
    have h3 : nu W L P hP (ψ f⁻¹) < 1 := by
      calc nu W L P hP (ψ f⁻¹)
          = nu W L P hP (ψ f⁻¹) * nu W L P hP (ψ (algebraMap (CR W' L) (FF W' L) b)) := by
            rw [h1, mul_one]
        _ = nu W L P hP (ψ (algebraMap (CR W' L) (FF W' L) a)) := by
            rw [← Valuation.map_mul, ← map_mul ψ, hab]
        _ < 1 := h2
    have hψf : ψ f ≠ 0 := (_root_.map_ne_zero ψ).mpr hf0
    rw [map_inv₀] at h3
    exact (not_lt.mpr hf) ((Valuation.one_lt_val_iff _ hψf).mpr h3)
  · intro hf
    rw [nu_eq_valuation] at hf
    obtain ⟨a, b, hb, hab⟩ := (valuation_le_one_iff_exists _ f).mp hf
    have h1 : nu W L P hP (ψ (algebraMap (CR W' L) (FF W' L) b)) = 1 := (hG b).nu_eq_one hb
    obtain ⟨c, -, hc⟩ := hG a
    calc nu W L P hP (ψ f)
        = nu W L P hP (ψ f) * nu W L P hP (ψ (algebraMap (CR W' L) (FF W' L) b)) := by
          rw [h1, mul_one]
      _ = nu W L P hP (ψ (algebraMap (CR W' L) (FF W' L) a)) := by
          rw [← Valuation.map_mul, ← map_mul ψ, hab]
      _ ≤ 1 := hc.nu_le

/-- **Two-curve place formula at one point.** -/
theorem ord_comap2 (ψ : FF W' L →ₐ[L] FF W L) {P : Pt W L} {Q : Pt W' L} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hx : HV W L P hP (ψ (gx W' L)) (px Q)) (hy : HV W L P hP (ψ (gy W' L)) (py Q)) :
    ∃ e : ℕ, 1 ≤ e ∧ ∀ f, f ≠ 0 → ord W L (ψ f) P = e * ord W' L f Q := by
  obtain ⟨t, ht⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer
    (K := FF W' L) (v := hosP W' L Q hQ)
  obtain ⟨e, he1, he⟩ := exists_pow_of_le_one_iff ((nu W L P hP).comap ψ.toRingHom) (nu W' L Q hQ)
    (fun f => by rw [Valuation.comap_apply]; exact nu_le_one_iff2 ψ hP hQ hx hy f) (t := t) ht
  refine ⟨e, he1, fun f hf => ?_⟩
  have := he f hf
  rw [Valuation.comap_apply] at this
  rw [ord_eq hP, ord_eq hQ]
  change -WithZero.log (nu W L P hP (ψ.toRingHom f)) = _
  rw [this]; ring

/-- If `x(Φ)` is regular at `P`, so is `y(Φ)` (`Φ ∈ W'(L(E))`). -/
lemma nu_py_le2 {Φ : (W'.baseChange (FF W L)).toAffine.Point} (hΦ : Φ ≠ 0) {P : Pt W L}
    {hP : P ≠ 0} {c : L} (hc : HV W L P hP (px Φ) c) : nu W L P hP (py Φ) ≤ 1 := by
  by_contra hy
  push_neg at hy
  have hy0 : py Φ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hy; exact (not_lt.mpr zero_le') hy
  have hi : HV W L P hP (py Φ)⁻¹ 0 := HV_of_nu_lt ((Valuation.one_lt_val_iff _ hy0).mp hy)
  have e1 := eqn_FF (nonsingular_px_py hΦ).1
  have hE := ((((hc.pow 3).add ((HV_alg (W'.baseChange L).toAffine.a₂).mul (hc.pow 2))).add
    ((HV_alg (W'.baseChange L).toAffine.a₄).mul hc)).add (HV_alg (W'.baseChange L).toAffine.a₆)).mul
    (hi.pow 2) |>.sub ((((HV_alg (W'.baseChange L).toAffine.a₁).mul hc).add
      (HV_alg (W'.baseChange L).toAffine.a₃)).mul hi)
  have hyi : py Φ * (py Φ)⁻¹ = 1 := mul_inv_cancel₀ hy0
  have hE' : HV W L P hP 1 0 := by
    refine hE.congr ?_ (by ring)
    linear_combination (-((py Φ)⁻¹ ^ 2)) * e1 + (py Φ * (py Φ)⁻¹ + 1 +
      (algebraMap L (FF W L) (W'.baseChange L).toAffine.a₁ * px Φ +
        algebraMap L (FF W L) (W'.baseChange L).toAffine.a₃) * (py Φ)⁻¹) * hyi
  unfold HV at hE'
  rw [map_zero, sub_zero, map_one] at hE'
  exact lt_irrefl _ hE'

/-- The residue point (on `E'`) of `Φ ∈ W'(L(E))` at a point `P ∈ E` where `x(Φ)` is regular. -/
lemma exists_res2 {Φ : (W'.baseChange (FF W L)).toAffine.Point} (hΦ : Φ ≠ 0) {P : Pt W L}
    (hP : P ≠ 0) (hx : nu W L P hP (px Φ) ≤ 1) :
    ∃ Q : Pt W' L, Q ≠ 0 ∧ HV W L P hP (px Φ) (px Q) ∧ HV W L P hP (py Φ) (py Q) := by
  obtain ⟨c, hc⟩ := exists_HV hP hx
  obtain ⟨d, hd⟩ := exists_HV hP (nu_py_le2 hΦ hc)
  have e1 := eqn_FF (nonsingular_px_py hΦ).1
  have hE := (((hd.pow 2).add (((HV_alg (W'.baseChange L).toAffine.a₁).mul hc).mul hd)).add
    ((HV_alg (W'.baseChange L).toAffine.a₃).mul hd)).sub
    ((((hc.pow 3).add ((HV_alg (W'.baseChange L).toAffine.a₂).mul (hc.pow 2))).add
      ((HV_alg (W'.baseChange L).toAffine.a₄).mul hc)).add (HV_alg (W'.baseChange L).toAffine.a₆))
  have h0 := HV_eq_zero (hE.congr (sub_eq_zero.mpr e1) rfl)
  have heq : (W'.baseChange L).toAffine.Equation c d := by
    rw [equation_iff]; exact sub_eq_zero.mp h0
  exact ⟨Point.some c d (equation_iff_nonsingular.mp heq), Point.some_ne_zero _, hc, hd⟩

/-- **Place formula for an algebra map at a regular point.** If `ψ x'` is regular at the affine point `P`, there is
an affine `Q ∈ E'` with `ψ x' ≡ x(Q)`, `ψ y' ≡ y(Q)` at `P` and `ord_P (ψ f) = e * ord_Q f`. -/
theorem exists_place2 (ψ : FF W' L →ₐ[L] FF W L) {P : Pt W L} (hP : P ≠ 0)
    (hx : nu W L P hP (ψ (gx W' L)) ≤ 1) :
    ∃ Q : Pt W' L, ∃ hQ : Q ≠ 0, HV W L P hP (ψ (gx W' L)) (px Q) ∧ HV W L P hP (ψ (gy W' L)) (py Q) ∧
      ∃ e : ℕ, 1 ≤ e ∧ ∀ f, f ≠ 0 → ord W L (ψ f) P = e * ord W' L f Q := by
  set Φ := Point.map (W' := W'.toAffine) (ψ.restrictScalars F) (G W' L) with hΦdef
  have hΦ : Φ ≠ 0 := by rw [hΦdef, G, Point.map_some]; exact Point.some_ne_zero _
  have hpx : px Φ = ψ (gx W' L) := by rw [hΦdef, px_map]; rfl
  have hpy : py Φ = ψ (gy W' L) := by rw [hΦdef, py_map]; rfl
  obtain ⟨Q, hQ, hqx, hqy⟩ := exists_res2 hΦ hP (by rw [hpx]; exact hx)
  rw [hpx] at hqx
  rw [hpy] at hqy
  exact ⟨Q, hQ, hqx, hqy, ord_comap2 ψ hP hQ hqx hqy⟩

end Place2

end RPLib.DWS


