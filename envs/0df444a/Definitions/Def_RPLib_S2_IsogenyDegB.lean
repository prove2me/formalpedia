-- Prove2me | Definitions.Def_RPLib_S2_IsogenyDegB
-- name    : RPLib_S2_IsogenyDegB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:12:25.514735+00:00
-- url     : https://prove2.me/theorems/e86f0224-067d-4452-acda-719a65cbb839
-- title:
--   Degrees of $r + s\pi$, part B: the place formula
-- statement:
--   Two discrete valuations with the same valuation ring differ by a power; the pullback multiplies orders by a fixed ramification index $e \ge 1$: $\mathrm{ord}_P(\psi f) = e \cdot \mathrm{ord}_{\varphi P}(f)$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, doi:10.1007/978-0-387-09494-6, Section II.2

import Mathlib
import Definitions.Def_RPLib_S2_IsogenyDegA

/-!
# S2-IsogenyDeg part B: the place formula for `pull Φ`

* `exists_pow_of_le_one_iff` : two `ℤᵐ⁰` valuations with the same valuation ring differ by a power.
* `ord_comap` : if `ψ x ≡ x(Q)`, `ψ y ≡ y(Q)` at `P`, then `ord_P (ψ f) = e * ord_Q f` for a fixed `e ≥ 1`.
* `exists_place` : such a pair `(P0, Q0)` exists for `ψ = pull Φ`.
* `exists_pull'` : after a translation, `ord_P (ψ f) = e * ord_{φ P} f` for all `P`, and
  `τ_S ∘ ψ = ψ ∘ τ_{φ S}`.
-/

set_option autoImplicit false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate

namespace RPLib.Isog

open RPLib.Weil

/-- Two `ℤᵐ⁰`-valued valuations with the same valuation ring, the second attaining `exp (-1)`:
the first is a positive power of the second. -/
theorem exists_pow_of_le_one_iff {F : Type*} [Field F]
    (ν₁ ν₂ : Valuation F (WithZero (Multiplicative ℤ)))
    (h : ∀ f, ν₁ f ≤ 1 ↔ ν₂ f ≤ 1) {t : F} (ht : ν₂ t = WithZero.exp (-1)) :
    ∃ e : ℕ, 1 ≤ e ∧ ∀ x, x ≠ 0 → WithZero.log (ν₁ x) = e * WithZero.log (ν₂ x) := by
  have he : ν₁.IsEquiv ν₂ := Valuation.isEquiv_iff_val_le_one.mpr (h _)
  have heq1 : ∀ {x}, ν₁ x = 1 ↔ ν₂ x = 1 := Valuation.isEquiv_iff_val_eq_one.mp he
  have hlt1 : ∀ {x}, ν₁ x < 1 ↔ ν₂ x < 1 := Valuation.isEquiv_iff_val_lt_one.mp he
  have ht0 : t ≠ 0 := by rintro rfl; rw [map_zero] at ht; exact WithZero.exp_ne_zero ht.symm
  have hν₁t : ν₁ t ≠ 0 := (Valuation.ne_zero_iff _).mpr ht0
  obtain ⟨a, ha'⟩ : ∃ a : ℤ, ν₁ t = WithZero.exp a := ⟨_, (WithZero.exp_log hν₁t).symm⟩
  have ha : a < 0 := by
    have : ν₁ t < 1 := hlt1.mpr (by rw [ht, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)
    rwa [ha', ← WithZero.exp_zero, WithZero.exp_lt_exp] at this
  refine ⟨(-a).toNat, by omega, fun x hx => ?_⟩
  have hx1 : ν₁ x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have hx2 : ν₂ x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨n, hn⟩ : ∃ n : ℤ, ν₂ x = WithZero.exp n := ⟨_, (WithZero.exp_log hx2).symm⟩
  obtain ⟨m, hm⟩ : ∃ m : ℤ, ν₁ x = WithZero.exp m := ⟨_, (WithZero.exp_log hx1).symm⟩
  have h3 : ν₂ (x * t ^ n) = 1 := by
    rw [map_mul, map_zpow₀, ht, hn, ← WithZero.exp_zsmul, ← WithZero.exp_add, WithZero.exp_eq_one,
      smul_eq_mul]
    ring
  have h1 := heq1.mpr h3
  rw [map_mul, map_zpow₀, ha', hm, ← WithZero.exp_zsmul, ← WithZero.exp_add, WithZero.exp_eq_one,
    smul_eq_mul] at h1
  rw [hm, hn, WithZero.log_exp, WithZero.log_exp, Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -a)]
  linear_combination h1

section Place

variable {k : Type*} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra k L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

lemma HV_a₆' {P : Pt W L} {hP : P ≠ 0} :
    HV W L P hP (W.baseChange (FF W L)).toAffine.a₆ (W.baseChange L).toAffine.a₆ := by
  rw [bc_a₆ W L (FF W L)]; exact HV_alg _

lemma HV_eq_zero {P : Pt W L} {hP : P ≠ 0} {c : L} (h : HV W L P hP 0 c) : c = 0 := by
  by_contra hc; exact h.ne_zero hc rfl

lemma HV_of_nu_lt {P : Pt W L} {hP : P ≠ 0} {f : FF W L} (h : nu W L P hP f < 1) :
    HV W L P hP f 0 := by
  unfold HV; rwa [map_zero, sub_zero]

lemma ord_nonneg_of_nu_le {P : Pt W L} (hP : P ≠ 0) {f : FF W L} (hf : f ≠ 0)
    (h : nu W L P hP f ≤ 1) : 0 ≤ ord W L f P := by
  rw [ord_eq hP]
  have h0 : nu W L P hP f ≠ 0 := (Valuation.ne_zero_iff _).mpr hf
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
  omega

/-! ### Residues along an algebra map -/

/-- `r` has value `c` at `Q`, and `ψ r ≡ c` at `P`. -/
def GoodG (ψ : CR W L →ₐ[L] FF W L) (P Q : Pt W L) (hP : P ≠ 0) (hQ : Q ≠ 0) (r : CR W L) : Prop :=
  ∃ c : L, r - algebraMap L (CR W L) c ∈ (hosP W L Q hQ).asIdeal ∧ HV W L P hP (ψ r) c

section GoodG

variable {ψ : CR W L →ₐ[L] FF W L} {P Q : Pt W L} {hP : P ≠ 0} {hQ : Q ≠ 0}

lemma GoodG_add {r s : CR W L} (hr : GoodG ψ P Q hP hQ r) (hs : GoodG ψ P Q hP hQ s) :
    GoodG ψ P Q hP hQ (r + s) := by
  obtain ⟨c, hc, hc'⟩ := hr
  obtain ⟨d, hd, hd'⟩ := hs
  refine ⟨c + d, ?_, ?_⟩
  · rw [map_add, show r + s - (algebraMap L (CR W L) c + algebraMap L (CR W L) d) =
      (r - algebraMap L (CR W L) c) + (s - algebraMap L (CR W L) d) by ring]
    exact Ideal.add_mem _ hc hd
  · rw [map_add]; exact hc'.add hd'

lemma GoodG_mul {r s : CR W L} (hr : GoodG ψ P Q hP hQ r) (hs : GoodG ψ P Q hP hQ s) :
    GoodG ψ P Q hP hQ (r * s) := by
  obtain ⟨c, hc, hc'⟩ := hr
  obtain ⟨d, hd, hd'⟩ := hs
  refine ⟨c * d, ?_, ?_⟩
  · rw [map_mul, show r * s - algebraMap L (CR W L) c * algebraMap L (CR W L) d =
      (r - algebraMap L (CR W L) c) * s + algebraMap L (CR W L) c * (s - algebraMap L (CR W L) d) by
      ring]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hc) (Ideal.mul_mem_left _ _ hd)
  · rw [map_mul]; exact hc'.mul hd'

lemma GoodG_alg (a : L) : GoodG ψ P Q hP hQ (algebraMap L (CR W L) a) :=
  ⟨a, by rw [sub_self]; exact Ideal.zero_mem _, by rw [AlgHom.commutes]; exact HV_alg a⟩

lemma GoodG_pow {r : CR W L} (hr : GoodG ψ P Q hP hQ r) (n : ℕ) : GoodG ψ P Q hP hQ (r ^ n) := by
  induction n with
  | zero => rw [pow_zero, ← map_one (algebraMap L (CR W L))]; exact GoodG_alg 1
  | succ n ih => rw [pow_succ]; exact GoodG_mul ih hr

lemma GoodG.nu_eq_one {b : CR W L} (hg : GoodG ψ P Q hP hQ b) (hb : b ∉ (hosP W L Q hQ).asIdeal) :
    nu W L P hP (ψ b) = 1 := by
  obtain ⟨c, hc, hc'⟩ := hg
  refine hc'.nu_eq_one ?_
  rintro rfl
  apply hb; simpa using hc

lemma GoodG.nu_lt_one {a : CR W L} (hg : GoodG ψ P Q hP hQ a) (ha : a ∈ (hosP W L Q hQ).asIdeal) :
    nu W L P hP (ψ a) < 1 := by
  obtain ⟨c, hc, hc'⟩ := hg
  have hc0 : c = 0 := by
    by_contra hc0
    have hmem : algebraMap L (CR W L) c ∈ (hosP W L Q hQ).asIdeal := by
      have := Ideal.sub_mem _ ha hc
      rwa [sub_sub_cancel] at this
    exact (hosP W L Q hQ).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hmem ((IsUnit.mk0 c hc0).map _))
  subst hc0
  have := hc'
  unfold HV at this
  rwa [map_zero, sub_zero] at this

end GoodG

lemma GoodG_all (ψ : CR W L →ₐ[L] FF W L) {P Q : Pt W L} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hx : HV W L P hP (ψ (mk (W.baseChange L).toAffine (C X))) (px Q))
    (hy : HV W L P hP (ψ (mk (W.baseChange L).toAffine Y)) (py Q)) (r : CR W L) :
    GoodG ψ P Q hP hQ r := by
  have gX : GoodG ψ P Q hP hQ (mk (W.baseChange L).toAffine (C X)) := by
    refine ⟨px Q, ?_, hx⟩
    rw [algebraMap_Rg, ← map_sub, ← C_sub]
    exact XClass_mem_XYIdeal _ _ _
  have gY : GoodG ψ P Q hP hQ (mk (W.baseChange L).toAffine Y) := by
    refine ⟨py Q, ?_, hy⟩
    rw [algebraMap_Rg, ← map_sub]
    exact YClass_mem_XYIdeal _ _ _
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective r
  refine Polynomial.induction_on' p (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add]; exact GoodG_add hp hq
  · rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
    refine GoodG_mul ?_ (GoodG_pow gY n)
    refine Polynomial.induction_on' a (fun p q hp hq => ?_) (fun m b => ?_)
    · rw [map_add, map_add]; exact GoodG_add hp hq
    · rw [← C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow]
      exact GoodG_mul (GoodG_alg b) (GoodG_pow gX m)

/-- If `ψ x ≡ x(Q)` and `ψ y ≡ y(Q)` at `P`, then `ψ` maps the valuation ring at `Q` onto the one at `P`. -/
lemma nu_le_one_iff (ψ : FF W L →ₐ[L] FF W L) {P Q : Pt W L} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hx : HV W L P hP (ψ (gx W L)) (px Q)) (hy : HV W L P hP (ψ (gy W L)) (py Q)) (f : FF W L) :
    nu W L P hP (ψ f) ≤ 1 ↔ nu W L Q hQ f ≤ 1 := by
  have hG := GoodG_all (ψ.comp (IsScalarTower.toAlgHom L (CR W L) (FF W L))) hP hQ hx hy
  constructor
  · intro hf
    by_contra hQf
    push_neg at hQf
    have hf0 : f ≠ 0 := by
      rintro rfl; rw [map_zero] at hQf; exact (not_lt.mpr zero_le') hQf
    have hinv : nu W L Q hQ f⁻¹ ≤ 1 := ((Valuation.one_lt_val_iff _ hf0).mp hQf).le
    rw [nu_eq_valuation] at hinv
    obtain ⟨a, b, hb, hab⟩ := (valuation_le_one_iff_exists _ f⁻¹).mp hinv
    have hb1 : (hosP W L Q hQ).valuation (FF W L) (algebraMap (CR W L) (FF W L) b) = 1 :=
      le_antisymm (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _)
        (not_lt.mp (fun h' => hb
          ((IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ _).mp h')))
    have ha : a ∈ (hosP W L Q hQ).asIdeal := by
      refine (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := FF W L) _ a).mp ?_
      change (hosP W L Q hQ).valuation (FF W L) (algebraMap (CR W L) (FF W L) a) < 1
      rw [← hab, map_mul, hb1, mul_one]
      exact (Valuation.one_lt_val_iff _ hf0).mp hQf
    have h1 : nu W L P hP (ψ (algebraMap (CR W L) (FF W L) b)) = 1 := (hG b).nu_eq_one hb
    have h2 : nu W L P hP (ψ (algebraMap (CR W L) (FF W L) a)) < 1 := (hG a).nu_lt_one ha
    have h3 : nu W L P hP (ψ f⁻¹) < 1 := by
      calc nu W L P hP (ψ f⁻¹)
          = nu W L P hP (ψ f⁻¹) * nu W L P hP (ψ (algebraMap (CR W L) (FF W L) b)) := by
            rw [h1, mul_one]
        _ = nu W L P hP (ψ (algebraMap (CR W L) (FF W L) a)) := by
            rw [← Valuation.map_mul, ← map_mul ψ, hab]
        _ < 1 := h2
    have hψf : ψ f ≠ 0 := (_root_.map_ne_zero ψ).mpr hf0
    rw [map_inv₀] at h3
    exact (not_lt.mpr hf) ((Valuation.one_lt_val_iff _ hψf).mpr h3)
  · intro hf
    rw [nu_eq_valuation] at hf
    obtain ⟨a, b, hb, hab⟩ := (valuation_le_one_iff_exists _ f).mp hf
    have h1 : nu W L P hP (ψ (algebraMap (CR W L) (FF W L) b)) = 1 := (hG b).nu_eq_one hb
    obtain ⟨c, -, hc⟩ := hG a
    calc nu W L P hP (ψ f)
        = nu W L P hP (ψ f) * nu W L P hP (ψ (algebraMap (CR W L) (FF W L) b)) := by
          rw [h1, mul_one]
      _ = nu W L P hP (ψ (algebraMap (CR W L) (FF W L) a)) := by
          rw [← Valuation.map_mul, ← map_mul ψ, hab]
      _ ≤ 1 := hc.nu_le

/-- **Place formula at one point.** -/
theorem ord_comap (ψ : FF W L →ₐ[L] FF W L) {P Q : Pt W L} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hx : HV W L P hP (ψ (gx W L)) (px Q)) (hy : HV W L P hP (ψ (gy W L)) (py Q)) :
    ∃ e : ℕ, 1 ≤ e ∧ ∀ f, f ≠ 0 → ord W L (ψ f) P = e * ord W L f Q := by
  obtain ⟨t, ht⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer
    (K := FF W L) (v := hosP W L Q hQ)
  obtain ⟨e, he1, he⟩ := exists_pow_of_le_one_iff ((nu W L P hP).comap ψ.toRingHom) (nu W L Q hQ)
    (fun f => by rw [Valuation.comap_apply]; exact nu_le_one_iff ψ hP hQ hx hy f) (t := t) ht
  refine ⟨e, he1, fun f hf => ?_⟩
  have := he f hf
  rw [Valuation.comap_apply] at this
  rw [ord_eq hP, ord_eq hQ]
  change -WithZero.log (nu W L P hP (ψ.toRingHom f)) = _
  rw [this]; ring

/-- A function with `ν_P f ≤ 1` has a residue at `P`. -/
lemma exists_HV {P : Pt W L} (hP : P ≠ 0) {f : FF W L} (hf : nu W L P hP f ≤ 1) :
    ∃ c, HV W L P hP f c := by
  have hG := GoodG_all (IsScalarTower.toAlgHom L (CR W L) (FF W L)) hP hP
    (HV_gx W L P hP) (HV_gy W L P hP)
  rw [nu_eq_valuation] at hf
  obtain ⟨a, b, hb, hab⟩ := (valuation_le_one_iff_exists _ f).mp hf
  obtain ⟨ca, -, hca⟩ := hG a
  obtain ⟨cb, hcb, hcb'⟩ := hG b
  have hcb0 : cb ≠ 0 := by rintro rfl; apply hb; simpa using hcb
  refine ⟨ca / cb, ?_⟩
  have hb0 : algebraMap (CR W L) (FF W L) b ≠ 0 := hcb'.ne_zero hcb0
  refine (hca.div hcb' hcb0).congr ?_ rfl
  show algebraMap (CR W L) (FF W L) a / algebraMap (CR W L) (FF W L) b = f
  rw [← hab, mul_div_cancel_right₀ _ hb0]

/-- A nonzero function is regular at some affine point. -/
lemma exists_regular {f : FF W L} (hf : f ≠ 0) :
    ∃ (P : Pt W L) (hP : P ≠ 0), nu W L P hP f ≤ 1 := by
  let g : L → Pt W L := fun a => Point.some _ _
    (equation_iff_nonsingular.mp (exists_y_alg (W.baseChange L) a).choose_spec)
  have hg : Function.Injective g := fun a b hab => (Point.some.inj hab).1
  obtain ⟨P, ⟨a, rfl⟩, hP⟩ :=
    (Set.infinite_range_of_injective hg).exists_notMem_finite (ord_finite hf)
  exact ⟨g a, Point.some_ne_zero _,
    (nu_eq_one_of_ord (Point.some_ne_zero _) hf (Function.notMem_support.mp hP)).le⟩

/-- If `x(Φ)` is regular at `P`, so is `y(Φ)`. -/
lemma nu_py_le {Φ : (W.baseChange (FF W L)).toAffine.Point} (hΦ : Φ ≠ 0) {P : Pt W L}
    {hP : P ≠ 0} {c : L} (hc : HV W L P hP (px Φ) c) : nu W L P hP (py Φ) ≤ 1 := by
  by_contra hy
  push_neg at hy
  have hy0 : py Φ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hy; exact (not_lt.mpr zero_le') hy
  have hi : HV W L P hP (py Φ)⁻¹ 0 := HV_of_nu_lt ((Valuation.one_lt_val_iff _ hy0).mp hy)
  have e1 := (nonsingular_px_py hΦ).1
  rw [equation_iff] at e1
  have hE := ((((hc.pow 3).add (HV_a₂.mul (hc.pow 2))).add (HV_a₄.mul hc)).add HV_a₆').mul
    (hi.pow 2) |>.sub (((HV_a₁.mul hc).add HV_a₃).mul hi)
  have hyi : py Φ * (py Φ)⁻¹ = 1 := mul_inv_cancel₀ hy0
  have hE' : HV W L P hP 1 0 := by
    refine hE.congr ?_ (by ring)
    linear_combination (-((py Φ)⁻¹ ^ 2)) * e1 + (py Φ * (py Φ)⁻¹ + 1 +
      ((W.baseChange (FF W L)).toAffine.a₁ * px Φ + (W.baseChange (FF W L)).toAffine.a₃) *
        (py Φ)⁻¹) * hyi
  unfold HV at hE'
  rw [map_zero, sub_zero, map_one] at hE'
  exact lt_irrefl _ hE'

/-- The residue point of `Φ` at a point where `x(Φ)` is regular. -/
lemma exists_res {Φ : (W.baseChange (FF W L)).toAffine.Point} (hΦ : Φ ≠ 0) {P : Pt W L}
    (hP : P ≠ 0) (hx : nu W L P hP (px Φ) ≤ 1) :
    ∃ Q : Pt W L, Q ≠ 0 ∧ HV W L P hP (px Φ) (px Q) ∧ HV W L P hP (py Φ) (py Q) := by
  obtain ⟨c, hc⟩ := exists_HV hP hx
  obtain ⟨d, hd⟩ := exists_HV hP (nu_py_le hΦ hc)
  have e1 := (nonsingular_px_py hΦ).1
  rw [equation_iff] at e1
  have hE := (((hd.pow 2).add ((HV_a₁.mul hc).mul hd)).add (HV_a₃.mul hd)).sub
    ((((hc.pow 3).add (HV_a₂.mul (hc.pow 2))).add (HV_a₄.mul hc)).add HV_a₆')
  have h0 := HV_eq_zero (hE.congr (sub_eq_zero.mpr e1) rfl)
  have heq : (W.baseChange L).toAffine.Equation c d := by
    rw [equation_iff]; exact sub_eq_zero.mp h0
  exact ⟨Point.some c d (equation_iff_nonsingular.mp heq), Point.some_ne_zero _, hc, hd⟩

/-- **Place formula for `pull Φ` at one point** `P0` (with image `Q0`). -/
theorem exists_place (Φ : (W.baseChange (FF W L)).toAffine.Point) (h : ∀ C, Φ ≠ ιP W L C) :
    ∃ (P0 Q0 : Pt W L) (e : ℕ), 1 ≤ e ∧
      ∀ f, f ≠ 0 → ord W L (pull W L Φ h f) P0 = e * ord W L f Q0 := by
  have hΦ := ne_zero_of_ne_ιP W L h
  have hx0 : px Φ ≠ 0 := fun h0 =>
    transcendental_of_ne_ιP W L h (by rw [h0]; exact isAlgebraic_zero)
  obtain ⟨P0, hP0, hreg⟩ := exists_regular hx0
  obtain ⟨Q0, hQ0, hx, hy⟩ := exists_res hΦ hP0 hreg
  obtain ⟨e, he1, he⟩ := ord_comap (pull W L Φ h) hP0 hQ0
    (by rw [pull_gx]; exact hx) (by rw [pull_gy]; exact hy)
  exact ⟨P0, Q0, e, he1, he⟩

/-- **Global place formula.** -/
theorem ord_pull_global (Φ : (W.baseChange (FF W L)).toAffine.Point) (h : ∀ C, Φ ≠ ιP W L C)
    (φ : Pt W L →+ Pt W L)
    (hE : ∀ S, Point.map (W' := W.toAffine) ((tauHom W L S).restrictScalars k) Φ =
      Φ + ιP W L (φ S)) :
    ∃ (P0 Q0 : Pt W L) (e : ℕ), 1 ≤ e ∧
      ∀ f, f ≠ 0 → ∀ P, ord W L (pull W L Φ h f) P = e * ord W L f (Q0 + φ (P - P0)) := by
  obtain ⟨P0, Q0, e, he1, he⟩ := exists_place Φ h
  refine ⟨P0, Q0, e, he1, fun f hf P => ?_⟩
  have h1 := ord_tau (P - P0) (pull W L Φ h f) P0
  have e0 : P0 + (P - P0) = P := by abel
  rw [e0] at h1
  rw [← h1, tau_pull W L Φ h φ hE, he _ (tau_ne_zero _ hf), ord_tau]

/-- A nonconstant function has a pole. -/
lemma exists_pole {f : FF W L} (hf : f ≠ 0) (hc : ∀ c : L, f ≠ algebraMap L (FF W L) c) :
    ∃ P, ord W L f P < 0 := by
  by_contra hneg
  push_neg at hneg
  have hfin := ord_finite hf
  have hsum := sum_ord_eq_zero hf hfin.toFinset (fun P hP => hfin.mem_toFinset.mpr hP)
  have hall : ∀ P, ord W L f P = 0 := by
    intro P
    by_cases hP : P ∈ hfin.toFinset
    · exact (Finset.sum_eq_zero_iff_of_nonneg (fun Q _ => hneg Q)).mp hsum P hP
    · exact Function.notMem_support.mp (fun h' => hP (hfin.mem_toFinset.mpr h'))
  obtain ⟨c, -, hc'⟩ := exists_const_of_ord hf (fun P _ => hall P)
  exact hc c hc'

/-- **Normalised pullback** `ψ = τ_{P2} ∘ pull Φ`: `ord_P (ψ f) = e * ord_{φ P} f` and
`τ_S ∘ ψ = ψ ∘ τ_{φ S}`. -/
theorem exists_pull' (Φ : (W.baseChange (FF W L)).toAffine.Point) (h : ∀ C, Φ ≠ ιP W L C)
    (φ : Pt W L →+ Pt W L)
    (hE : ∀ S, Point.map (W' := W.toAffine) ((tauHom W L S).restrictScalars k) Φ =
      Φ + ιP W L (φ S)) :
    ∃ (ψ : FF W L →ₐ[L] FF W L) (e : ℕ), 1 ≤ e ∧ Function.Injective ψ ∧
      (∀ f, f ≠ 0 → ∀ P, ord W L (ψ f) P = e * ord W L f (φ P)) ∧
      (∀ S f, tau W L S (ψ f) = ψ (tau W L (φ S) f)) := by
  obtain ⟨P0, Q0, e, he1, he⟩ := ord_pull_global Φ h φ hE
  have hgx0 : gx W L ≠ 0 := by have := gx_ne W L 0; rwa [map_zero] at this
  have hnc : ∀ c : L, pull W L Φ h (gx W L) ≠ algebraMap L (FF W L) c := by
    intro c hc
    rw [← (pull W L Φ h).commutes c] at hc
    exact gx_ne W L c (pull_injective W L Φ h hc)
  obtain ⟨P2, hP2⟩ := exists_pole ((_root_.map_ne_zero _).mpr hgx0) hnc
  have hz : Q0 + φ (P2 - P0) = 0 := by
    by_contra hQ
    rw [he _ hgx0] at hP2
    have h1 := ord_nonneg_of_nu_le hQ hgx0 (HV_gx W L _ hQ).nu_le
    have h2 : (0 : ℤ) ≤ e * ord W L (gx W L) (Q0 + φ (P2 - P0)) := mul_nonneg (by positivity) h1
    exact absurd hP2 (not_lt.mpr h2)
  refine ⟨(tau W L P2).toAlgHom.comp (pull W L Φ h), e, he1,
    ((tau W L P2).toAlgHom.comp (pull W L Φ h)).toRingHom.injective, ?_, ?_⟩
  · intro f hf P
    show ord W L (tau W L P2 (pull W L Φ h f)) P = _
    rw [ord_tau, he f hf, show Q0 + φ (P + P2 - P0) = φ P by
      rw [show P + P2 - P0 = (P2 - P0) + P by abel, map_add, ← add_assoc, hz, zero_add]]
  · intro S f
    show tau W L S (tau W L P2 (pull W L Φ h f)) = tau W L P2 (pull W L Φ h (tau W L (φ S) f))
    rw [← tau_pull W L Φ h φ hE, ← tau_add_apply, ← tau_add_apply, add_comm]

end Place

end RPLib.Isog


