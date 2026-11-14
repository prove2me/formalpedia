-- Prove2me | Definitions.Def_RPLib_S2_WeilPairingA
-- name    : RPLib_S2_WeilPairingA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T18:50:46.731192+00:00
-- url     : https://prove2.me/theorems/72746dc8-b5c8-44b9-82c3-334080d2f8c6
-- title:
--   Weil pairing, part A: the coordinate ring is Dedekind with point ideals
-- statement:
--   For an elliptic curve over an algebraically closed field, the affine coordinate ring is a Dedekind domain whose maximal ideals are exactly the ideals $(X - x, Y - y)$ of affine points.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, doi:10.1007/978-0-387-09494-6, Section II.1 and III.3

import Mathlib

/-!
# S2-WeilPairing part A1: the coordinate ring of an elliptic curve over an algebraically closed
field is a Dedekind domain whose maximal ideals are the point ideals `⟨X - x, Y - y⟩`.
-/

set_option autoImplicit false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsLocalRing

namespace RPLib.Weil

/-- In a local domain, if `m * J = (t)` with `t ≠ 0`, then the maximal ideal `m` is principal. -/
theorem maximalIdeal_isPrincipal_of_mul {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    {J : Ideal A} {t : A} (ht : t ≠ 0) (h : maximalIdeal A * J = Ideal.span {t}) :
    (maximalIdeal A).IsPrincipal := by
  by_cases hle : maximalIdeal A * J ≤ Ideal.span {t} * maximalIdeal A
  · exfalso
    have hmem : t ∈ Ideal.span {t} * maximalIdeal A :=
      hle (h ▸ Ideal.mem_span_singleton_self t)
    obtain ⟨μ, hμ, hμt⟩ := Ideal.mem_span_singleton_mul.mp hmem
    have h1 : t * (1 - μ) = 0 := by rw [mul_sub, mul_one, hμt, sub_self]
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact ht h2
    · have h3 : (1 : A) = μ := sub_eq_zero.mp h2
      rw [← h3] at hμ
      exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr hμ)
  · rw [Ideal.mul_le] at hle
    push Not at hle
    obtain ⟨x, hx, j, hj, hxj⟩ := hle
    have hxj' : x * j ∈ Ideal.span {t} := h ▸ Ideal.mul_mem_mul hx hj
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hxj'
    have hru : IsUnit r := by
      by_contra hr'
      apply hxj
      rw [← hr, mul_comm r t]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self t) ((mem_maximalIdeal r).mpr hr')
    refine ⟨⟨x, le_antisymm (fun y hy => ?_) ((Submodule.span_singleton_le_iff_mem x _).mpr hx)⟩⟩
    have hyj : y * j ∈ Ideal.span {t} := h ▸ Ideal.mul_mem_mul hy hj
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hyj
    have key : t * (y * r - x * s) = 0 := by linear_combination y * hr - x * hs
    have hyr : y * r = x * s := by
      rcases mul_eq_zero.mp key with h0 | h0
      · exact absurd h0 ht
      · exact sub_eq_zero.mp h0
    refine Submodule.mem_span_singleton.mpr ⟨s * ↑hru.unit⁻¹, ?_⟩
    calc (s * ↑hru.unit⁻¹) • x = (y * r) * ↑hru.unit⁻¹ := by rw [smul_eq_mul, hyr]; ring
      _ = y := by rw [mul_assoc, hru.mul_val_inv, mul_one]

section Dedekind

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

/-- The coordinate ring is a finite `K[X]`-module (basis `1, Y`). -/
theorem finite_coordinateRing : Module.Finite K[X] W.toAffine.CoordinateRing :=
  .of_basis (CoordinateRing.basis W.toAffine)

attribute [local instance] finite_coordinateRing

theorem isNoetherianRing_coordinateRing : IsNoetherianRing W.toAffine.CoordinateRing :=
  IsNoetherianRing.of_finite K[X] _

/-- Over an algebraically closed field every maximal ideal of `K[X]` contains some `X - a`. -/
theorem exists_X_sub_C_mem [IsAlgClosed K] (p : Ideal K[X]) [hp : p.IsMaximal] :
    ∃ a : K, X - C a ∈ p := by
  obtain ⟨f, hf⟩ := Submodule.IsPrincipal.principal p
  have hf0 : f ≠ 0 := by
    rintro rfl
    have hbot : p = ⊥ := by rw [hf]; exact Submodule.span_singleton_eq_bot.mpr rfl
    exact (Ideal.bot_lt_of_maximal p (Polynomial.not_isField K)).ne' hbot
  have hprime : Prime f := (Ideal.span_singleton_prime hf0).mp (by
    have := hp.isPrime; rw [hf] at this; exact this)
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root f (degree_pos_of_irreducible hprime.irreducible).ne'
  refine ⟨a, ?_⟩
  obtain ⟨g, hg⟩ := dvd_iff_isRoot.mpr ha
  rcases hprime.irreducible.isUnit_or_isUnit hg with h | h
  · exact absurd h (Polynomial.not_isUnit_X_sub_C a)
  · have : X - C a = f * ((h.unit⁻¹ : K[X]ˣ) : K[X]) := by
      rw [hg, mul_assoc, h.mul_val_inv, mul_one]
    rw [this, hf]
    exact Ideal.mul_mem_right _ _ (Submodule.mem_span_singleton_self f)

end Dedekind


section Points

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

attribute [local instance] finite_coordinateRing

lemma algebraMap_X_sub_C (a : K) :
    algebraMap K[X] W.toAffine.CoordinateRing (X - C a) = XClass W.toAffine a := rfl

theorem exists_y_alg [IsAlgClosed K] (a : K) : ∃ b : K, W.toAffine.Equation a b := by
  have hdeg : (X ^ 2 + C (W.a₁ * a + W.a₃) * X -
      C (a ^ 3 + W.a₂ * a ^ 2 + W.a₄ * a + W.a₆) : K[X]).degree = 2 := by
    compute_degree!
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_root (X ^ 2 + C (W.a₁ * a + W.a₃) * X -
      C (a ^ 3 + W.a₂ * a ^ 2 + W.a₄ * a + W.a₆) : K[X]) (by rw [hdeg]; norm_num)
  refine ⟨b, ?_⟩
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [IsRoot, eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X] at hb
  linear_combination hb

theorem isMaximal_XYIdeal {x y : K} (h : W.toAffine.Equation x y) :
    (XYIdeal W.toAffine x (C y)).IsMaximal := by
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact MulEquiv.isField (Field.toIsField K) (quotientXYIdealEquiv h).toMulEquiv

theorem XClass_mem_XYIdeal (x : K) (y : K[X]) :
    XClass W.toAffine x ∈ XYIdeal W.toAffine x y :=
  Ideal.subset_span (Set.mem_insert _ _)

theorem YClass_mem_XYIdeal (x : K) (y : K[X]) :
    YClass W.toAffine y ∈ XYIdeal W.toAffine x y :=
  Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

/-- Every maximal ideal of the coordinate ring is the ideal of an affine point. -/
theorem exists_eq_XYIdeal [IsAlgClosed K] [W.IsElliptic] (q : Ideal W.toAffine.CoordinateRing)
    [hq : q.IsMaximal] :
    ∃ x y : K, ∃ _ : W.toAffine.Nonsingular x y, q = XYIdeal W.toAffine x (C y) := by
  haveI : Algebra.IsIntegral K[X] W.toAffine.CoordinateRing := Algebra.IsIntegral.of_finite _ _
  haveI : (q.comap (algebraMap K[X] W.toAffine.CoordinateRing)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q
  obtain ⟨a, ha⟩ := exists_X_sub_C_mem (q.comap (algebraMap K[X] W.toAffine.CoordinateRing))
  rw [Ideal.mem_comap, algebraMap_X_sub_C] at ha
  obtain ⟨b, hb⟩ := exists_y_alg W a
  have hns : W.toAffine.Nonsingular a b := WeierstrassCurve.Affine.equation_iff_nonsingular.mp hb
  have hX : XIdeal W.toAffine a ≤ q := (Ideal.span_singleton_le_iff_mem q).mpr ha
  rw [← XYIdeal_neg_mul hns] at hX
  rcases hq.isPrime.mul_le.mp hX with h1 | h1
  · have hns' : W.toAffine.Nonsingular a (W.toAffine.negY a b) :=
      (WeierstrassCurve.Affine.nonsingular_neg ..).mpr hns
    exact ⟨a, _, hns', ((isMaximal_XYIdeal W hns'.1).eq_of_le hq.ne_top h1).symm⟩
  · exact ⟨a, b, hns, ((isMaximal_XYIdeal W hns.1).eq_of_le hq.ne_top h1).symm⟩

theorem isDVR_localization [IsAlgClosed K] [W.IsElliptic] (P : Ideal W.toAffine.CoordinateRing)
    [P.IsMaximal] : IsDiscreteValuationRing (Localization.AtPrime P) := by
  obtain ⟨a, b, h, rfl⟩ := exists_eq_XYIdeal W P
  haveI : IsNoetherianRing (Localization.AtPrime (XYIdeal W.toAffine a (C b))) :=
    IsLocalization.isNoetherianRing (XYIdeal W.toAffine a (C b)).primeCompl _
      (isNoetherianRing_coordinateRing W)
  set t := algebraMap W.toAffine.CoordinateRing (Localization.AtPrime (XYIdeal W.toAffine a (C b)))
    (XClass W.toAffine a) with ht_def
  have ht : t ≠ 0 := fun h0 => XClass_ne_zero (W' := W.toAffine) a
    (IsLocalization.injective (Localization.AtPrime (XYIdeal W.toAffine a (C b)))
      (Ideal.primeCompl_le_nonZeroDivisors (XYIdeal W.toAffine a (C b))) (h0.trans (map_zero _).symm))
  have hmax := IsLocalization.AtPrime.map_eq_maximalIdeal (XYIdeal W.toAffine a (C b))
    (Localization.AtPrime (XYIdeal W.toAffine a (C b)))
  have hmul : maximalIdeal (Localization.AtPrime (XYIdeal W.toAffine a (C b))) *
      (XYIdeal W.toAffine a (C (W.toAffine.negY a b))).map (algebraMap _ _) = Ideal.span {t} := by
    rw [← hmax, ← Ideal.map_mul, mul_comm, XYIdeal_neg_mul h, XIdeal, Ideal.map_span,
      Set.image_singleton]
  have hnf : ¬ IsField (Localization.AtPrime (XYIdeal W.toAffine a (C b))) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq]
    intro hbot
    have : t ∈ maximalIdeal (Localization.AtPrime (XYIdeal W.toAffine a (C b))) := by
      rw [← hmax]
      exact Ideal.mem_map_of_mem _ (XClass_mem_XYIdeal W a _)
    rw [hbot, Ideal.mem_bot] at this
    exact ht this
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 0 4).mpr (maximalIdeal_isPrincipal_of_mul ht hmul)

/-- The coordinate ring of an elliptic curve over an algebraically closed field is Dedekind. -/
theorem isDedekindDomain [IsAlgClosed K] [W.IsElliptic] :
    IsDedekindDomain W.toAffine.CoordinateRing := by
  haveI : IsNoetherianRing W.toAffine.CoordinateRing := isNoetherianRing_coordinateRing W
  haveI : Algebra.IsIntegral K[X] W.toAffine.CoordinateRing := Algebra.IsIntegral.of_finite _ _
  haveI : IsDedekindDomainDvr W.toAffine.CoordinateRing :=
    { is_dvr_at_nonzero_prime := fun P hP0 hPp => by
        obtain ⟨r, hrP, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
        have hne : P.comap (algebraMap K[X] W.toAffine.CoordinateRing) ≠ ⊥ :=
          Ideal.comap_ne_bot_of_integral_mem hr0 hrP (Algebra.IsIntegral.isIntegral r)
        haveI : (P.comap (algebraMap K[X] W.toAffine.CoordinateRing)).IsPrime := Ideal.IsPrime.comap _
        haveI : (P.comap (algebraMap K[X] W.toAffine.CoordinateRing)).IsMaximal :=
          _root_.IsPrime.to_maximal_ideal hne
        haveI : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := K[X]) P inferInstance
        exact isDVR_localization W P }
  infer_instance

end Points

section Valuation

/-- Two `ℤᵐ⁰`-valued valuations on a field with the same valuation ring, each attaining
`exp (-1)`, are equal. -/
theorem valuation_eq_of_le_one_iff {F : Type*} [Field F] (ν₁ ν₂ : Valuation F (WithZero (Multiplicative ℤ)))
    (h : ∀ f, ν₁ f ≤ 1 ↔ ν₂ f ≤ 1) {t₁ t₂ : F} (h₁ : ν₁ t₁ = WithZero.exp (-1))
    (h₂ : ν₂ t₂ = WithZero.exp (-1)) : ν₁ = ν₂ := by
  have he : ν₁.IsEquiv ν₂ := Valuation.isEquiv_iff_val_le_one.mpr (h _)
  have heq1 : ∀ {x}, ν₁ x = 1 ↔ ν₂ x = 1 := Valuation.isEquiv_iff_val_eq_one.mp he
  have hlt1 : ∀ {x}, ν₁ x < 1 ↔ ν₂ x < 1 := Valuation.isEquiv_iff_val_lt_one.mp he
  have ht₁ : t₁ ≠ 0 := by rintro rfl; rw [map_zero] at h₁; exact WithZero.exp_ne_zero h₁.symm
  have ht₂ : t₂ ≠ 0 := by rintro rfl; rw [map_zero] at h₂; exact WithZero.exp_ne_zero h₂.symm
  have hν₁t₂ : ν₁ t₂ ≠ 0 := (Valuation.ne_zero_iff _).mpr ht₂
  have hν₂t₁ : ν₂ t₁ ≠ 0 := (Valuation.ne_zero_iff _).mpr ht₁
  obtain ⟨a, ha'⟩ : ∃ a : ℤ, ν₁ t₂ = WithZero.exp a := ⟨_, (WithZero.exp_log hν₁t₂).symm⟩
  obtain ⟨b, hb'⟩ : ∃ b : ℤ, ν₂ t₁ = WithZero.exp b := ⟨_, (WithZero.exp_log hν₂t₁).symm⟩
  have ha : a < 0 := by
    have : ν₁ t₂ < 1 := hlt1.mpr (by rw [h₂, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)
    rwa [ha', ← WithZero.exp_zero, WithZero.exp_lt_exp] at this
  have hb : b < 0 := by
    have : ν₂ t₁ < 1 := hlt1.mp (by rw [h₁, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)
    rwa [hb', ← WithZero.exp_zero, WithZero.exp_lt_exp] at this
  have hg : ν₁ (t₁ ^ (-a) * t₂⁻¹) = 1 := by
    rw [map_mul, map_zpow₀, map_inv₀, h₁, ha', ← WithZero.exp_zsmul, ← WithZero.exp_neg,
      ← WithZero.exp_add, WithZero.exp_eq_one]
    simp
  have hg2 := heq1.mp hg
  rw [map_mul, map_zpow₀, map_inv₀, h₂, hb', ← WithZero.exp_zsmul, ← WithZero.exp_neg,
    ← WithZero.exp_add, WithZero.exp_eq_one, smul_eq_mul] at hg2
  have ha1 : a = -1 := by nlinarith
  ext x
  by_cases hx : x = 0
  · simp [hx]
  have hx2 : ν₂ x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨n, hn⟩ : ∃ n : ℤ, ν₂ x = WithZero.exp n := ⟨_, (WithZero.exp_log hx2).symm⟩
  have h3 : ν₂ (x * t₂ ^ n) = 1 := by
    rw [map_mul, map_zpow₀, h₂, hn, ← WithZero.exp_zsmul, ← WithZero.exp_add, WithZero.exp_eq_one,
      smul_eq_mul]
    ring
  have h1 := heq1.mpr h3
  rw [map_mul, map_zpow₀, ha', ha1, ← WithZero.exp_zsmul, smul_eq_mul] at h1
  rw [hn, eq_inv_of_mul_eq_one_left h1, ← WithZero.exp_neg]
  congr 1
  ring

variable {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F]
  [IsFractionRing R F]

theorem valuation_le_one_iff_exists (v : IsDedekindDomain.HeightOneSpectrum R) (f : F) :
    v.valuation F f ≤ 1 ↔ ∃ a b : R, b ∉ v.asIdeal ∧ f * algebraMap R F b = algebraMap R F a := by
  constructor
  · intro hf
    obtain ⟨n, d, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer f hf
    exact ⟨n, d, d.2, hnd⟩
  · rintro ⟨a, b, hb, hab⟩
    have hb0 : algebraMap R F b ≠ 0 := by
      rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]
      rintro rfl
      exact hb v.asIdeal.zero_mem
    have hf : f = algebraMap R F a / algebraMap R F b := by
      rw [← hab, mul_div_cancel_right₀ _ hb0]
    rw [hf, map_div₀, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr hb, div_one]
    exact v.intValuation_le_one a

end Valuation


section HOS

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

/-- The height-one prime of the coordinate ring at an affine point `(x, y)`. -/
noncomputable def hos {x y : K} (h : W.toAffine.Nonsingular x y) :
    IsDedekindDomain.HeightOneSpectrum W.toAffine.CoordinateRing where
  asIdeal := XYIdeal W.toAffine x (C y)
  isPrime := (isMaximal_XYIdeal W h.1).isPrime
  ne_bot := by
    intro h0
    have := XClass_mem_XYIdeal W x (C y)
    rw [h0, Ideal.mem_bot] at this
    exact XClass_ne_zero (W' := W.toAffine) x this

lemma hos_asIdeal {x y : K} (h : W.toAffine.Nonsingular x y) :
    (hos W h).asIdeal = XYIdeal W.toAffine x (C y) := rfl

end HOS

end RPLib.Weil


