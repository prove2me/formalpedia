-- Prove2me | solution 1 for ArtinKP.A.kappa_mul_of_mem_Gamma
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:16:19.961024+00:00
-- url     : https://prove2.me/submissions/bb1c4eae-0fa6-4ffb-a599-5c49d2c44ca3

import Mathlib
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinKPB000

section
-- module Solutions.Artin.KP.A_Pkg
/-!
# WP-A: the global cubic symbol package and the `S`-Hilbert pairing

`CubicPkg F` is a universe-polymorphic, completion-free form of `C0Y.SymbolPkg F 3`: local cubic
Hilbert symbols `hv v : Fˣ →* Fˣ →* μ₃(F)` evaluated on *global* elements, with Steinberg, the
product formula, triviality on units and the tame formula at places prime to `3`, and local
constancy (`deep`).  Everything in WP-A is derived from a `CubicPkg`.

The orientation is pinned by the field `tame`: `hv v a π ≡ a^{(Nv-1)/3} (mod v)` for a `v`-unit
`a` and a uniformizer `π`.

Main results: `CubicPkg.skew`, `CubicPkg.self`, `CubicPkg.isTame` (the bridge to `A_Local`),
`CubicPkg.tame_zpow` (A1 for a unit against any element), `CubicPkg.tame_formula` (A1),
`CubicPkg.HS` (the pairing `(a,b)_S`), `CubicPkg.HS_mul_prod` (A2, product formula),
`CubicPkg.HS_unit`, `CubicPkg.HS_add_eq_one`, `CubicPkg.exists_isDeepLevel`,
`CubicPkg.HS_deep_right/left` (A4).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.A

variable (F : Type*) [Field F] [NumberField F]

variable {F}

namespace CubicPkg

variable (P : CubicPkg F)

/-! ### The `S`-part -/

/-- Steinberg relation for the `S`-pairing: `(a, 1 - a)_S = 1`. -/
theorem HS_add_eq_one {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥)
    (h3 : ∀ v : HeightOneSpectrum (𝓞 F), (3 : 𝓞 F) ∈ v.asIdeal → 𝔪 ≤ v.asIdeal) (a b : Fˣ)
    (hab : (a : F) + b = 1) : P.HS 𝔪 a b = 1 := by
  classical
  set T := extSupp 𝔪 (a : F) ∪ extSupp 𝔪 (b : F) with hTdef
  have hT : ∀ v ∈ T, ¬ 𝔪 ≤ v.asIdeal := by
    intro v hv
    rcases Finset.mem_union.mp hv with h | h <;> exact not_le_of_mem_extSupp h
  have hcov : ∀ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal → v ∉ T →
      v.valuation F (a : F) = 1 ∧ v.valuation F (b : F) = 1 := by
    intro v hv hvT
    rw [hTdef, Finset.mem_union, not_or, mem_extSupp a.ne_zero, mem_extSupp b.ne_zero] at hvT
    exact ⟨by_contra fun h => hvT.1 ⟨hv, h⟩, by_contra fun h => hvT.2 ⟨hv, h⟩⟩
  have h1 := P.HS_mul_prod' h𝔪 h3 a b T hT hcov
  have h2 : ∏ v ∈ T, P.hv v a b = 1 := by
    refine Finset.prod_eq_one fun v hv => ?_
    have := (P.isTame v (fun h => hT v hv (h3 v h))).add_eq_one a b hab
    simpa using this
  rwa [h2, mul_one] at h1

/-- Steinberg relation for the `S`-pairing, homogeneous form. -/
theorem HS_add_eq {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥)
    (h3 : ∀ v : HeightOneSpectrum (𝓞 F), (3 : 𝓞 F) ∈ v.asIdeal → 𝔪 ≤ v.asIdeal) (x y z : Fˣ)
    (hxyz : (x : F) + y = z) : P.HS 𝔪 (x / z) (y / z) = 1 := by
  apply P.HS_add_eq_one h𝔪 h3
  push_cast
  have : (z : F) ≠ 0 := z.ne_zero
  field_simp
  exact hxyz

/-! ### Deep units -/

end CubicPkg

end ArtinKP.A
end
end

section
-- module Solutions.Artin.KP.A_Kubota
/-!
# WP-A: the Kubota symbol on `SL₂(R)`, `R = SInt 𝔪`

* `kappa ι 𝔪 γ = (d/c)⁻¹` (`1` if `c = 0`), with `(d/c) = cubicExt`.
* `sigmaS P 𝔪 g₁ g₂ = (X(g₁g₂)/X(g₁), X(g₁g₂)/X(g₂))_S` on rational matrices.
* `kappa_mul` (Lemma A5): `κ(γ₁γ₂) = κ(γ₁) κ(γ₂) σ_S(γ₁,γ₂)⁻¹`.

  **Orientation.**  With the symbols oriented by `CubicPkg.tame` the exponent is `ε = -1`
  (equivalently `ε = +1` for the opposite pairing `(b,a)_S`).  It is forced: for
  `γ₁ = diag(ε₁⁻¹, ε₁)` with an `S`-unit `ε₁`, and `c₂ ≠ 0`,
  `κ(γ₁γ₂)/κ(γ₂) = (ε₁/c₂)⁻¹ = (c₂, ε₁)_S⁻¹ = σ_S(γ₁, γ₂)⁻¹` by the unit law.
* `sigmaS_eq_one`: `σ_S(g₁, g₂) = 1` as soon as `a₂`, `d₁` and `d₃` lie in the radical of `(·,·)_S`.
* `Gamma 𝔪 𝔫`: the image in `SL₂(R)` of the principal congruence subgroup of `SL₂(𝓞 F)` of level
  `𝔫`; `kappa_mul_of_mem_Gamma` (Corollary A6): `κ` is multiplicative on `Γ(𝔫)` for `𝔫 ≤ 𝔪^N`,
  `N ≥ 1` any deep level of the package (`CubicPkg.IsDeepLevel`); `kappaHom`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots Matrix

noncomputable section

namespace ArtinKP.A

variable {F : Type*} [Field F] [NumberField F]

variable {𝔪 : Ideal (𝓞 F)}

/-! ### Triviality of `σ_S` on deep matrices -/

theorem sigmaS_eq (P : CubicPkg F) (g₁ g₂ : Matrix.SpecialLinearGroup (Fin 2) F) (x1 x2 x3 : Fˣ)
    (h1 : (x1 : F) = X g₁) (h2 : (x2 : F) = X g₂) (h3 : (x3 : F) = X (g₁ * g₂)) :
    sigmaS P 𝔪 g₁ g₂ = P.HS 𝔪 (x3 / x1) (x3 / x2) := by
  have e1 : Xu g₁ = x1 := Units.ext h1.symm
  have e2 : Xu g₂ = x2 := Units.ext h2.symm
  have e3 : Xu (g₁ * g₂) = x3 := Units.ext h3.symm
  rw [sigmaS, e1, e2, e3]

/-- `σ_S(g₁, g₂) = 1` if `a₂`, `d₁` and the lower right entry `d₃` of `g₁g₂` lie in the radical
of the `S`-pairing. -/
theorem sigmaS_eq_one (P : CubicPkg F) (hG : Good 𝔪)
    (g₁ g₂ : Matrix.SpecialLinearGroup (Fin 2) F) (ha : IsRad P 𝔪 (g₂.1 0 0))
    (hd : IsRad P 𝔪 (g₁.1 1 1)) (hd3 : IsRad P 𝔪 ((g₁ * g₂).1 1 1)) :
    sigmaS P 𝔪 g₁ g₂ = 1 := by
  obtain ⟨ua, hua, hal⟩ := ha
  obtain ⟨ud, hud, hdl⟩ := hd
  obtain ⟨ud3, hud3, hd3l⟩ := hd3
  have har : ∀ y : Fˣ, P.HS 𝔪 y ua = 1 := fun y => by rw [P.HS_skew', hal, inv_one]
  have hdr : ∀ y : Fˣ, P.HS 𝔪 y ud = 1 := fun y => by rw [P.HS_skew', hdl, inv_one]
  have hd3r : ∀ y : Fˣ, P.HS 𝔪 y ud3 = 1 := fun y => by rw [P.HS_skew', hd3l, inv_one]
  have hc3 : (g₁ * g₂).1 1 0 = g₁.1 1 0 * g₂.1 0 0 + g₁.1 1 1 * g₂.1 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  by_cases z1 : g₁.1 1 0 = 0
  · have hX1 : (ud : F) = X g₁ := by rw [hud, X, Xs, if_pos z1]
    by_cases z2 : g₂.1 1 0 = 0
    · have z3 : (g₁ * g₂).1 1 0 = 0 := by rw [hc3, z1, z2]; ring
      have hX3 : (ud3 : F) = X (g₁ * g₂) := by rw [hud3, X, Xs, if_pos z3]
      rw [sigmaS_eq P g₁ g₂ ud (Xu g₂) ud3 hX1 rfl hX3]
      simp only [map_div, MonoidHom.div_apply, hd3l, hd3r, hdl, hdr, div_one]
    · obtain ⟨c2, hc2⟩ : ∃ c2 : Fˣ, (c2 : F) = g₂.1 1 0 := ⟨Units.mk0 _ z2, rfl⟩
      have hX2 : (c2 : F) = X g₂ := by rw [X, Xs, ← hc2, if_neg c2.ne_zero]
      have e3 : (g₁ * g₂).1 1 0 = ((ud * c2 : Fˣ) : F) := by
        rw [hc3, z1, Units.val_mul, hud, hc2]; ring
      have hX3 : ((ud * c2 : Fˣ) : F) = X (g₁ * g₂) := by
        rw [X, Xs, e3, if_neg (Units.ne_zero _)]
      rw [sigmaS_eq P g₁ g₂ ud c2 (ud * c2) hX1 hX2 hX3]
      simp only [map_div, map_mul, MonoidHom.div_apply, MonoidHom.mul_apply, hdl, hdr,
        P.HS_self, div_one, mul_one, one_mul]
  · obtain ⟨c1, hc1⟩ : ∃ c1 : Fˣ, (c1 : F) = g₁.1 1 0 := ⟨Units.mk0 _ z1, rfl⟩
    have hX1 : (c1 : F) = X g₁ := by rw [X, Xs, ← hc1, if_neg c1.ne_zero]
    by_cases z2 : g₂.1 1 0 = 0
    · have e3 : (g₁ * g₂).1 1 0 = ((c1 * ua : Fˣ) : F) := by
        rw [hc3, z2, Units.val_mul, hua, hc1]; ring
      have hX3 : ((c1 * ua : Fˣ) : F) = X (g₁ * g₂) := by
        rw [X, Xs, e3, if_neg (Units.ne_zero _)]
      rw [sigmaS_eq P g₁ g₂ c1 (Xu g₂) (c1 * ua) hX1 rfl hX3]
      simp only [map_div, map_mul, MonoidHom.div_apply, MonoidHom.mul_apply, hal, har,
        P.HS_self, div_one, mul_one, one_mul, div_self']
    · obtain ⟨c2, hc2⟩ : ∃ c2 : Fˣ, (c2 : F) = g₂.1 1 0 := ⟨Units.mk0 _ z2, rfl⟩
      have hX2 : (c2 : F) = X g₂ := by rw [X, Xs, ← hc2, if_neg c2.ne_zero]
      by_cases z3 : (g₁ * g₂).1 1 0 = 0
      · have hX3 : (ud3 : F) = X (g₁ * g₂) := by rw [hud3, X, Xs, if_pos z3]
        have hu : c1 = -(ud * c2 / ua) := by
          apply Units.ext
          push_cast
          rw [hua, hud, hc1, hc2]
          have hne : g₂.1 0 0 ≠ 0 := hua ▸ ua.ne_zero
          field_simp
          rw [hc3] at z3
          linear_combination z3
        rw [sigmaS_eq P g₁ g₂ c1 c2 ud3 hX1 hX2 hX3, hu]
        simp only [map_div, map_mul, map_neg, MonoidHom.div_apply, MonoidHom.mul_apply, hd3l,
          hd3r, hdl, hdr, hal, har, P.HS_self, P.HS_neg_left, div_one, mul_one, one_mul,
          one_div, inv_one, inv_inv]
      · obtain ⟨c3, hc3'⟩ : ∃ c3 : Fˣ, (c3 : F) = (g₁ * g₂).1 1 0 := ⟨Units.mk0 _ z3, rfl⟩
        have hX3 : (c3 : F) = X (g₁ * g₂) := by rw [X, Xs, ← hc3', if_neg c3.ne_zero]
        have hsum : ((c1 * ua : Fˣ) : F) + ((ud * c2 : Fˣ) : F) = c3 := by
          push_cast
          rw [hua, hud, hc1, hc2, hc3', hc3]
        have hst := P.HS_add_eq hG.ne_bot hG.three (c1 * ua) (ud * c2) c3 hsum
        have e32 : P.HS 𝔪 c3 c2 = (P.HS 𝔪 c2 c3)⁻¹ := P.HS_skew' 𝔪 c3 c2
        have e33 := P.HS_self 𝔪 c3
        rw [sigmaS_eq P g₁ g₂ c1 c2 c3 hX1 hX2 hX3]
        simp only [map_div, map_mul, MonoidHom.div_apply, MonoidHom.mul_apply, hdl, hdr, hal,
          har, mul_one, one_mul, e32, e33] at hst ⊢
        refine Eq.trans ?_ hst
        simp only [div_eq_mul_inv, _root_.mul_inv_rev, inv_inv, mul_one, one_mul, inv_one]
        ac_rfl

/-! ### The principal congruence subgroup and Corollary A6 -/

/-- Integers `≡ 1 mod 𝔪^N` (`N ≥ 1` a deep level) lie in the radical of the `S`-pairing. -/
theorem isRad_of_sub_one_mem (P : CubicPkg F) (hG : Good 𝔪) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : P.IsDeepLevel 𝔪 N) (x : 𝓞 F) (hx : x - 1 ∈ 𝔪 ^ N) :
    IsRad P 𝔪 (algebraMap (𝓞 F) F x) := by
  obtain ⟨v₀, hv₀⟩ := hG.exists_place
  have hx0 : x ≠ 0 := by
    rintro rfl
    have h1 : (0 : 𝓞 F) - 1 ∈ 𝔪 := Ideal.pow_le_self (by omega) hx
    have h2 : (1 : 𝓞 F) ∈ v₀.asIdeal := by
      have := hv₀ h1
      rw [zero_sub] at this
      simpa using v₀.asIdeal.neg_mem this
    exact v₀.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h2)
  have hxF : algebraMap (𝓞 F) F x ≠ 0 := by
    intro h
    exact hx0 (FaithfulSMul.algebraMap_injective (𝓞 F) F (by simpa using h))
  refine ⟨Units.mk0 _ hxF, rfl, fun y => P.HS_deep_left hG.ne_bot hN _ y fun v hv => ?_⟩
  have hmem : x - 1 ∈ v.asIdeal ^ N := Ideal.pow_right_mono hv N hx
  have := (v.intValuation_le_pow_iff_mem (x - 1) N).mpr hmem
  rw [← v.valuation_of_algebraMap (K := F)] at this
  simpa using this

/-- **Corollary A6.** `κ` is multiplicative on `Γ(𝔫)` for every `𝔫 ≤ 𝔪^N`, `N ≥ 1` a deep level. -/
theorem kappa_mul_of_mem_Gamma_oai (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F}
    (hz6 : IsPrimitiveRoot z6 6) {N : ℕ} (hN1 : 1 ≤ N) (hN : P.IsDeepLevel 𝔪 N)
    {𝔫 : Ideal (𝓞 F)} (h𝔫 : 𝔫 ≤ 𝔪 ^ N) {γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)}
    (h₁ : γ₁ ∈ Gamma 𝔪 𝔫) (h₂ : γ₂ ∈ Gamma 𝔪 𝔫) :
    kappa ι 𝔪 (γ₁ * γ₂) = kappa ι 𝔪 γ₁ * kappa ι 𝔪 γ₂ := by
  have hrad : ∀ γ ∈ Gamma 𝔪 𝔫, ∀ i : Fin 2, IsRad P 𝔪 ((toF 𝔪 γ).1 i i) := by
    intro γ hγ i
    obtain ⟨γ₀, h0, rfl⟩ := (mem_Gamma_iff γ).mp hγ
    have := isRad_of_sub_one_mem P hG hN1 hN (γ₀.1 i i) (h𝔫 (by simpa using h0 i i))
    exact this
  have h3 := hrad _ (mul_mem h₁ h₂) 1
  rw [map_mul] at h3
  rw [kappa_mul ι P hG hz6, sigmaS_eq_one P hG _ _ (hrad γ₂ h₂ 0) (hrad γ₁ h₁ 1) h3, map_one,
    inv_one, mul_one]

end ArtinKP.A
end
end

theorem solution.{u_1} : type_of% @ArtinKP.A.kappa_mul_of_mem_Gamma_oai.{u_1} := @ArtinKP.A.kappa_mul_of_mem_Gamma_oai.{u_1}
