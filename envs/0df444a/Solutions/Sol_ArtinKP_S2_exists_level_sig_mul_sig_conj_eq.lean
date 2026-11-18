-- Prove2me | solution 1 for ArtinKP.S2.exists_level_sig_mul_sig_conj_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:32:57.985196+00:00
-- url     : https://prove2.me/submissions/781fc0b1-e4cf-4abc-a9f9-8393bdbc6c73

import Mathlib
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ArtinKPB004

section
-- module Solutions.Artin.KP.A_Pkg
attribute [-instance] _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero
attribute [-simp] _root_.ArtinKP.S.GSection.add_apply _root_.ArtinKP.S.GSection.nT_apply _root_.ArtinKP.S.GSection.smulFun_apply _root_.ArtinKP.S.GSection.smul_apply _root_.ArtinKP.S.GSection.twist_apply _root_.ArtinKP.S.GSection.zero_apply _root_.ArtinKP.S.TSection.translate_apply _root_.ArtinKP.S.brk_neg_left _root_.ArtinKP.S.brk_neg_right _root_.ArtinKP.S.brk_one_left _root_.ArtinKP.S.brk_one_right _root_.ArtinKP.S.brk_pow_three_left _root_.ArtinKP.S.brk_pow_three_right _root_.ArtinKP.S.brk_self _root_.ArtinKP.S.brk_zero_left _root_.ArtinKP.S.brk_zero_right _root_.ArtinKP.S2.cubicSymbol_sym
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

theorem HS_neg_one_right (𝔪 : Ideal (𝓞 F)) (a : Fˣ) : P.HS 𝔪 a (-1) = 1 := by
  rw [P.HS_apply]
  exact Finset.prod_eq_one fun v _ => P.neg_one_right v a

theorem HS_neg_right (𝔪 : Ideal (𝓞 F)) (a b : Fˣ) : P.HS 𝔪 a (-b) = P.HS 𝔪 a b := by
  rw [← neg_one_mul, map_mul, P.HS_neg_one_right, one_mul]

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

/-! ### Deep units -/

end CubicPkg

end ArtinKP.A
end
end

section
-- module Solutions.Artin.KP.S2_Cocycle
attribute [-simp] _root_.ArtinKP.S.Xs_zero
/-!
# WP-S2, part 1: Kubota's cocycle identity for a Steinberg symbol

`F` is any field and `t : Fˣ → Fˣ → A` a bi-additive symbol with `t a (-a) = 0`, `t (-1) a = 0`
and the Steinberg relation `a + b = 1 → t a b = 0` (`IsSteinbergSymbol`; no valuation, no
tameness).  With `X(c, d) = c` if `c ≠ 0`, else `d`, and for a row `p` and a matrix `h`

  `σ(p, h) = t (X(ph)/X(p)) (X(ph)/X(h))`     (`X(h)` = `X` of the bottom row),

`cocycle_scalar` is Kubota's 2-cocycle identity on all of `SL₂(F)`, in row form:

  `σ(p, h) + σ(ph, k) = σ(p, hk) + σ(bot h, k)`.

Proof.  Put `P = (p₂, -p₁)ᵀ`, `E = e₁`, `A = h e₁`, `B = hk e₁`.  The six `X`-values are the
"brackets" `[U, V] = U ∧ V` (or the ratio `U/V` when `U ∥ V`) of the four vectors, and the
identity is the 4-point relation

  `t([P,A]/[P,E], [P,A]/[E,A]) + t([P,B]/[P,A], [P,B]/[A,B])
      = t([P,B]/[P,E], [P,B]/[E,B]) + t([E,B]/[E,A], [E,B]/[A,B])`.

In general position it is *equivalent* (by bi-additivity, `t x x = 0`, skew-symmetry) to the
Steinberg relation for the Plücker identity `[P,E][A,B] + [P,B][E,A] = [P,A][E,B]`
(`coc_generic`); the eight degenerate configurations are bi-additive identities.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section

namespace ArtinKP.S2

open ArtinKP.A

variable {F : Type*} [Field F] {A : Type*} [AddCommGroup A]

namespace IsSteinbergSymbol

variable {t : Fˣ → Fˣ → A} (h : IsSteinbergSymbol t)
include h

theorem one_left (c : Fˣ) : t 1 c = 0 := by
  have := h.mul_left 1 1 c
  rw [mul_one] at this
  simpa using this

theorem one_right (c : Fˣ) : t c 1 = 0 := by
  have := h.mul_right c 1 1
  rw [mul_one] at this
  simpa using this

theorem inv_left (a c : Fˣ) : t a⁻¹ c = -t a c := by
  have := h.mul_left a a⁻¹ c
  rw [mul_inv_cancel, h.one_left] at this
  exact eq_neg_of_add_eq_zero_right this.symm

theorem inv_right (a c : Fˣ) : t a c⁻¹ = -t a c := by
  have := h.mul_right a c c⁻¹
  rw [mul_inv_cancel, h.one_right] at this
  exact eq_neg_of_add_eq_zero_right this.symm

theorem div_left (a b c : Fˣ) : t (a / b) c = t a c - t b c := by
  rw [div_eq_mul_inv, h.mul_left, h.inv_left, sub_eq_add_neg]

theorem div_right (a b c : Fˣ) : t a (b / c) = t a b - t a c := by
  rw [div_eq_mul_inv, h.mul_right, h.inv_right, sub_eq_add_neg]

theorem neg_left (a b : Fˣ) : t (-a) b = t a b := by
  rw [← neg_one_mul, h.mul_left, h.neg_one_left, zero_add]

theorem self (b : Fˣ) : t b b = 0 := by
  have := h.steinberg (-b)
  rwa [neg_neg, h.neg_left] at this

theorem neg_one_right (b : Fˣ) : t b (-1) = 0 := by
  have := h.steinberg b
  rwa [← neg_one_mul, h.mul_right, h.self, add_zero] at this

theorem neg_right (a b : Fˣ) : t a (-b) = t a b := by
  rw [← neg_one_mul, h.mul_right, h.neg_one_right, zero_add]

theorem skew (a b : Fˣ) : t a b + t b a = 0 := by
  have := h.self (a * b)
  rw [h.mul_left, h.mul_right, h.mul_right, h.self, h.self] at this
  linear_combination (norm := module) this

/-- Steinberg relation in homogeneous form. -/
theorem add_eq (x y z : Fˣ) (hxyz : (x : F) + y = z) : t (x / z) (y / z) = 0 := by
  apply h.add_eq_one
  push_cast
  have : (z : F) ≠ 0 := z.ne_zero
  field_simp
  exact hxyz

end IsSteinbergSymbol

section Cases

variable {t : Fˣ → Fˣ → A} (h : IsSteinbergSymbol t)
include h

/-- `P ∥ E`. -/
theorem coc_PE {u y y₁ z : F} (hu : u ≠ 0) (hy : y ≠ 0) (hy₁ : y₁ ≠ 0) (hz : z ≠ 0) :
    Coc t u (u * y) (u * y₁) y y₁ z := by
  lift u to Fˣ using hu.isUnit
  lift y to Fˣ using hy.isUnit
  lift y₁ to Fˣ using hy₁.isUnit
  lift z to Fˣ using hz.isUnit
  unfold Coc
  simp only [← Units.val_mul, ← Units.val_div_eq_div_val, tz_coe]
  simp only [h.div_left, h.div_right, h.mul_left, h.mul_right]
  abel

/-- `E ∥ A` (the middle matrix is upper triangular). -/
theorem coc_EA {p d x₂ z : F} (hp : p ≠ 0) (hd : d ≠ 0) (hx₂ : x₂ ≠ 0) (hz : z ≠ 0) :
    Coc t p (p / d) x₂ d (d * z) z := by
  lift p to Fˣ using hp.isUnit
  lift d to Fˣ using hd.isUnit
  lift x₂ to Fˣ using hx₂.isUnit
  lift z to Fˣ using hz.isUnit
  unfold Coc
  simp only [← Units.val_mul, ← Units.val_div_eq_div_val, tz_coe]
  simp only [h.div_left, h.div_right, h.mul_left, h.mul_right]
  linear_combination (norm := module) h.self d + h.self d - h.skew d p + h.skew d x₂ - h.skew d z

/-- `A ∥ B` (the last matrix is upper triangular), `P ∦ A`. -/
theorem coc_AB {x x₁ y δ : F} (hx : x ≠ 0) (hx₁ : x₁ ≠ 0) (hy : y ≠ 0) (hδ : δ ≠ 0) :
    Coc t x x₁ (x₁ / δ) y (y / δ) δ := by
  lift x to Fˣ using hx.isUnit
  lift x₁ to Fˣ using hx₁.isUnit
  lift y to Fˣ using hy.isUnit
  lift δ to Fˣ using hδ.isUnit
  unfold Coc
  simp only [← Units.val_mul, ← Units.val_div_eq_div_val, tz_coe]
  simp only [h.div_left, h.div_right, h.mul_left, h.mul_right]
  abel

/-- `P ∥ A ∥ B`. -/
theorem coc_PAB {x y δ : F} (hx : x ≠ 0) (hy : y ≠ 0) (hδ : δ ≠ 0) :
    Coc t x (-(x / y)) (-(x * δ / y)) y (y / δ) δ := by
  lift x to Fˣ using hx.isUnit
  lift y to Fˣ using hy.isUnit
  lift δ to Fˣ using hδ.isUnit
  unfold Coc
  simp only [← Units.val_mul, ← Units.val_div_eq_div_val, ← Units.val_neg, tz_coe]
  simp only [h.div_left, h.div_right, h.mul_left, h.mul_right, h.neg_left, h.neg_right]
  linear_combination (norm := module) (2 : ℤ) • h.skew y δ - (4 : ℤ) • h.self δ

/-- General position: the Plücker relation and the Steinberg relation. -/
theorem coc_generic {x x₁ x₂ y y₁ z : F} (hx : x ≠ 0) (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hy : y ≠ 0) (hy₁ : y₁ ≠ 0) (hz : z ≠ 0) (hP : x * z + x₂ * y = x₁ * y₁) :
    Coc t x x₁ x₂ y y₁ z := by
  lift x to Fˣ using hx.isUnit
  lift x₁ to Fˣ using hx₁.isUnit
  lift x₂ to Fˣ using hx₂.isUnit
  lift y to Fˣ using hy.isUnit
  lift y₁ to Fˣ using hy₁.isUnit
  lift z to Fˣ using hz.isUnit
  have e := h.add_eq (x * z) (x₂ * y) (x₁ * y₁) (by push_cast; exact hP)
  unfold Coc
  simp only [← Units.val_mul, ← Units.val_div_eq_div_val, tz_coe]
  simp only [h.div_left, h.div_right, h.mul_left, h.mul_right] at e ⊢
  linear_combination (norm := module) e - h.skew x₁ y₁ + h.skew x₁ z + h.skew x₂ y₁
    - h.skew x₂ z + h.skew y y₁ - h.skew y z - (2 : ℤ) • h.self y₁ + h.skew y₁ z

/-- `P ∥ A` only. -/
theorem coc_PA {x y y₁ z : F} (hx : x ≠ 0) (hy : y ≠ 0) (hy₁ : y₁ ≠ 0) (hz : z ≠ 0) :
    Coc t x (-(x / y)) (-(x * z / y)) y y₁ z := by
  lift x to Fˣ using hx.isUnit
  lift y to Fˣ using hy.isUnit
  lift y₁ to Fˣ using hy₁.isUnit
  lift z to Fˣ using hz.isUnit
  unfold Coc
  simp only [← Units.val_mul, ← Units.val_div_eq_div_val, ← Units.val_neg, tz_coe]
  simp only [h.div_left, h.div_right, h.mul_left, h.mul_right, h.neg_left, h.neg_right]
  linear_combination (norm := module) h.self y - h.self y₁ + h.skew y₁ z - h.self z

/-- `P ∥ A` and `E ∥ B`. -/
theorem coc_PA_EB {x y z : F} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    Coc t x (-(x / y)) (-(x * z / y)) y (-(y / z)) z := by
  lift x to Fˣ using hx.isUnit
  lift y to Fˣ using hy.isUnit
  lift z to Fˣ using hz.isUnit
  unfold Coc
  simp only [← Units.val_mul, ← Units.val_div_eq_div_val, ← Units.val_neg, tz_coe]
  simp only [h.div_left, h.div_right, h.mul_left, h.mul_right, h.neg_left, h.neg_right]
  linear_combination (norm := module) (2 : ℤ) • h.skew y z - (4 : ℤ) • h.self z

/-- `E ∥ B` only. -/
theorem coc_EB {x x₁ y z : F} (hx : x ≠ 0) (hx₁ : x₁ ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    Coc t x x₁ (-(x * z / y)) y (-(y / z)) z := by
  lift x to Fˣ using hx.isUnit
  lift x₁ to Fˣ using hx₁.isUnit
  lift y to Fˣ using hy.isUnit
  lift z to Fˣ using hz.isUnit
  unfold Coc
  simp only [← Units.val_mul, ← Units.val_div_eq_div_val, ← Units.val_neg, tz_coe]
  simp only [h.div_left, h.div_right, h.mul_left, h.mul_right, h.neg_left, h.neg_right]
  linear_combination (norm := module) h.self x - h.skew x x₁ + h.self x₁ - h.self y
    + (2 : ℤ) • h.skew y z - (4 : ℤ) • h.self z

/-- `P ∥ B` only. -/
theorem coc_PB {x x₁ y z : F} (hx : x ≠ 0) (hx₁ : x₁ ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    Coc t x x₁ (-(x₁ / z)) y (x * z / x₁) z := by
  lift x to Fˣ using hx.isUnit
  lift x₁ to Fˣ using hx₁.isUnit
  lift y to Fˣ using hy.isUnit
  lift z to Fˣ using hz.isUnit
  unfold Coc
  simp only [← Units.val_mul, ← Units.val_div_eq_div_val, ← Units.val_neg, tz_coe]
  simp only [h.div_left, h.div_right, h.mul_left, h.mul_right, h.neg_left, h.neg_right]
  linear_combination (norm := module) -(2 : ℤ) • h.self x + (2 : ℤ) • h.skew x x₁ + h.skew x y
    - (2 : ℤ) • h.skew x z - (2 : ℤ) • h.self x₁ - h.skew x₁ y + (2 : ℤ) • h.skew x₁ z

end Cases

theorem Xs_ne_zero_of {c d : F} (h : c ≠ 0 ∨ d ≠ 0) : Xs c d ≠ 0 := by
  by_cases hc : c = 0
  · subst hc; simpa [Xs_zero_left] using h
  · rwa [Xs_ne d hc]

/-- **Kubota's cocycle identity** on `SL₂(F)` for a Steinberg symbol, in row form:
`σ(p, h) + σ(ph, k) = σ(p, hk) + σ(bot h, k)` with `h = [[a,b],[c,d]]`, `k = [[α,β],[γ,δ]]`. -/
theorem cocycle_scalar {t : Fˣ → Fˣ → A} (h : IsSteinbergSymbol t)
    {p₁ p₂ a b c d α β γ δ : F} (hp : p₁ ≠ 0 ∨ p₂ ≠ 0)
    (det1 : a * d - b * c = 1) (det2 : α * δ - β * γ = 1) :
    Coc t (Xs p₁ p₂) (Xs (p₁ * a + p₂ * c) (p₁ * b + p₂ * d))
      (Xs ((p₁ * a + p₂ * c) * α + (p₁ * b + p₂ * d) * γ)
        ((p₁ * a + p₂ * c) * β + (p₁ * b + p₂ * d) * δ))
      (Xs c d) (Xs (c * α + d * γ) (c * β + d * δ)) (Xs γ δ) := by
  have hcd : c ≠ 0 ∨ d ≠ 0 := by
    by_contra hh
    rw [not_or, not_not, not_not] at hh
    rw [hh.1, hh.2] at det1
    simp at det1
  have hγδ : γ ≠ 0 ∨ δ ≠ 0 := by
    by_contra hh
    rw [not_or, not_not, not_not] at hh
    rw [hh.1, hh.2] at det2
    simp at det2
  have hm : c * α + d * γ ≠ 0 ∨ c * β + d * δ ≠ 0 := by
    by_contra hh
    rw [not_or, not_not, not_not] at hh
    rcases hcd with h0 | h0
    · exact h0 (by linear_combination δ * hh.1 - γ * hh.2 - c * det2)
    · exact h0 (by linear_combination -β * hh.1 + α * hh.2 - d * det2)
  set q₁ := p₁ * a + p₂ * c with hq₁
  set q₂ := p₁ * b + p₂ * d with hq₂
  set m₁ := c * α + d * γ with hm₁
  set m₂ := c * β + d * δ with hm₂
  set r₁ := q₁ * α + q₂ * γ with hr₁
  set r₂ := q₁ * β + q₂ * δ with hr₂
  have hq : q₁ ≠ 0 ∨ q₂ ≠ 0 := by
    by_contra hh
    rw [not_or, not_not, not_not] at hh
    rcases hp with h0 | h0
    · exact h0 (by linear_combination d * hh.1 - c * hh.2 - p₁ * det1)
    · exact h0 (by linear_combination -b * hh.1 + a * hh.2 - p₂ * det1)
  have hr : r₁ ≠ 0 ∨ r₂ ≠ 0 := by
    by_contra hh
    rw [not_or, not_not, not_not] at hh
    rcases hq with h0 | h0
    · exact h0 (by linear_combination δ * hh.1 - γ * hh.2 - q₁ * det2)
    · exact h0 (by linear_combination -β * hh.1 + α * hh.2 - q₂ * det2)
  have hplu : p₁ * γ + r₁ * c = q₁ * m₁ := by
    rw [hr₁, hq₁, hq₂, hm₁]; linear_combination -(p₁ * γ) * det1
  by_cases hp₁ : p₁ = 0
  · -- `P ∥ E`
    have hp₂ : p₂ ≠ 0 := hp.resolve_left (not_not.mpr hp₁)
    have e1 : q₁ = p₂ * c := by rw [hq₁, hp₁]; ring
    have e2 : q₂ = p₂ * d := by rw [hq₂, hp₁]; ring
    have e3 : r₁ = p₂ * m₁ := by rw [hr₁, e1, e2, hm₁]; ring
    have e4 : r₂ = p₂ * m₂ := by rw [hr₂, e1, e2, hm₂]; ring
    rw [e1, e2, e3, e4, hp₁, Xs_zero_left, Xs_smul hp₂, Xs_smul hp₂]
    exact coc_PE h hp₂ (Xs_ne_zero_of hcd) (Xs_ne_zero_of hm) (Xs_ne_zero_of hγδ)
  rw [Xs_ne _ hp₁]
  by_cases hc : c = 0
  · -- `E ∥ A`
    have hd : d ≠ 0 := hcd.resolve_left (not_not.mpr hc)
    have had : a * d = 1 := by rw [hc] at det1; linear_combination det1
    have e1 : q₁ = p₁ / d := by
      rw [hq₁, hc]; field_simp; linear_combination p₁ * had
    have hq₁0 : q₁ ≠ 0 := by rw [e1]; exact div_ne_zero hp₁ hd
    have e3 : m₁ = d * γ := by rw [hm₁, hc]; ring
    have e4 : m₂ = d * δ := by rw [hm₂, hc]; ring
    rw [Xs_ne _ hq₁0, e1, e3, e4, hc, Xs_zero_left, Xs_smul hd]
    exact coc_EA h hp₁ hd (Xs_ne_zero_of hr) (Xs_ne_zero_of hγδ)
  rw [Xs_ne _ hc]
  by_cases hγ : γ = 0
  · -- `A ∥ B`
    have hδ : δ ≠ 0 := hγδ.resolve_left (not_not.mpr hγ)
    have hαδ : α * δ = 1 := by rw [hγ] at det2; linear_combination det2
    have e3 : m₁ = c / δ := by
      rw [hm₁, hγ]; field_simp; linear_combination c * hαδ
    have hm₁0 : m₁ ≠ 0 := by rw [e3]; exact div_ne_zero hc hδ
    rw [Xs_ne _ hm₁0, e3, hγ, Xs_zero_left]
    by_cases hq₁0 : q₁ = 0
    · have hq₂0 : q₂ ≠ 0 := hq.resolve_left (not_not.mpr hq₁0)
      have e2 : q₂ = -(p₁ / c) := by
        field_simp
        rw [hq₁] at hq₁0
        rw [hq₂]; linear_combination d * hq₁0 - p₁ * det1
      have e5 : r₁ = 0 := by rw [hr₁, hq₁0, hγ]; ring
      have e6 : r₂ = -(p₁ * δ / c) := by rw [hr₂, hq₁0, e2]; field_simp; ring
      rw [e5, e6, hq₁0, Xs_zero_left, Xs_zero_left, e2]
      exact coc_PAB h hp₁ hc hδ
    · have e5 : r₁ = q₁ / δ := by
        rw [hr₁, hγ]; field_simp; linear_combination q₁ * hαδ
      have hr₁0 : r₁ ≠ 0 := by rw [e5]; exact div_ne_zero hq₁0 hδ
      rw [Xs_ne _ hr₁0, e5, Xs_ne _ hq₁0]
      exact coc_AB h hp₁ hq₁0 hc hδ
  rw [Xs_ne _ hγ]
  have hm₂γ : m₁ = 0 → m₂ = -(c / γ) := by
    intro h0
    field_simp
    rw [hm₁] at h0
    rw [hm₂]; linear_combination δ * h0 - c * det2
  by_cases hq₁0 : q₁ = 0
  · have e2 : q₂ = -(p₁ / c) := by
      field_simp
      rw [hq₁] at hq₁0
      rw [hq₂]; linear_combination d * hq₁0 - p₁ * det1
    have e5 : r₁ = -(p₁ * γ / c) := by rw [hr₁, hq₁0, e2]; field_simp; ring
    have hr₁0 : r₁ ≠ 0 := by
      rw [e5]; exact neg_ne_zero.mpr (div_ne_zero (mul_ne_zero hp₁ hγ) hc)
    rw [Xs_ne _ hr₁0, e5, hq₁0, Xs_zero_left, e2]
    by_cases hm₁0 : m₁ = 0
    · rw [hm₁0, Xs_zero_left, hm₂γ hm₁0]
      exact coc_PA_EB h hp₁ hc hγ
    · rw [Xs_ne _ hm₁0]
      exact coc_PA h hp₁ hc hm₁0 hγ
  rw [Xs_ne _ hq₁0]
  by_cases hm₁0 : m₁ = 0
  · have e5 : r₁ = -(p₁ * γ / c) := by
      field_simp
      rw [hm₁0] at hplu
      linear_combination hplu
    have hr₁0 : r₁ ≠ 0 := by
      rw [e5]; exact neg_ne_zero.mpr (div_ne_zero (mul_ne_zero hp₁ hγ) hc)
    rw [Xs_ne _ hr₁0, e5, hm₁0, Xs_zero_left, hm₂γ hm₁0]
    exact coc_EB h hp₁ hq₁0 hc hγ
  rw [Xs_ne _ hm₁0]
  by_cases hr₁0 : r₁ = 0
  · have e6 : r₂ = -(q₁ / γ) := by
      field_simp
      rw [hr₁] at hr₁0
      rw [hr₂]; linear_combination δ * hr₁0 - q₁ * det2
    have e3 : m₁ = p₁ * γ / q₁ := by
      field_simp
      rw [hr₁0] at hplu
      linear_combination -hplu
    rw [hr₁0, Xs_zero_left, e6, e3]
    exact coc_PB h hp₁ hq₁0 hc hγ
  · rw [Xs_ne _ hr₁0]
    exact coc_generic h hp₁ hq₁0 hr₁0 hc hm₁0 hγ hplu

end ArtinKP.S2
end
end

section
-- module Solutions.Artin.KP.S2_Sig
attribute [-simp] _root_.ArtinKP.S2.cubicSymbol_sym
/-!
# WP-S2, part 2: Kubota's cocycle identity for `σ_S` on `SL₂(F)`

* `isSteinberg`: `(·,·)_S` is a Steinberg symbol in the sense of `S2_Cocycle`.
* `sig_cocycle`: `σ_S(p, h) σ_S(ph, k) = σ_S(p, hk) σ_S(bot h, k)` for every non-zero pair
  `p ∈ F²` and all `h, k ∈ SL₂(F)` (no integrality, no depth).
* `sigmaS_cocycle`: the same on `Matrix.SpecialLinearGroup (Fin 2) F`.
* `sig_smul`: `σ_S(lp, h) = σ_S(p, h) ⟨X(ph)/X(p), l⟩`.
* `sig_conj`: for `σ ∈ SL₂(F)` and `k` deep enough (depending on `σ`),
  `σ_S(bot σ, σ⁻¹kσ) = σ_S(bot k, σ)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S2

open ArtinKP.A ArtinKP.S

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

theorem isSteinberg (P : CubicPkg F) (hG : Good 𝔪) : IsSteinbergSymbol (tS P 𝔪) where
  mul_left a b c := by simp only [tS, map_mul, MonoidHom.mul_apply, ofMul_mul]
  mul_right a b c := by simp only [tS, map_mul, ofMul_mul]
  steinberg a := by
    simp only [tS]
    rw [P.HS_neg_right, P.HS_self, ofMul_one]
  neg_one_left a := by
    simp only [tS]
    rw [P.HS_neg_left, map_one, MonoidHom.one_apply, ofMul_one]
  add_eq_one a b hab := by
    simp only [tS]
    rw [P.HS_add_eq_one hG.ne_bot hG.three a b hab, ofMul_one]

variable {ι : F →+* ℂ} {P : CubicPkg F}

theorem brk_eq_tz (x y : F) :
    brk ι P 𝔪 x y = iota3 ι (Additive.toMul (tz (tS P 𝔪) x y)) := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  lift x to Fˣ using IsUnit.mk0 x hx
  lift y to Fˣ using IsUnit.mk0 y hy
  rw [brk_units, tz_coe]
  rfl

/-- **Kubota's cocycle identity** for `σ_S`, on a non-zero pair and two matrices of `SL₂(F)`. -/
theorem sig_cocycle (hG : Good 𝔪) {p₁ p₂ a b c d α β γ δ : F} (hp : p₁ ≠ 0 ∨ p₂ ≠ 0)
    (det1 : a * d - b * c = 1) (det2 : α * δ - β * γ = 1) :
    sig ι P 𝔪 p₁ p₂ a b c d * sig ι P 𝔪 (p₁ * a + p₂ * c) (p₁ * b + p₂ * d) α β γ δ
      = sig ι P 𝔪 p₁ p₂ (a * α + b * γ) (a * β + b * δ) (c * α + d * γ) (c * β + d * δ)
        * sig ι P 𝔪 c d α β γ δ := by
  have hC := cocycle_scalar (isSteinberg P hG) hp det1 det2
  unfold Coc at hC
  have h2 := congrArg (fun z => iota3 ι (Additive.toMul z)) hC
  simp only [toMul_add, map_mul, ← brk_eq_tz] at h2
  have e1 : p₁ * (a * α + b * γ) + p₂ * (c * α + d * γ)
      = (p₁ * a + p₂ * c) * α + (p₁ * b + p₂ * d) * γ := by ring
  have e2 : p₁ * (a * β + b * δ) + p₂ * (c * β + d * δ)
      = (p₁ * a + p₂ * c) * β + (p₁ * b + p₂ * d) * δ := by ring
  simp only [sig, e1, e2]
  exact h2

/-- **Conjugation of deep elements**: `σ_S(bot σ, σ⁻¹kσ) = σ_S(bot k, σ)` for `k` deep enough. -/
theorem sig_conj (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {α β γ δ : F}
    (det : α * δ - β * γ = 1) :
    ∃ N : ℕ, ∀ a b c' d' : F, IsK 𝔪 N a b c' d' →
      sig ι P 𝔪 γ δ (cj00 α β γ δ a b c' d') (cj01 α β γ δ a b c' d') (cj10 α β γ δ a b c' d')
          (cj11 α β γ δ a b c' d')
        = sig ι P 𝔪 c' d' α β γ δ := by
  obtain ⟨N₀, hN₀1, hN₀⟩ := P.exists_isDeepLevel hG.ne_bot
  obtain ⟨v₀, hv₀⟩ := hG.exists_place
  have hN₀1' : (1 : ℤ) ≤ N₀ := by exact_mod_cast hN₀1
  by_cases hγ : γ = 0
  · refine ⟨N₀, fun a b c' d' hK => ?_⟩
    have hαδ : α * δ = 1 := by rw [hγ] at det; linear_combination det
    have hα : α ≠ 0 := left_ne_zero_of_mul_eq_one hαδ
    obtain rfl : δ = α⁻¹ := eq_inv_of_mul_eq_one_right hαδ
    have hd0 : d' ≠ 0 := by
      intro h
      have := hK.hd.val_eq_one hN₀1' v₀ hv₀
      rw [h, map_zero] at this
      exact zero_ne_one this
    have hdr : ∀ x, brk ι P 𝔪 x d' = 1 := fun x => brk_deep_right hG hN₀ x hK.hd
    have hdl : ∀ y, brk ι P 𝔪 d' y = 1 := fun y => brk_deep_left hG hN₀ y hK.hd
    have e1 : γ * cj00 α β γ α⁻¹ a b c' d' + α⁻¹ * cj10 α β γ α⁻¹ a b c' d' = α * c' := by
      simp only [cj00, cj10, hγ]; field_simp; ring
    have e2 : γ * cj01 α β γ α⁻¹ a b c' d' + α⁻¹ * cj11 α β γ α⁻¹ a b c' d'
        = c' * β + d' * α⁻¹ := by
      simp only [cj01, cj11, hγ]; field_simp; ring
    have e3 : cj10 α β γ α⁻¹ a b c' d' = α ^ 2 * c' := by simp only [cj10, hγ]; ring
    have e4 : cj11 α β γ α⁻¹ a b c' d' = α * (c' * β + d' * α⁻¹) := by
      simp only [cj11, hγ]; ring
    have e5 : c' * α + d' * γ = α * c' := by rw [hγ]; ring
    rw [sig, sig, e1, e2, e3, e4, e5, hγ, Xs_zero]
    by_cases hc : c' = 0
    · rw [hc]
      simp only [mul_zero, zero_mul, zero_add, Xs_zero]
      have x1 : d' * α⁻¹ / α⁻¹ = d' := by field_simp
      have x2 : d' * α⁻¹ / (α * (d' * α⁻¹)) = α⁻¹ := by field_simp
      have x3 : d' * α⁻¹ / d' = α⁻¹ := by field_simp
      rw [x1, x2, x3, hdl, hdr]
    · have hαc : α * c' ≠ 0 := mul_ne_zero hα hc
      have x1 : α * c' / α⁻¹ = α ^ 2 * c' := by field_simp
      have x2 : α * c' / (α ^ 2 * c') = α⁻¹ := by field_simp
      have x3 : α * c' / c' = α := by field_simp
      rw [Xs_of_ne _ hαc, Xs_of_ne _ (mul_ne_zero (pow_ne_zero 2 hα) hc), Xs_of_ne _ hc,
        x1, x2, x3, brk_inv_right, brk_mul_left _ (pow_ne_zero 2 hα) hc,
        brk_mul_right _ (pow_ne_zero 2 hα) hc,
        pow_two, brk_mul_left _ hα hα, brk_mul_right _ hα hα, brk_self, one_mul, one_mul, one_mul,
        ← brk_skew]
  · obtain ⟨B, hB⟩ := exists_small_neg hG.ne_bot (α / γ)
    refine ⟨N₀ + B, fun a b c' d' hK => ?_⟩
    have hK' : IsK 𝔪 ((N₀ : ℤ) + B) a b c' d' := by
      have : ((N₀ + B : ℕ) : ℤ) = (N₀ : ℤ) + B := by push_cast; ring
      rwa [this] at hK
    set u : F := d' + c' * (α / γ) with hu
    have hu1 : Small 𝔪 N₀ (u - 1) := by
      have e : u - 1 = (d' - 1) + c' * (α / γ) := by rw [hu]; ring
      rw [e]
      exact (hK'.hd.mono (by omega)).add (Small.mono (by omega) (hK'.hc.mul hB))
    have hu0 : u ≠ 0 := by
      intro h
      have := hu1.val_eq_one hN₀1' v₀ hv₀
      rw [h, map_zero] at this
      exact zero_ne_one this
    have e5 : c' * α + d' * γ = γ * u := by rw [hu]; field_simp; ring
    have e1 : γ * cj00 α β γ δ a b c' d' + δ * cj10 α β γ δ a b c' d' = γ * u := by
      rw [← e5]; simp only [cj00, cj10]; linear_combination (c' * α + d' * γ) * det
    have hγu : γ * u ≠ 0 := mul_ne_zero hγ hu0
    rw [sig, sig, e1, e5, Xs_of_ne _ hγu, Xs_of_ne _ hγu, Xs_of_ne _ hγ,
      show γ * u / γ = u by field_simp, brk_deep_left hG hN₀ _ hu1, brk_deep_right hG hN₀ _ hu1]

end ArtinKP.S2
end
end

section
-- module Solutions.Artin.KP.S2_Translate
/-!
# WP-S2, part 3: genuine sections are stable under `SL₂(F)`, in particular under `SL₂(R)`

* `GSection.translateF α β γ δ` (`αδ - βγ = 1`, entries in `F`):
  `(σ·Φ)_s(p) = σ_S(p, σ)⁻¹ Φ_s(pσ)`.  It is a genuine section: (S1), (S1³) by `sig_smul`, the
  level condition by Kubota's cocycle identity (`sig_cocycle`, twice) and `sig_conj`.
* `GSection.translate σ` for `σ ∈ SL₂(R)`: `κ(σ) · translateF σ`, and
  `twist_translate : twist (translate σ Φ) = TSection.translate σ (twist Φ)` — MATH2 §5.2's `Φ^σ`.
* `translate_mul`: `translate (σ₁ σ₂) Φ = translate σ₁ (translate σ₂ Φ)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S2

open ArtinKP.A ArtinKP.S

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

/-- The symbol identity behind the level condition of a translate. -/
theorem exists_level_sig_mul_sig_conj_eq_oai (hG : Good 𝔪) {α β γ δ : F} (det : α * δ - β * γ = 1) :
    ∃ N : ℕ, ∀ a b c' d' : F, IsK 𝔪 N a b c' d' → ∀ c d : F, c ≠ 0 ∨ d ≠ 0 →
      sig ι P 𝔪 c d α β γ δ * sig ι P 𝔪 (c * α + d * γ) (c * β + d * δ)
          (cj00 α β γ δ a b c' d') (cj01 α β γ δ a b c' d') (cj10 α β γ δ a b c' d')
          (cj11 α β γ δ a b c' d')
        = sig ι P 𝔪 c d a b c' d' * sig ι P 𝔪 (c * a + d * c') (c * b + d * d') α β γ δ := by
  obtain ⟨N, hN⟩ := sig_conj ι P hG det
  refine ⟨N, fun a b c' d' hK c d hcd => ?_⟩
  have detc : cj00 α β γ δ a b c' d' * cj11 α β γ δ a b c' d'
      - cj01 α β γ δ a b c' d' * cj10 α β γ δ a b c' d' = 1 := by
    simp only [cj00, cj01, cj10, cj11]
    linear_combination (a * d' - b * c') * (α * δ - β * γ + 1) * det + hK.det
  have h1 := sig_cocycle (ι := ι) (P := P) hG hcd det detc
  have h2 := sig_cocycle (ι := ι) (P := P) hG hcd hK.det det
  have e00 : α * cj00 α β γ δ a b c' d' + β * cj10 α β γ δ a b c' d' = a * α + b * γ := by
    simp only [cj00, cj10]; linear_combination (a * α + b * γ) * det
  have e01 : α * cj01 α β γ δ a b c' d' + β * cj11 α β γ δ a b c' d' = a * β + b * δ := by
    simp only [cj01, cj11]; linear_combination (a * β + b * δ) * det
  have e10 : γ * cj00 α β γ δ a b c' d' + δ * cj10 α β γ δ a b c' d' = c' * α + d' * γ := by
    simp only [cj00, cj10]; linear_combination (c' * α + d' * γ) * det
  have e11 : γ * cj01 α β γ δ a b c' d' + δ * cj11 α β γ δ a b c' d' = c' * β + d' * δ := by
    simp only [cj01, cj11]; linear_combination (c' * β + d' * δ) * det
  rw [e00, e01, e10, e11, hN a b c' d' hK] at h1
  rw [h1, h2]

end ArtinKP.S2
end
end

theorem solution.{u_1} : type_of% @ArtinKP.S2.exists_level_sig_mul_sig_conj_eq_oai.{u_1} := @ArtinKP.S2.exists_level_sig_mul_sig_conj_eq_oai.{u_1}
