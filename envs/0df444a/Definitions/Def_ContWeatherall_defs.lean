-- Prove2me | Definitions.Def_ContWeatherall_defs
-- name    : ContWeatherall_defs
-- status  : Definition
-- author  : @Alien60
-- created : 2026-10-14T21:57:28.635559+00:00
-- url     : https://prove2.me/theorems/b36b1a9c-712c-4ebb-87e3-69ac04ec790b
-- title:
--   Differential forms on a normed space, the radial homotopy operator, and the categories of potentials and field strengths
-- statement:
--   On a real normed space $E$ with values in a real normed space $F$: the radial homotopy operator `homotopyOp` $(K\omega)(x)(v)=\int_0^1 t^k\,\omega(tx)(x,v)\,dt$ (for complete $F$); a function as a 0-form (`zeroForm`) and its exterior derivative `grad` $=d\chi$; proved helper facts (smoothness of `extDeriv`, $d^2=0$, additivity of `grad`, $d(A+d\chi)=dA$); the elementary conditions `H0Vanishes`, `H1Vanishes`, `H2Vanishes P`; the discrete category `Fld P` of smooth closed 2-forms satisfying a field-equation predicate $P$ (Weatherall's EM1); the category `Pot P` of smooth potentials with $P(dA)$ and smooth gauge arrows $A+d\chi=A'$ (EM2 with gauge arrows, fn. 15); and the functor `fieldStrength P`, $A\mapsto dA$. Metric-free: no Hodge star.
-- source:
--   J. O. Weatherall, Understanding Gauge, Philos. Sci. 83 (2016) 1039-1049, https://arxiv.org/abs/1505.02229 (page numbers refer to arXiv v2), §4 pp. 7-11 (EM1, EM2, fn. 15; erratum p. 15); M. Spivak, Calculus on Manifolds (W. A. Benjamin, 1965), Theorem 4-11 (Poincaré lemma) and its proof

import Mathlib

/-!
# Continuum Weatherall: potentials vs. field strengths on a normed space

Continuum twin of `WeatherallGauge` (J. O. Weatherall, "Understanding Gauge", Philos. Sci. 83
(2016), §4, arXiv:1505.02229). Spacetime is a real normed space `E` (e.g. `ℝⁿ`), fields take
values in a real Banach space `F`, and differential forms are Mathlib's
`E → E [⋀^Fin k]→L[ℝ] F` with exterior derivative `extDeriv`. "Smooth" means `ContDiff ℝ ∞`.
Everything is metric-free: no Hodge star is used. Field equations (e.g. Maxwell's inhomogeneous
equation, once a metric is chosen) enter only through an arbitrary predicate `P` on 2-forms.

* `homotopyOp w` — the radial homotopy operator `(Kw)(x)(v) = ∫₀¹ tᵏ w(t x)(x, v) dt`.
* `zeroForm`, `grad` — a function `χ : E → F` as a 0-form, and its exterior derivative `dχ`.
* `H0Vanishes`, `H1Vanishes`, `H2Vanishes` — elementary forms of `H⁰ = 0`, `H¹ = 0`, `H² = 0`.
* `Pot P` — potentials (smooth 1-forms `A` with `P (dA)`), arrows `A ⟶ A'` the smooth gauge
  functions `χ` with `A + dχ = A'`.
* `Fld P` — field strengths (smooth closed 2-forms satisfying `P`), only identity arrows.
* `fieldStrength P : Pot P ⥤ Fld P` — the functor `A ↦ dA`.
-/

open CategoryTheory ContinuousAlternatingMap
open scoped ContDiff

namespace ContWeatherall

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The radial homotopy operator: for a `(k+1)`-form `w`,
`(homotopyOp w)(x)(v₁,…,v_k) = ∫₀¹ tᵏ · w(t • x)(x, v₁, …, v_k) dt`. -/
noncomputable def homotopyOp [CompleteSpace F] {k : ℕ} (w : E → E [⋀^Fin (k + 1)]→L[ℝ] F)
    (x : E) : E [⋀^Fin k]→L[ℝ] F :=
  ∫ t in (0 : ℝ)..1, t ^ k • (w (t • x)).curryLeft x

/-- A function `χ : E → F` viewed as a differential 0-form. -/
noncomputable def zeroForm (χ : E → F) : E → E [⋀^Fin 0]→L[ℝ] F :=
  fun x => constOfIsEmpty ℝ E (Fin 0) (χ x)

/-- The exterior derivative `dχ` of a function `χ : E → F`, a 1-form. -/
noncomputable def grad (χ : E → F) : E → E [⋀^Fin 1]→L[ℝ] F :=
  extDeriv (zeroForm χ)

theorem grad_apply (χ : E → F) (x : E) :
    grad χ x = ofSubsingleton ℝ E F (0 : Fin 1) (fderiv ℝ χ x) :=
  extDeriv_constOfIsEmpty χ x

theorem zeroForm_contDiff {χ : E → F} (h : ContDiff ℝ ∞ χ) : ContDiff ℝ ∞ (zeroForm χ) :=
  (constOfIsEmptyLIE ℝ E F (Fin 0)).contDiff.comp h

theorem extDeriv_contDiff {n : ℕ} {w : E → E [⋀^Fin n]→L[ℝ] F} (h : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (extDeriv w) := by
  have e : extDeriv w = fun x => alternatizeUncurryFinCLM ℝ E F (fderiv ℝ w x) := by
    funext x; simp [extDeriv]
  rw [e]
  exact (alternatizeUncurryFinCLM ℝ E F).contDiff.comp (contDiff_infty_iff_fderiv.1 h).2

theorem extDeriv_extDeriv_eq_zero {n : ℕ} {w : E → E [⋀^Fin n]→L[ℝ] F}
    (h : ContDiff ℝ ∞ w) : extDeriv (extDeriv w) = 0 :=
  extDeriv_extDeriv h (by
    rw [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out)

theorem grad_contDiff {χ : E → F} (h : ContDiff ℝ ∞ χ) : ContDiff ℝ ∞ (grad χ) :=
  extDeriv_contDiff (zeroForm_contDiff h)

theorem extDeriv_grad {χ : E → F} (h : ContDiff ℝ ∞ χ) : extDeriv (grad χ) = 0 :=
  extDeriv_extDeriv_eq_zero (zeroForm_contDiff h)

theorem grad_zero : grad (0 : E → F) = 0 := by
  funext x; ext v; simp [grad_apply]

theorem grad_add {χ₁ χ₂ : E → F} (h₁ : Differentiable ℝ χ₁) (h₂ : Differentiable ℝ χ₂) :
    grad (χ₁ + χ₂) = grad χ₁ + grad χ₂ := by
  funext x; ext v; simp [grad_apply, fderiv_add (h₁ x) (h₂ x)]

theorem extDeriv_add_grad {A : E → E [⋀^Fin 1]→L[ℝ] F} {χ : E → F} (hA : ContDiff ℝ ∞ A)
    (hχ : ContDiff ℝ ∞ χ) : extDeriv (A + grad χ) = extDeriv A := by
  funext x
  rw [extDeriv_add (hA.differentiable (by simp) x)
    ((grad_contDiff hχ).differentiable (by simp) x), extDeriv_grad hχ]
  simp

/-! ### Elementary cohomology-vanishing conditions -/

/-- `H⁰ = 0`: a smooth function with `dχ = 0` is zero. -/
def H0Vanishes (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : Prop :=
  ∀ χ : E → F, ContDiff ℝ ∞ χ → grad χ = 0 → χ = 0

/-- `H¹ = 0`: every smooth closed 1-form is `dχ` for a smooth function `χ`. -/
def H1Vanishes (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : Prop :=
  ∀ A : E → E [⋀^Fin 1]→L[ℝ] F, ContDiff ℝ ∞ A → extDeriv A = 0 →
    ∃ χ : E → F, ContDiff ℝ ∞ χ ∧ grad χ = A

/-- `H² = 0` on the `P`-sector: every smooth closed 2-form satisfying `P` is `dA` for a smooth
1-form `A`. -/
def H2Vanishes (P : (E → E [⋀^Fin 2]→L[ℝ] F) → Prop) : Prop :=
  ∀ B : E → E [⋀^Fin 2]→L[ℝ] F, ContDiff ℝ ∞ B → extDeriv B = 0 → P B →
    ∃ A : E → E [⋀^Fin 1]→L[ℝ] F, ContDiff ℝ ∞ A ∧ extDeriv A = B

/-! ### The categories -/

/-- Weatherall's EM1 with field equations `P`: smooth closed 2-forms satisfying `P`, with only
identity arrows. -/
abbrev Fld (P : (E → E [⋀^Fin 2]→L[ℝ] F) → Prop) :=
  Discrete {B : E → E [⋀^Fin 2]→L[ℝ] F // ContDiff ℝ ∞ B ∧ extDeriv B = 0 ∧ P B}

/-- Potentials whose field strength satisfies `P`. -/
structure Pot (P : (E → E [⋀^Fin 2]→L[ℝ] F) → Prop) where
  /-- The underlying 1-form. -/
  pot : E → E [⋀^Fin 1]→L[ℝ] F
  smooth : ContDiff ℝ ∞ pot
  field_eq : P (extDeriv pot)

/-- Gauge transformations from `A` to `A'`: smooth `χ : E → F` with `A + dχ = A'`. -/
@[ext]
structure GaugeHom {P : (E → E [⋀^Fin 2]→L[ℝ] F) → Prop} (A A' : Pot P) where
  /-- The gauge function. -/
  chi : E → F
  smooth : ContDiff ℝ ∞ chi
  eq : A.pot + grad chi = A'.pot

instance (P : (E → E [⋀^Fin 2]→L[ℝ] F) → Prop) : Category (Pot P) where
  Hom := GaugeHom
  id A := ⟨0, contDiff_const, by rw [grad_zero, add_zero]⟩
  comp f g := ⟨f.chi + g.chi, f.smooth.add g.smooth, by
    rw [grad_add (f.smooth.differentiable (by simp)) (g.smooth.differentiable (by simp)),
      ← add_assoc, f.eq, g.eq]⟩
  id_comp f := GaugeHom.ext (zero_add _)
  comp_id f := GaugeHom.ext (add_zero _)
  assoc f g h := GaugeHom.ext (add_assoc _ _ _)

/-- The field-strength functor `A ↦ dA`; a gauge arrow goes to the identity, since
`d(A + dχ) = dA`. -/
noncomputable def fieldStrength (P : (E → E [⋀^Fin 2]→L[ℝ] F) → Prop) : Pot P ⥤ Fld P where
  obj A := Discrete.mk ⟨extDeriv A.pot, extDeriv_contDiff A.smooth,
    extDeriv_extDeriv_eq_zero A.smooth, A.field_eq⟩
  map {A A'} f := Discrete.eqToHom (Subtype.ext (by
    show extDeriv A.pot = extDeriv A'.pot
    rw [← f.eq, extDeriv_add_grad A.smooth f.smooth]))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

end ContWeatherall


