-- Prove2me | Definitions.Def_ChapterQgOuterFockFarisLavine
-- name    : ChapterQgOuterFockFarisLavine
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-15T11:44:33.103211+00:00
-- url     : https://prove2.me/theorems/83e317aa-be74-4370-b968-00be831b6c7d
-- title:
--   Faris–Lavine on the outer Fock space: the lifted Friedrichs comparison operator What is proved Honest boundary
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.QgOuterFockFarisLavine`, source chapter `BookProof/ChapterQgOuterFockFarisLavine.lean`): Faris–Lavine on the outer Fock space: the lifted Friedrichs comparison operator What is proved Honest boundary
--
--   `BookProof.ChapterQgOuterFockEsa` proves that the full gauge-fixed gravity Hamiltonian is essentially self-adjoint on the finite-particle core of the outer Fock space `𝔉 = ⊕ₙ L²(ℝ^{84n})`, by the Carleman route sector by sector. This module builds the **Faris–Lavine apparatus on the outer Fock space itself**, with the comparison operator that the strategy calls for: the Friedrichs extension of the positive one-particle operator `N₁ = −Δ + ‖x‖²/4`, lifted to `𝔉`.
--
--   Theorem 1 of Faris–Lavine (`BookProof.ChapterFarisLavine`) needs exactly three things of its comparison operator `N`: symmetry, positivity, and that `N + 1` maps the domain **onto** the space — the one consequence of self-adjointness the argument uses. The point of this module is that all three survive the two constructions the strategy chains together:
--
--   * **Friedrichs.** `friedrichsComparison` packages the Friedrichs extension of `BookProof.ChapterFriedrichsExtension` as such a comparison operator: the extension is built there as `S⁻¹ − 1` for the resolvent `S = (P+1)⁻¹`, so `N + 1` is onto by construction. `Comparison.selfAdjoint` shows conversely that these three properties *are* self-adjointness, so `Comparison.isPositiveSelfAdjointExtension` produces the project's `IsPositiveSelfAdjointExtension` predicate. * **Lifting.** `dsComparison` lifts a family of fibre comparison operators to the `ℓ²`-direct sum, on the maximal domain `dsDom`. Symmetry and positivity are fibrewise (`dsCompOp_hasSum_quadForm`), and surjectivity of `N + 1` lifts because the fibre solutions obey `‖xᵢ‖ ≤ ‖(Nᵢ+1)xᵢ‖ = ‖fᵢ‖` (`norm_le_norm_shift`), so they are automatically square-summable (`dsCompOp_surj`). This is the precise sense in which "the Friedrichs extension of the positive one-particle operator lifts to an operator on the outer Fock space".
--
--   * `Comparison`, `Comparison.selfAdjoint`, `Comparison.isPositiveSelfAdjointExtension`, `Comparison.essentiallySelfAdjointOn`, `Comparison.esa_self` — comparison operators and the Faris–Lavine criterion packaged with one; a comparison operator is essentially self-adjoint on its own domain (the case `H = N`, `c = 0`). * `friedrichsComparison`, `friedrichsComparison_extends` — every densely defined positive symmetric operator has one, namely its Friedrichs extension. * `dsDom`, `dsCompOp`, `dsComparison`, `dsCompOp_surj` — the lift to an `ℓ²`-direct sum. * `dsFibOp`, `dsFibOp_symmetricOn`, `dsFibOp_hasSum_commForm`, `dsFibOp_commForm_le` — a fibrewise symmetric operator on the lifted domain, under a relative bound `‖Hᵢu‖ ≤ K‖(Nᵢ+1)u‖` uniform in the fibre; **the commutator form of the lift is the sum of the fibre commutator forms**, so the Faris–Lavine bound `±i[H,N] ≤ cN` lifts with the *same* constant `c`. * `dsFibOp_essentiallySelfAdjointOn` — **Faris–Lavine on an `ℓ²`-direct sum**: uniform fibre data gives essential self-adjointness of the direct-sum operator on the lifted domain. * `harmPosSym`, `harmFried`, `harmFried_isPositiveSelfAdjointExtension` — the positive one-particle gravity operator `N₁ = −Δ + ‖x‖²/4` and its Friedrichs extension. * `qgOuterComparison`, `qgOuterFriedDom`, `qgOuterFriedN`, `qgOuterFriedN_surj`, `qgOuterCore_le_friedDom`, `qgOuterFriedN_isPositiveSelfAdjointExtension`, `qgOuterFriedN_esa` — **the lifted comparison operator on the outer Fock space**: it is a positive self-adjoint extension of the finite-particle-core operator `dΓ(N₁)` (`qgOuterN`), `𝑁 + 1` is onto `𝔉`, and it is essentially self-adjoint on its domain. * `qgOuterFock_esa_farisLavine` — **the Faris–Lavine theorem for the gravity Hamiltonian on the outer Fock space**: given sector realizations of the `n`-particle Hamiltonians on the domain of the sector comparison operator that are
--
--   ...
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockFarisLavine.lean

import Definitions.Def_ChapterFriedrichsExtension
import Mathlib
import Mathlib
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Theorems.Thm_BookProof_QgHermiteFriedrichs_hamCore_symmetricOn
import Theorems.Thm_BookProof_QgHermiteFriedrichs_hamCore_quadForm_nonneg
open scoped ENNReal
open BookProof.FarisLavine
open BookProof.YangMillsFriedrichs
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.HashimotoShiftInvert
open BookProof.HermiteProductCore
open Classical in
open BookProof.QgHermiteCore
open BookProof.QgHermiteFriedrichs


/-!
# Faris–Lavine on the outer Fock space: the lifted Friedrichs comparison operator

`BookProof.ChapterQgOuterFockEsa` proves that the full gauge-fixed gravity Hamiltonian is
essentially self-adjoint on the finite-particle core of the outer Fock space
`𝔉 = ⊕ₙ L²(ℝ^{84n})`, by the Carleman route sector by sector.  This module builds the
**Faris–Lavine apparatus on the outer Fock space itself**, with the comparison operator
that the strategy calls for: the Friedrichs extension of the positive one-particle
operator `N₁ = −Δ + ‖x‖²/4`, lifted to `𝔉`.

Theorem 1 of Faris–Lavine (`BookProof.ChapterFarisLavine`) needs exactly three things of
its comparison operator `N`: symmetry, positivity, and that `N + 1` maps the domain
**onto** the space — the one consequence of self-adjointness the argument uses.  The point
of this module is that all three survive the two constructions the strategy chains
together:

* **Friedrichs.**  `friedrichsComparison` packages the Friedrichs extension of
  `BookProof.ChapterFriedrichsExtension` as such a comparison operator: the extension is
  built there as `S⁻¹ − 1` for the resolvent `S = (P+1)⁻¹`, so `N + 1` is onto by
  construction.  `Comparison.selfAdjoint` shows conversely that these three properties
  *are* self-adjointness, so `Comparison.isPositiveSelfAdjointExtension` produces the
  project's `IsPositiveSelfAdjointExtension` predicate.
* **Lifting.**  `dsComparison` lifts a family of fibre comparison operators to the
  `ℓ²`-direct sum, on the maximal domain `dsDom`.  Symmetry and positivity are fibrewise
  (`dsCompOp_hasSum_quadForm`), and surjectivity of `N + 1` lifts because the fibre
  solutions obey `‖xᵢ‖ ≤ ‖(Nᵢ+1)xᵢ‖ = ‖fᵢ‖` (`norm_le_norm_shift`), so they are
  automatically square-summable (`dsCompOp_surj`).  This is the precise sense in which
  "the Friedrichs extension of the positive one-particle operator lifts to an operator on
  the outer Fock space".

## What is proved

* `Comparison`, `Comparison.selfAdjoint`, `Comparison.isPositiveSelfAdjointExtension`,
  `Comparison.essentiallySelfAdjointOn`, `Comparison.esa_self` — comparison operators and
  the Faris–Lavine criterion packaged with one; a comparison operator is essentially
  self-adjoint on its own domain (the case `H = N`, `c = 0`).
* `friedrichsComparison`, `friedrichsComparison_extends` — every densely defined positive
  symmetric operator has one, namely its Friedrichs extension.
* `dsDom`, `dsCompOp`, `dsComparison`, `dsCompOp_surj` — the lift to an `ℓ²`-direct sum.
* `dsFibOp`, `dsFibOp_symmetricOn`, `dsFibOp_hasSum_commForm`, `dsFibOp_commForm_le` — a
  fibrewise symmetric operator on the lifted domain, under a relative bound
  `‖Hᵢu‖ ≤ K‖(Nᵢ+1)u‖` uniform in the fibre; **the commutator form of the lift is the sum
  of the fibre commutator forms**, so the Faris–Lavine bound `±i[H,N] ≤ cN` lifts with the
  *same* constant `c`.
* `dsFibOp_essentiallySelfAdjointOn` — **Faris–Lavine on an `ℓ²`-direct sum**: uniform
  fibre data gives essential self-adjointness of the direct-sum operator on the lifted
  domain.
* `harmPosSym`, `harmFried`, `harmFried_isPositiveSelfAdjointExtension` — the positive
  one-particle gravity operator `N₁ = −Δ + ‖x‖²/4` and its Friedrichs extension.
* `qgOuterComparison`, `qgOuterFriedDom`, `qgOuterFriedN`, `qgOuterFriedN_surj`,
  `qgOuterCore_le_friedDom`, `qgOuterFriedN_isPositiveSelfAdjointExtension`,
  `qgOuterFriedN_esa` — **the lifted comparison operator on the outer Fock space**: it is
  a positive self-adjoint extension of the finite-particle-core operator `dΓ(N₁)`
  (`qgOuterN`), `𝑁 + 1` is onto `𝔉`, and it is essentially self-adjoint on its domain.
* `qgOuterFock_esa_farisLavine` — **the Faris–Lavine theorem for the gravity Hamiltonian
  on the outer Fock space**: given sector realizations of the `n`-particle Hamiltonians on
  the domain of the sector comparison operator that are symmetric, relatively bounded by
  `N + 1` and satisfy `±i[H,N] ≤ cN`, all with constants uniform in the particle number,
  the lifted Hamiltonian is essentially self-adjoint on the lifted domain and extends the
  outer Fock Hamiltonian `qgOuterHam` on the finite-particle core.

## Honest boundary

The sector data of `qgOuterFock_esa_farisLavine` are hypotheses, not theorems of this
module: extending the `n`-particle quadratic Hamiltonian from the Gauss–polynomial core to
the *whole* domain of the sector oscillator, with a relative bound and a commutator bound
whose constants do not degrade as the particle number grows, is a separate analytic step
(the Hermite matrix elements of `BookProof.FullQuadratic.fqOp_hermiteCore` are the natural
route to it) and is not carried out here.  What is unconditional here is everything about
the comparison operator — the Friedrichs extension, its lift, and the fact that
Faris–Lavine applies on the outer Fock space once the sector data are supplied, with the
same constant `c` — together with the observation that uniformity in the particle number
is the only thing the lift asks for.  The *unconditional* essential self-adjointness of
the gravity Hamiltonian on the finite-particle core is proved, by the independent Carleman
route, in `BookProof.ChapterQgOuterFockEsa` (`qgOuterFock_esa`).

Everything in this module is `sorry`-free and `axiom`-free.
-/


namespace BookProof.FriedrichsExtension

namespace FormDom

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]



theorem isUniformInducing_toComplL (P : PosSymOp F) :
    IsUniformInducing (UniformSpace.Completion.toComplL (𝕜 := ℂ) (E := FormDom P)) := by
  simpa [UniformSpace.Completion.coe_toComplL] using
    UniformSpace.Completion.isUniformInducing_coe (FormDom P)

@[simp] theorem formExt_coe (P : PosSymOp F) (x : FormDom P) :
    formExt P (x : FormSpace P) = toAmbient x := by
  have := ContinuousLinearMap.extend_eq (incl P) (denseRange_toComplL P)
    (isUniformInducing_toComplL P) x
  simpa [formExt, toAmbient_eq, incl, inclLin, ContinuousLinearMap.coe_coe,
      UniformSpace.Completion.coe_toComplL] using this

theorem inner_coe_eq (P : PosSymOp F) (x : FormDom P) (k : FormSpace P) :
    (inner ℂ (x : FormSpace P) k : ℂ)
      = inner ℂ (toAmbient x + P.op (toDom x)) (formExt P k) := by
  refine UniformSpace.Completion.induction_on k ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro y
    rw [formExt_coe, UniformSpace.Completion.inner_coe, inner_def, inner_add_left,
      toAmbient_eq, toAmbient_eq, P.sym (toDom x) (toDom y)]

theorem formExt_injective (P : PosSymOp F) : Function.Injective (formExt P) := by
  rw [injective_iff_map_eq_zero]
  intro k hk
  have hzero : ∀ y : FormDom P, (inner ℂ (y : FormSpace P) k : ℂ) = 0 := by
    intro y
    rw [inner_coe_eq, hk, inner_zero_right]
  have hall : ∀ z : FormSpace P, (inner ℂ z k : ℂ) = 0 := by
    intro z
    refine UniformSpace.Completion.induction_on z ?_ hzero
    exact isClosed_eq (by fun_prop) (by fun_prop)
  simpa using hall k

theorem dense_range_formExt (P : PosSymOp F) (hdense : Dense (P.dom : Set F)) :
    Dense (Set.range (formExt P)) := by
  refine Dense.mono ?_ hdense
  intro v hv
  exact ⟨((show FormDom P from ⟨v, hv⟩ : FormDom P) : FormSpace P), by rw [formExt_coe]; rfl⟩


@[simp] theorem friedrichsResolvent_apply (P : PosSymOp F) (u : F) :
    friedrichsResolvent P u = formExt P (formRiesz P u) := rfl

theorem inner_friedrichsResolvent (P : PosSymOp F) (u v : F) :
    (inner ℂ u (friedrichsResolvent P v) : ℂ) = inner ℂ (formRiesz P u) (formRiesz P v) := by
  rw [friedrichsResolvent_apply, formRiesz_spec]

theorem friedrichsResolvent_isSelfAdjoint (P : PosSymOp F) :
    IsSelfAdjoint (friedrichsResolvent P) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  simp only [ContinuousLinearMap.coe_coe]
  rw [← inner_conj_symm, inner_friedrichsResolvent, inner_friedrichsResolvent, inner_conj_symm]

theorem friedrichsResolvent_pos (P : PosSymOp F) (u : F) :
    (1 : ℝ) * ‖friedrichsResolvent P u‖ ^ 2
      ≤ (inner ℂ (friedrichsResolvent P u) u : ℂ).re := by
  have h : (inner ℂ (friedrichsResolvent P u) u : ℂ)
      = starRingEnd ℂ (inner ℂ u (friedrichsResolvent P u)) := (inner_conj_symm _ _).symm
  rw [h, inner_friedrichsResolvent]
  have h2 : (inner ℂ (formRiesz P u) (formRiesz P u) : ℂ) = ((‖formRiesz P u‖ ^ 2 : ℝ) : ℂ) := by
    simp [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
  rw [h2]
  simp only [Complex.conj_ofReal, Complex.ofReal_re, one_mul, friedrichsResolvent_apply]
  nlinarith [norm_formExt_apply_le P (formRiesz P u), norm_nonneg (formExt P (formRiesz P u)),
    norm_nonneg (formRiesz P u)]

theorem friedrichsResolvent_injective (P : PosSymOp F) (hdense : Dense (P.dom : Set F)) :
    Function.Injective (friedrichsResolvent P) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  have h0 : formRiesz P u = 0 := formExt_injective P (by simpa using hu)
  have hall : ∀ k : FormSpace P, (inner ℂ u (formExt P k) : ℂ) = 0 := by
    intro k
    rw [← formRiesz_spec, h0, inner_zero_left]
  have hzero : ∀ v : F, (inner ℂ u v : ℂ) = 0 := by
    intro v
    have hc : Continuous fun w : F => (inner ℂ u w : ℂ) := (innerSL ℂ u).continuous
    have heq : Set.EqOn (fun w : F => (inner ℂ u w : ℂ)) (fun _ => (0 : ℂ))
        (Set.range (formExt P)) := by
      rintro _ ⟨k, rfl⟩
      exact hall k
    exact congrFun (Continuous.ext_on (dense_range_formExt P hdense) hc continuous_const heq) v
  simpa using hzero u

end FormDom

end BookProof.FriedrichsExtension


namespace BookProof.HashimotoShiftInvert

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {Dom : Submodule ℂ F}

@[simp] theorem shiftMap_apply (A : Dom →ₗ[ℂ] F) (γ : ℝ) (x : Dom) :
    shiftMap A γ x = A x + (γ : ℂ) • (x : F) := rfl


theorem preim_eq (R : F →L[ℂ] F) (hinj : Function.Injective R)
    (y : LinearMap.range (R : F →ₗ[ℂ] F)) {u : F} (hu : R u = (y : F)) : preim R y = u :=
  hinj (by rw [preim_spec, hu])

@[simp] theorem invShiftOperator_apply (R : F →L[ℂ] F) (hinj : Function.Injective R) (γ : ℝ)
    (y : LinearMap.range (R : F →ₗ[ℂ] F)) :
    invShiftOperator R hinj γ y = preim R y - (γ : ℂ) • (y : F) := rfl

theorem invShiftOperator_symmetricOn (R : F →L[ℂ] F) (hinj : Function.Injective R) (γ : ℝ)
    (hR : IsSelfAdjoint R) :
    SymmetricOn (LinearMap.range (R : F →ₗ[ℂ] F)) (invShiftOperator R hinj γ) := by
  have hRsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hR
  intro y z
  have hy : R (preim R y) = (y : F) := preim_spec R y
  have hz : R (preim R z) = (z : F) := preim_spec R z
  have hcross : (inner ℂ (preim R y) (z : F) : ℂ) = inner ℂ (y : F) (preim R z) := by
    rw [← hy, ← hz]
    exact (hRsym (preim R y) (preim R z)).symm
  simp only [invShiftOperator_apply, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal, hcross]

theorem invShiftOperator_quadForm_nonneg (R : F →L[ℂ] F) (hinj : Function.Injective R) (γ : ℝ)
    (hposR : ∀ u : F, γ * ‖R u‖ ^ 2 ≤ (inner ℂ (R u) u : ℂ).re)
    (y : LinearMap.range (R : F →ₗ[ℂ] F)) : 0 ≤ quadForm (invShiftOperator R hinj γ) y := by
  have hy : R (preim R y) = (y : F) := preim_spec R y
  have hq : quadForm (invShiftOperator R hinj γ) y
      = (inner ℂ (y : F) (preim R y) : ℂ).re - γ * ‖(y : F)‖ ^ 2 := by
    rw [quadForm, invShiftOperator_apply, inner_sub_right, inner_smul_right, Complex.sub_re,
      inner_self_eq_norm_sq_to_K]
    congr 1
    simp [← Complex.ofReal_pow]
  have hp := hposR (preim R y)
  rw [hy] at hp
  rw [hq]
  linarith

end BookProof.HashimotoShiftInvert


namespace BookProof.QgOuterFockFL


noncomputable section

/-! ## 1. Comparison operators for the Faris–Lavine criterion -/

section Abstract

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- A positive symmetric operator obeys `‖x‖ ≤ ‖A x + x‖`: the shift `A + 1` is bounded
below, hence injective. -/
theorem norm_le_norm_shift {D : Submodule ℂ F} (A : D →ₗ[ℂ] F)
    (hpos : ∀ x : D, 0 ≤ quadForm A x) (x : D) : ‖(x : F)‖ ≤ ‖A x + (x : F)‖ := by
  have hre : ‖(x : F)‖ ^ 2 ≤ (inner ℂ (x : F) (A x + (x : F)) : ℂ).re := by
    rw [inner_add_right, Complex.add_re]
    have h1 : (inner ℂ (x : F) ((x : F)) : ℂ).re = ‖(x : F)‖ ^ 2 := by
      simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (x : F)
    have h2 := hpos x
    rw [quadForm] at h2
    linarith
  have hcs : (inner ℂ (x : F) (A x + (x : F)) : ℂ).re ≤ ‖(x : F)‖ * ‖A x + (x : F)‖ := by
    calc (inner ℂ (x : F) (A x + (x : F)) : ℂ).re
        ≤ ‖(inner ℂ (x : F) (A x + (x : F)) : ℂ)‖ := Complex.re_le_norm _
      _ ≤ ‖(x : F)‖ * ‖A x + (x : F)‖ := norm_inner_le_norm _ _
  rcases eq_or_lt_of_le (norm_nonneg (x : F)) with h | h
  · rw [← h]; exact norm_nonneg _
  · nlinarith

/-- **A Faris–Lavine comparison operator**: a positive symmetric operator whose shift
`N + 1` maps the domain onto the whole space.  These are exactly the three properties of
the comparison operator that Theorem 1 of Faris–Lavine uses; by
`comparison_isPositiveSelfAdjointExtension` they say precisely that `N` is a positive
self-adjoint operator. -/
structure Comparison (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F] where
  /-- The domain of the comparison operator. -/
  dom : Submodule ℂ F
  /-- The comparison operator. -/
  op : dom →ₗ[ℂ] F
  /-- It is symmetric. -/
  sym : SymmetricOn dom op
  /-- It is positive. -/
  pos : ∀ x : dom, 0 ≤ quadForm op x
  /-- `N + 1` maps the domain onto the space. -/
  surj : ∀ f : F, ∃ x : dom, op x + (x : F) = f











/-- **The Friedrichs extension is a Faris–Lavine comparison operator.**  Every densely
defined positive symmetric operator has one: the resolvent `S = (P+1)⁻¹` built in
`BookProof.ChapterFriedrichsExtension` inverts the shift by construction. -/
def friedrichsComparison [CompleteSpace F] (P : PosSymOp F) (hdense : Dense (P.dom : Set F)) :
    Comparison F where
  dom := LinearMap.range (friedrichsResolvent P : F →ₗ[ℂ] F)
  op := invShiftOperator (friedrichsResolvent P) (friedrichsResolvent_injective P hdense) 1
  sym := invShiftOperator_symmetricOn _ _ _ (friedrichsResolvent_isSelfAdjoint P)
  pos := invShiftOperator_quadForm_nonneg _ _ _ (friedrichsResolvent_pos P)
  surj := by
    intro f
    have hinj : Function.Injective (friedrichsResolvent P) :=
      friedrichsResolvent_injective P hdense
    refine ⟨⟨friedrichsResolvent P f, ⟨f, rfl⟩⟩, ?_⟩
    have hpre : preim (friedrichsResolvent P) ⟨friedrichsResolvent P f, ⟨f, rfl⟩⟩ = f :=
      preim_eq _ hinj _ rfl
    rw [invShiftOperator_apply, hpre]
    push_cast
    module



end Abstract

/-! ## 2. Lifting a comparison operator to an `ℓ²`-direct sum -/

section Lift

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]

/-- Squares of `ℝ≥0∞`-exponent two are ordinary squares. -/
theorem rpow_two_eq (a : ℝ) : a ^ (2 : ℝ≥0∞).toReal = a ^ (2 : ℕ) := by
  simp [ENNReal.toReal_ofNat]

/-- An operator on a submodule, extended by zero to the whole space. -/
noncomputable def opTot {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {D : Submodule ℂ H} (A : D →ₗ[ℂ] H) (v : H) : H := by
  classical
  exact if h : v ∈ D then A ⟨v, h⟩ else 0

theorem opTot_of_mem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {D : Submodule ℂ H} (A : D →ₗ[ℂ] H) {v : H} (h : v ∈ D) : opTot A v = A ⟨v, h⟩ := by
  classical
  rw [opTot, dif_pos h]

theorem opTot_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {D : Submodule ℂ H} (A : D →ₗ[ℂ] H) : opTot A 0 = 0 := by
  rw [opTot_of_mem A (Submodule.zero_mem D)]
  have hz : (⟨(0 : H), Submodule.zero_mem D⟩ : D) = 0 := rfl
  rw [hz, map_zero]

theorem opTot_add {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {D : Submodule ℂ H} (A : D →ₗ[ℂ] H) {u v : H} (hu : u ∈ D) (hv : v ∈ D) :
    opTot A (u + v) = opTot A u + opTot A v := by
  rw [opTot_of_mem A (Submodule.add_mem D hu hv), opTot_of_mem A hu, opTot_of_mem A hv]
  exact map_add A ⟨u, hu⟩ ⟨v, hv⟩

theorem opTot_smul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {D : Submodule ℂ H} (A : D →ₗ[ℂ] H) (c : ℂ) {v : H} (hv : v ∈ D) :
    opTot A (c • v) = c • opTot A v := by
  rw [opTot_of_mem A (Submodule.smul_mem D c hv), opTot_of_mem A hv]
  exact map_smul A c ⟨v, hv⟩

variable (C : ∀ i, Comparison (G i))

/-- **The domain of the lifted comparison operator**: the vectors of the direct sum whose
fibres lie in the fibre domains and whose images are again square-summable. -/
def dsDom : Submodule ℂ (lp G 2) where
  carrier := {x | (∀ i, (x : ∀ i, G i) i ∈ (C i).dom) ∧
    Memℓp (fun i => opTot (C i).op ((x : ∀ i, G i) i)) 2}
  add_mem' := by
    rintro x y ⟨hx, hxm⟩ ⟨hy, hym⟩
    refine ⟨fun i => by
      simpa only [lp.coeFn_add, Pi.add_apply] using Submodule.add_mem _ (hx i) (hy i), ?_⟩
    have hfun : (fun i => opTot (C i).op (((x + y : lp G 2)) i))
        = (fun i => opTot (C i).op ((x : lp G 2) i))
          + fun i => opTot (C i).op ((y : lp G 2) i) := by
      funext i
      simp only [lp.coeFn_add, Pi.add_apply]
      exact opTot_add _ (hx i) (hy i)
    rw [hfun]
    exact hxm.add hym
  zero_mem' := by
    refine ⟨fun i => by simp, ?_⟩
    have hfun : (fun i => opTot (C i).op (((0 : lp G 2)) i)) = fun i => (0 : G i) := by
      funext i
      have h0 : ((0 : lp G 2) : ∀ i, G i) i = 0 := by simp
      rw [h0]
      exact opTot_zero (C i).op
    rw [hfun]
    exact zero_memℓp
  smul_mem' := by
    rintro a x ⟨hx, hxm⟩
    refine ⟨fun i => by
      simpa only [lp.coeFn_smul, Pi.smul_apply] using Submodule.smul_mem _ a (hx i), ?_⟩
    have hfun : (fun i => opTot (C i).op (((a • x : lp G 2)) i))
        = a • fun i => opTot (C i).op ((x : lp G 2) i) := by
      funext i
      simp only [lp.coeFn_smul, Pi.smul_apply]
      exact opTot_smul _ a (hx i)
    rw [hfun]
    exact hxm.const_smul a



/-- **The lifted comparison operator** `⊕ᵢ Nᵢ`. -/
def dsCompOp : dsDom C →ₗ[ℂ] lp G 2 where
  toFun x := ⟨fun i => opTot (C i).op ((x : lp G 2) i), x.2.2⟩
  map_add' x y := by
    refine lp.ext (funext fun i => ?_)
    change opTot (C i).op (((x + y : dsDom C) : lp G 2) i) = _
    simp only [Submodule.coe_add, lp.coeFn_add, Pi.add_apply]
    exact opTot_add _ (x.2.1 i) (y.2.1 i)
  map_smul' a x := by
    refine lp.ext (funext fun i => ?_)
    change opTot (C i).op (((a • x : dsDom C) : lp G 2) i) = _
    simp only [SetLike.val_smul, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
    exact opTot_smul _ a (x.2.1 i)



/-- The fibre of a domain vector, as an element of the fibre domain. -/
def fib (x : dsDom C) (i : ι) : (C i).dom := ⟨(x : lp G 2) i, x.2.1 i⟩

@[simp] theorem dsCompOp_fib (x : dsDom C) (i : ι) :
    ((dsCompOp C x : lp G 2) : ∀ i, G i) i = (C i).op (fib C x i) :=
  opTot_of_mem _ (x.2.1 i)

theorem dsCompOp_symmetricOn : SymmetricOn (dsDom C) (dsCompOp C) := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun i => ?_
  rw [dsCompOp_fib, dsCompOp_fib]
  exact (C i).sym (fib C x i) (fib C y i)

/-- The quadratic form of the lift is the sum of the fibre quadratic forms. -/
theorem dsCompOp_hasSum_quadForm (x : dsDom C) :
    HasSum (fun i => quadForm (C i).op (fib C x i)) (quadForm (dsCompOp C) x) := by
  have hsum : HasSum (fun i => (inner ℂ ((x : lp G 2) i) ((dsCompOp C x : lp G 2) i) : ℂ))
      (inner ℂ (x : lp G 2) (dsCompOp C x : lp G 2)) := lp.hasSum_inner _ _
  have hre := Complex.reCLM.hasSum hsum
  have hfun : (fun i => Complex.reCLM
        (inner ℂ ((x : lp G 2) i) ((dsCompOp C x : lp G 2) i) : ℂ))
      = fun i => quadForm (C i).op (fib C x i) := by
    funext i
    rw [Complex.reCLM_apply, quadForm, dsCompOp_fib]
    rfl
  rw [hfun] at hre
  exact hre

theorem dsCompOp_quadForm_nonneg (x : dsDom C) : 0 ≤ quadForm (dsCompOp C) x :=
  hasSum_le (fun i => (C i).pos (fib C x i)) hasSum_zero (dsCompOp_hasSum_quadForm C x)

/-- **The shift of the lift is onto.**  Given `f`, solve fibrewise; the solutions are
square-summable because `‖xᵢ‖ ≤ ‖(Nᵢ+1)xᵢ‖ = ‖fᵢ‖`. -/
theorem dsCompOp_surj (f : lp G 2) : ∃ x : dsDom C, dsCompOp C x + (x : lp G 2) = f := by
  choose u hu using fun i => (C i).surj ((f : ∀ i, G i) i)
  have hbound : ∀ i, ‖((u i : G i))‖ ≤ ‖(f : ∀ i, G i) i‖ := by
    intro i
    have := norm_le_norm_shift (C i).op (C i).pos (u i)
    rwa [hu i] at this
  have hmem : Memℓp (fun i => ((u i : G i))) 2 := by
    refine memℓp_gen ?_
    have hfs : Summable (fun i => ‖(f : ∀ i, G i) i‖ ^ (2 : ℝ≥0∞).toReal) :=
      (lp.memℓp f).summable (by norm_num)
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) hfs
    rw [rpow_two_eq, rpow_two_eq]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbound i) 2
  set x : lp G 2 := ⟨fun i => ((u i : G i)), hmem⟩ with hxdef
  have hxfib : ∀ i, (x : ∀ i, G i) i = (u i : G i) := fun i => rfl
  have hxmem : x ∈ dsDom C := by
    refine ⟨fun i => by rw [hxfib]; exact (u i).2, ?_⟩
    have hfun : (fun i => opTot (C i).op ((x : ∀ i, G i) i))
        = fun i => (f : ∀ i, G i) i - (x : ∀ i, G i) i := by
      funext i
      rw [hxfib, opTot_of_mem _ (u i).2]
      have : (⟨(u i : G i), (u i).2⟩ : (C i).dom) = u i := Subtype.ext rfl
      rw [this, ← hu i]
      abel
    rw [hfun]
    have hsub := lp.memℓp (f - x)
    have hcoe : ((f - x : lp G 2) : ∀ i, G i)
        = fun i => (f : ∀ i, G i) i - (x : ∀ i, G i) i := funext fun i => by simp
    rw [hcoe] at hsub
    exact hsub
  refine ⟨⟨x, hxmem⟩, ?_⟩
  refine lp.ext (funext fun i => ?_)
  simp only [lp.coeFn_add, Pi.add_apply]
  rw [dsCompOp_fib]
  have hfibx : fib C ⟨x, hxmem⟩ i = u i := Subtype.ext (hxfib i)
  rw [hfibx, hxfib]
  exact hu i

/-- **The lift of a family of comparison operators is a comparison operator.**  This is
the step the Faris–Lavine strategy needs: positivity, symmetry and — crucially —
invertibility of `N + 1` all survive the passage to the `ℓ²`-direct sum. -/
def dsComparison : Comparison (lp G 2) where
  dom := dsDom C
  op := dsCompOp C
  sym := dsCompOp_symmetricOn C
  pos := dsCompOp_quadForm_nonneg C
  surj := dsCompOp_surj C

/-! ### The commutator form of a fibrewise operator -/

variable (H : ∀ i, (C i).dom →ₗ[ℂ] G i)

/-- The fibrewise operator `⊕ᵢ Hᵢ` on the lifted domain, under a uniform relative bound
`‖Hᵢ u‖ ≤ K‖(Nᵢ+1)u‖` — the bound that makes the image square-summable. -/
def dsFibOp (K : ℝ) (hrel : ∀ (i : ι) (u : (C i).dom), ‖H i u‖ ≤ K * ‖(C i).op u + (u : G i)‖) :
    dsDom C →ₗ[ℂ] lp G 2 where
  toFun x := ⟨fun i => opTot (H i) ((x : lp G 2) i), by
    refine memℓp_gen ?_
    have hbig := lp.memℓp (dsCompOp C x + (x : lp G 2))
    have hcoe : ((dsCompOp C x + (x : lp G 2) : lp G 2) : ∀ i, G i)
        = fun i => (dsCompOp C x : lp G 2) i + (x : lp G 2) i := funext fun i => by simp
    rw [hcoe] at hbig
    have hs : Summable (fun i => ‖(dsCompOp C x : lp G 2) i + (x : lp G 2) i‖
        ^ (2 : ℝ≥0∞).toReal) := hbig.summable (by norm_num)
    have hsK : Summable (fun i => (K ^ 2) * ‖(dsCompOp C x : lp G 2) i + (x : lp G 2) i‖
        ^ (2 : ℝ≥0∞).toReal) := hs.mul_left _
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) hsK
    rw [rpow_two_eq, rpow_two_eq]
    have hval : opTot (H i) ((x : lp G 2) i) = H i (fib C x i) := opTot_of_mem _ (x.2.1 i)
    have hshift : (C i).op (fib C x i) + ((fib C x i : G i))
        = (dsCompOp C x : lp G 2) i + (x : lp G 2) i := by
      rw [dsCompOp_fib]
      rfl
    have hb := hrel i (fib C x i)
    rw [hshift] at hb
    rw [hval]
    calc ‖H i (fib C x i)‖ ^ 2
        ≤ (K * ‖(dsCompOp C x : lp G 2) i + (x : lp G 2) i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ = K ^ 2 * ‖(dsCompOp C x : lp G 2) i + (x : lp G 2) i‖ ^ 2 := by ring⟩
  map_add' x y := by
    refine lp.ext (funext fun i => ?_)
    change opTot (H i) (((x + y : dsDom C) : lp G 2) i) = _
    simp only [Submodule.coe_add, lp.coeFn_add, Pi.add_apply]
    exact opTot_add _ (x.2.1 i) (y.2.1 i)
  map_smul' a x := by
    refine lp.ext (funext fun i => ?_)
    change opTot (H i) (((a • x : dsDom C) : lp G 2) i) = _
    simp only [SetLike.val_smul, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
    exact opTot_smul _ a (x.2.1 i)

variable {C H}











end Lift

/-! ## 3. The quantum-gravity outer Fock space -/

open BookProof.QgHermiteCore
open BookProof.QgHermiteFriedrichs

variable {d : ℕ}

/-- The **positive one-particle operator** `N₁ = −Δ + ‖x‖²/4` of the gravity sector, as a
densely defined positive symmetric operator on `L²(ℝᵈ)`. -/
def harmW (x : Vd d) : ℝ := ‖x‖ ^ 2 / 4

theorem continuous_harmW : Continuous (harmW (d := d)) := by
  unfold harmW
  fun_prop

theorem expBounded_harmW : ExpBounded (harmW (d := d)) := by
  refine ⟨1, 1, zero_le_one, fun x => ?_⟩
  have h := Real.pow_div_factorial_le_exp ‖x‖ (norm_nonneg x) 2
  have hfac : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num
  rw [hfac] at h
  have hpos : (0 : ℝ) ≤ harmW x := by
    unfold harmW; positivity
  rw [abs_of_nonneg hpos, one_mul, one_mul]
  unfold harmW
  nlinarith [sq_nonneg ‖x‖]

def harmCore : (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  hamCore harmW continuous_harmW expBounded_harmW

theorem harmonicCore_symmetricOn : SymmetricOn (polyGaussCore (d := d)) harmCore :=
  hamCore_symmetricOn harmW continuous_harmW expBounded_harmW

theorem harmonicCore_quadForm_nonneg (x : polyGaussCore (d := d)) : 0 ≤ quadForm harmCore x :=
  hamCore_quadForm_nonneg harmW continuous_harmW expBounded_harmW
    (fun x => by unfold harmW; positivity) x


def harmPosSym (d : ℕ) : PosSymOp (L2d d) where
  dom := polyGaussCore (d := d)
  op := harmCore
  sym := harmonicCore_symmetricOn
  pos := harmonicCore_quadForm_nonneg

/-- **The Friedrichs extension of the positive one-particle operator**, as a Faris–Lavine
comparison operator: positive, self-adjoint, and with `N₁ + 1` onto `L²(ℝᵈ)`. -/
def harmFried (d : ℕ) : Comparison (L2d d) :=
  friedrichsComparison (harmPosSym d) polyGaussCore_dense







/-- **The lift of the one-particle comparison operator to the outer Fock space**: the
`ℓ²`-direct sum `⊕ₙ N₁^{(n)}` of the sector realizations of the Friedrichs extension.  It
is again positive, self-adjoint and has `𝑁 + 1` onto the whole outer Fock space, so it is
an admissible Faris–Lavine comparison operator there. -/
abbrev qgOuterFock := lp (fun n : ℕ => L2d (n * 84)) 2

def qgOuterComparison : Comparison qgOuterFock :=
  dsComparison (fun n : ℕ => harmFried (n * 84))

/-- The domain of the lifted comparison operator. -/
abbrev qgOuterFriedDom : Submodule ℂ qgOuterFock := qgOuterComparison.dom

/-- The lifted comparison operator `dΓ(N₁)` on the outer Fock space. -/
abbrev qgOuterFriedN : qgOuterFriedDom →ₗ[ℂ] qgOuterFock := qgOuterComparison.op

















end

end BookProof.QgOuterFockFL


