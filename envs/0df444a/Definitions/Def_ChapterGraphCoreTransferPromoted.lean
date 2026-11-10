-- Prove2me | Definitions.Def_ChapterGraphCoreTransferPromoted
-- name    : ChapterGraphCoreTransferPromoted
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-09T10:08:37.052749+00:00
-- url     : https://prove2.me/theorems/2ad34cac-bcd1-4e65-8e12-ccfd5a90575f
-- title:
--   Graph-norm core transfer: IsGraphCore and the transfer principle
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterGraphCoreTransfer.lean`): the platform's served `Def_ChapterGraphCoreTransfer` copy is a skeleton (it declares nothing, so consumers that cite `graphCore_transfer`, `IsGraphCore` and the core-transfer lemmas die with `unknown namespace`/`unknown identifier`), and published bundles are immutable, so the fix is a new bundle name that keeps the original namespace (the new-name route, PIPELINE_PLAN §2.13). This bundle re-carries the chapter's full body in `BookProof.GraphCore`: the graph-norm core predicate `IsGraphCore`, the norm and density estimates that transfer a graph core along an inclusion, and the transfer principle that carries essential self-adjointness from one domain to a graph-norm dense subspace. It imports the promoted Faris-Lavine core bundle, whose declarations the proofs cite. Consumers add a single `import Definitions.Def_ChapterGraphCoreTransferPromoted`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGraphCoreTransfer.lean

-- §2.13 new-name route (Session 40): the platform's served `Def_ChapterGraphCoreTransfer` copy is a
-- skeleton (no declarations at all), so `open BookProof.GraphCore` in every consumer statement
-- dies with `unknown namespace`.  `submit-definition` cannot update an existing
-- name, so this bundle carries the chapter's DEFINITIONS in the original
-- namespace; its theorem facts stay problem nodes.  Consumers add a single
-- `import Definitions.Def_ChapterGraphCoreTransferPromoted`.
import Definitions.Def_ChapterFarisLavineCorePromoted
import Mathlib


/-!
# The core transfer principle: graph-norm density transfers essential self-adjointness

Everywhere in this project essential self-adjointness of a symmetric operator
`T : D →ₗ[ℂ] F` is rendered by the vanishing of the deficiency spaces of the adjoint
(`BookProof.FarisLavine.EssentiallySelfAdjointOn`).  All the criteria available so far
(Faris–Lavine, Nelson-type commutator bounds, …) verify this on the domain on which the
operator is given.  The present module supplies the missing *domain-changing* instrument:

> **Core transfer.**  Let `T₂` be an operator on `D₂` and let `D₁ ≤ D₂` be a subspace which
> is dense in `D₂` for the **graph norm** `‖x‖ + ‖T₂ x‖` of `T₂`.  Then every deficiency
> space of the restriction `T₂|_{D₁}` is contained in the corresponding deficiency space of
> `T₂`; in particular, if `T₂` is essentially self-adjoint on `D₂`, then its restriction to
> `D₁` is essentially self-adjoint on `D₁`.

This is the standard way to handle an operator that is only *essentially* self-adjoint on a
small domain `D`: one never has to make `D` invariant under the unitary group, nor to invert
`A ± i` on `D`.  One works with the self-adjoint (or merely essentially self-adjoint)
operator on the larger domain and transfers the conclusion back along the graph-norm
density.

## Contents

* `IsGraphCore D₁ T` — `D₁` is a core for `T` (graph-norm dense in the domain of `T`).
* `restrictOp` — the restriction of an operator to a smaller domain; `restrictOp_apply`,
  `symmetricOn_restrictOp`.
* `IsGraphCore.refl`, `IsGraphCore.trans` — a domain is a core for its own operator, and
  cores compose.
* `deficiencyTrivialAt_of_graphCore` — the transfer of one deficiency space.
* `essentiallySelfAdjointOn_of_graphCore` — **the core transfer principle.**
* `isGraphCore_of_isometry` — the same notion transported along a linear isometry, which is
  how a core inside an incomplete space becomes a core inside its completion.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.GraphCore

open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-! ## Restriction of an operator to a smaller domain -/

/-- The restriction of `T : D₂ →ₗ[ℂ] F` to a subspace `D₁ ≤ D₂`. -/
def restrictOp {D₁ D₂ : Submodule ℂ F} (T : D₂ →ₗ[ℂ] F) (h : D₁ ≤ D₂) : D₁ →ₗ[ℂ] F :=
  T ∘ₗ Submodule.inclusion h

@[simp] theorem restrictOp_apply {D₁ D₂ : Submodule ℂ F} (T : D₂ →ₗ[ℂ] F) (h : D₁ ≤ D₂)
    (x : D₁) : restrictOp T h x = T ⟨(x : F), h x.2⟩ := rfl

/-- The restriction of a symmetric operator is symmetric. -/
theorem symmetricOn_restrictOp {D₁ D₂ : Submodule ℂ F} (T : D₂ →ₗ[ℂ] F) (h : D₁ ≤ D₂)
    (hT : SymmetricOn D₂ T) : SymmetricOn D₁ (restrictOp T h) :=
  fun x y => hT ⟨(x : F), h x.2⟩ ⟨(y : F), h y.2⟩

/-! ## Cores -/

/-- `D₁` is a **core** for the operator `T` defined on `D₂`: every vector of `D₂` is
approximated, simultaneously in the norm and in the norm of its image under `T` — that is,
in the graph norm of `T` — by vectors of `D₁`.  (The inclusion `D₁ ≤ D₂` is part of the
statement: the approximating vectors are elements of `D₂` that lie in `D₁`.) -/
def IsGraphCore (D₁ : Submodule ℂ F) {D₂ : Submodule ℂ F} (T : D₂ →ₗ[ℂ] F) : Prop :=
  ∀ x : D₂, ∀ ε > 0, ∃ y : D₂, (y : F) ∈ D₁ ∧ ‖(x : F) - (y : F)‖ < ε ∧ ‖T x - T y‖ < ε

/-- The domain of an operator is a core for it. -/
theorem IsGraphCore.refl {D₂ : Submodule ℂ F} (T : D₂ →ₗ[ℂ] F) : IsGraphCore D₂ T :=
  fun x ε hε => ⟨x, x.2, by simpa using hε, by simpa using hε⟩

/-- A core of a core is a core. -/
theorem IsGraphCore.trans {D₁ D₂ D₃ : Submodule ℂ F} {T : D₃ →ₗ[ℂ] F}
    (h₂₃ : D₂ ≤ D₃) (h₁ : IsGraphCore D₁ (restrictOp T h₂₃)) (h₂ : IsGraphCore D₂ T) :
    IsGraphCore D₁ T := by
  intro x ε hε
  obtain ⟨y, hyD₂, hy₁, hy₂⟩ := h₂ x (ε / 2) (by positivity)
  obtain ⟨z, hzD₁, hz₁, hz₂⟩ := h₁ ⟨(y : F), hyD₂⟩ (ε / 2) (by positivity)
  refine ⟨⟨(z : F), h₂₃ z.2⟩, hzD₁, ?_, ?_⟩
  · calc ‖(x : F) - (z : F)‖ ≤ ‖(x : F) - (y : F)‖ + ‖(y : F) - (z : F)‖ := by
          simpa using norm_sub_le_norm_sub_add_norm_sub (x : F) (y : F) (z : F)
      _ < ε / 2 + ε / 2 := by exact add_lt_add hy₁ hz₁
      _ = ε := by ring
  · have hzz : T ⟨(z : F), h₂₃ z.2⟩ = restrictOp T h₂₃ z := rfl
    have hyy : restrictOp T h₂₃ ⟨(y : F), hyD₂⟩ = T y := rfl
    calc ‖T x - T ⟨(z : F), h₂₃ z.2⟩‖
        ≤ ‖T x - T y‖ + ‖T y - T ⟨(z : F), h₂₃ z.2⟩‖ := by
          simpa using norm_sub_le_norm_sub_add_norm_sub (T x) (T y) (T ⟨(z : F), h₂₃ z.2⟩)
      _ < ε / 2 + ε / 2 := by
          refine add_lt_add hy₂ ?_
          rw [hzz, ← hyy]
          exact hz₂
      _ = ε := by ring

/-! ## The transfer -/

/-- **Transfer of a deficiency space along a core.**  If `D₁` is a core for `T` then any
vector annihilating the range of `T|_{D₁} - z̄` annihilates the range of `T - z̄`.  Hence
triviality of the deficiency space of `T` at `z` implies triviality of that of `T|_{D₁}`. -/
theorem deficiencyTrivialAt_of_graphCore {D₁ D₂ : Submodule ℂ F} (T : D₂ →ₗ[ℂ] F)
    (h : D₁ ≤ D₂) (hcore : IsGraphCore D₁ T) {z : ℂ}
    (h₂ : DeficiencyTrivialAt D₂ T z) :
    DeficiencyTrivialAt D₁ (restrictOp T h) z := by
  intro w hw
  refine h₂ w ?_
  intro v
  -- the defect of `v`, which we show to be arbitrarily small
  set c : ℂ := (inner ℂ (T v) w : ℂ) - z * inner ℂ (v : F) w with hc
  have hsmall : ∀ ε > 0, ‖c‖ ≤ ε * (1 + ‖z‖) * ‖w‖ := by
    intro ε hε
    obtain ⟨y, hyD₁, hy₁, hy₂⟩ := hcore v ε hε
    have hy : (inner ℂ (T y) w : ℂ) = z * inner ℂ (y : F) w := by
      have hre : restrictOp T h ⟨(y : F), hyD₁⟩ = T y := rfl
      have := hw ⟨(y : F), hyD₁⟩
      rw [hre] at this
      exact this
    have hcc : c = (inner ℂ (T v - T y) w : ℂ) - z * inner ℂ ((v : F) - (y : F)) w := by
      rw [hc, inner_sub_left, inner_sub_left, hy]; ring
    have h1 : ‖(inner ℂ (T v - T y) w : ℂ)‖ ≤ ε * ‖w‖ := by
      refine le_trans (norm_inner_le_norm (𝕜 := ℂ) _ _) ?_
      exact mul_le_mul_of_nonneg_right hy₂.le (norm_nonneg w)
    have h2 : ‖z * (inner ℂ ((v : F) - (y : F)) w : ℂ)‖ ≤ ‖z‖ * (ε * ‖w‖) := by
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg z)
      refine le_trans (norm_inner_le_norm (𝕜 := ℂ) _ _) ?_
      exact mul_le_mul_of_nonneg_right hy₁.le (norm_nonneg w)
    calc ‖c‖ ≤ ‖(inner ℂ (T v - T y) w : ℂ)‖ + ‖z * (inner ℂ ((v : F) - (y : F)) w : ℂ)‖ := by
          rw [hcc]; exact norm_sub_le _ _
      _ ≤ ε * ‖w‖ + ‖z‖ * (ε * ‖w‖) := add_le_add h1 h2
      _ = ε * (1 + ‖z‖) * ‖w‖ := by ring
  have : c = 0 := by
    by_contra hne
    have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hne
    set M : ℝ := (1 + ‖z‖) * ‖w‖ with hM
    have hMpos : 0 < M := by
      rcases lt_or_eq_of_le (norm_nonneg w) with hw0 | hw0
      · have : 0 < 1 + ‖z‖ := by positivity
        exact mul_pos this hw0
      · exfalso
        have hw' : w = 0 := by
          have : ‖w‖ = 0 := hw0.symm
          exact norm_eq_zero.mp this
        have : c = 0 := by simp [hc, hw']
        exact hne this
    obtain ⟨ε, hε, hεlt⟩ : ∃ ε > 0, ε * M < ‖c‖ :=
      ⟨‖c‖ / (2 * M), by positivity, by
        have hM0 : M ≠ 0 := ne_of_gt hMpos
        have h2 : ‖c‖ / (2 * M) * M = ‖c‖ / 2 := by field_simp
        rw [h2]; linarith⟩
    have := hsmall ε hε
    rw [mul_assoc] at this
    linarith
  rw [hc] at this
  exact sub_eq_zero.mp this

/-- **The core transfer principle.**  An operator which is essentially self-adjoint on `D₂`
is essentially self-adjoint on every core `D₁ ≤ D₂`: no invariance of `D₁` under the unitary
group and no resolvent on `D₁` is needed, only graph-norm density. -/
theorem essentiallySelfAdjointOn_of_graphCore {D₁ D₂ : Submodule ℂ F} (T : D₂ →ₗ[ℂ] F)
    (h : D₁ ≤ D₂) (hcore : IsGraphCore D₁ T)
    (hesa : EssentiallySelfAdjointOn D₂ T) :
    EssentiallySelfAdjointOn D₁ (restrictOp T h) :=
  ⟨deficiencyTrivialAt_of_graphCore T h hcore hesa.1,
    deficiencyTrivialAt_of_graphCore T h hcore hesa.2⟩

/-! ## A criterion: bounded and symmetric on a dense domain

The transfer principle consumes essential self-adjointness on the large domain.  The
following elementary criterion produces it in the bounded case, and is what makes the whole
package non-vacuous: for a densely defined *bounded* symmetric operator the expectation
`⟪T v, v⟫` is real, while the deficiency equation forces a purely imaginary value in the
limit `v → w`; hence `w = 0`. -/

/-- A densely defined bounded symmetric operator has trivial deficiency space at `d i`, for
every real `d ≠ 0`. -/
theorem deficiencyTrivialAt_of_bounded_dense {D : Submodule ℂ F} (T : D →ₗ[ℂ] F)
    (hT : SymmetricOn D T) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x : D, ‖T x‖ ≤ C * ‖(x : F)‖)
    (hdense : Dense (D : Set F)) {d : ℝ} (hd : d ≠ 0) :
    DeficiencyTrivialAt D T ((d : ℂ) * Complex.I) := by
  intro w hw
  have key : ∀ ε > 0, |d| * ‖w‖ ^ 2 ≤ (C * (‖w‖ + 1) + |d| * ‖w‖) * ε := by
    intro ε hε
    set e : ℝ := min ε 1 with he
    have hepos : 0 < e := lt_min hε one_pos
    have hele : e ≤ ε := min_le_left _ _
    obtain ⟨v, hvD, hv⟩ := Metric.mem_closure_iff.mp (hdense w) e hepos
    have hvw : ‖w - v‖ < e := by rw [← dist_eq_norm]; exact hv
    have hvnorm : ‖v‖ ≤ ‖w‖ + 1 := by
      have h1 : ‖v‖ - ‖w‖ ≤ ‖v - w‖ := by simpa using norm_sub_norm_le v w
      have h2 : ‖v - w‖ = ‖w - v‖ := norm_sub_rev v w
      have h3 : e ≤ 1 := min_le_right _ _
      linarith
    have heq := hw ⟨v, hvD⟩
    have hsplit : (inner ℂ (T ⟨v, hvD⟩) w : ℂ)
        = inner ℂ (T ⟨v, hvD⟩) (v : F) + inner ℂ (T ⟨v, hvD⟩) (w - v) := by
      rw [← inner_add_right]; congr 1; abel
    have hreal : (inner ℂ (T ⟨v, hvD⟩) (v : F) : ℂ).im = 0 :=
      inner_apply_self_im T hT ⟨v, hvD⟩
    have hsmall : ‖(inner ℂ (T ⟨v, hvD⟩) (w - v) : ℂ)‖ ≤ C * (‖w‖ + 1) * e := by
      refine le_trans (norm_inner_le_norm (𝕜 := ℂ) _ _) ?_
      have h1 : ‖T ⟨v, hvD⟩‖ ≤ C * (‖w‖ + 1) :=
        le_trans (hC ⟨v, hvD⟩) (mul_le_mul_of_nonneg_left hvnorm hC0)
      exact mul_le_mul h1 hvw.le (norm_nonneg _) (by positivity)
    have hrhs : ((d : ℂ) * Complex.I * inner ℂ (v : F) w : ℂ)
        = (d : ℂ) * Complex.I * (inner ℂ w w) - (d : ℂ) * Complex.I * inner ℂ (w - v) w := by
      rw [← mul_sub, ← inner_sub_left]; congr 2; abel
    have hww : (inner ℂ w w : ℂ) = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; norm_num
    have himL : (inner ℂ (T ⟨v, hvD⟩) w : ℂ).im
        = (inner ℂ (T ⟨v, hvD⟩) (w - v) : ℂ).im := by
      rw [hsplit]; simp [hreal]
    have himR : ((d : ℂ) * Complex.I * inner ℂ (v : F) w : ℂ).im
        = d * ‖w‖ ^ 2 - ((d : ℂ) * Complex.I * inner ℂ (w - v) w : ℂ).im := by
      rw [hrhs, hww]
      simp only [Complex.ofReal_pow, CStarModule.inner_sub_left, inner_self_eq_norm_sq_to_K,
        Complex.coe_algebraMap, Complex.sub_im, Complex.mul_im, Complex.mul_re,
        Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one,
        sub_self, zero_mul, add_zero, zero_add, Complex.sub_re, sub_left_inj,
        mul_eq_mul_left_iff]
      left
      simp [pow_two, Complex.mul_re]
    have hbound2 : ‖((d : ℂ) * Complex.I * inner ℂ (w - v) w : ℂ)‖ ≤ |d| * ‖w‖ * e := by
      rw [norm_mul, norm_mul]
      have h1 : ‖(inner ℂ (w - v) w : ℂ)‖ ≤ e * ‖w‖ :=
        le_trans (norm_inner_le_norm (𝕜 := ℂ) _ _)
          (mul_le_mul_of_nonneg_right hvw.le (norm_nonneg w))
      have hd' : ‖((d : ℂ))‖ = |d| := by simp
      rw [hd']
      simp only [Complex.norm_I, mul_one]
      calc |d| * ‖(inner ℂ (w - v) w : ℂ)‖ ≤ |d| * (e * ‖w‖) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg d)
        _ = |d| * ‖w‖ * e := by ring
    have hfinal : d * ‖w‖ ^ 2
        = (inner ℂ (T ⟨v, hvD⟩) (w - v) : ℂ).im
          + ((d : ℂ) * Complex.I * inner ℂ (w - v) w : ℂ).im := by
      have h := congrArg Complex.im heq
      rw [himL, himR] at h
      linarith
    have h1 : |(inner ℂ (T ⟨v, hvD⟩) (w - v) : ℂ).im| ≤ C * (‖w‖ + 1) * e :=
      le_trans (Complex.abs_im_le_norm _) hsmall
    have h2 : |((d : ℂ) * Complex.I * inner ℂ (w - v) w : ℂ).im| ≤ |d| * ‖w‖ * e :=
      le_trans (Complex.abs_im_le_norm _) hbound2
    have h3 : |d * ‖w‖ ^ 2| ≤ C * (‖w‖ + 1) * e + |d| * ‖w‖ * e := by
      rw [hfinal]
      exact le_trans (abs_add_le _ _) (add_le_add h1 h2)
    have h4 : |d| * ‖w‖ ^ 2 ≤ C * (‖w‖ + 1) * e + |d| * ‖w‖ * e := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖w‖ ^ 2)] at h3
      exact h3
    have hexp : C * (‖w‖ + 1) * e + |d| * ‖w‖ * e
        = (C * (‖w‖ + 1) + |d| * ‖w‖) * e := by ring
    have hmono : (C * (‖w‖ + 1) + |d| * ‖w‖) * e ≤ (C * (‖w‖ + 1) + |d| * ‖w‖) * ε := by
      have hnn : 0 ≤ C * (‖w‖ + 1) + |d| * ‖w‖ := by positivity
      exact mul_le_mul_of_nonneg_left hele hnn
    linarith
  have hzero : ‖w‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hne)
    have hd0 : 0 < |d| := abs_pos.mpr hd
    set K : ℝ := C * (‖w‖ + 1) + |d| * ‖w‖ with hK
    have hKpos : 0 < K := by
      have hA : 0 ≤ C * (‖w‖ + 1) := by positivity
      have hB : 0 < |d| * ‖w‖ := mul_pos hd0 hpos
      simp only [hK]; linarith
    have hgoal : 0 < |d| * ‖w‖ ^ 2 := by positivity
    have hK0 : K ≠ 0 := ne_of_gt hKpos
    have hcalc : ((|d| * ‖w‖ ^ 2) / (2 * K)) * K = (|d| * ‖w‖ ^ 2) / 2 := by field_simp
    have hkey := key ((|d| * ‖w‖ ^ 2) / (2 * K)) (by positivity)
    rw [mul_comm K] at hkey
    linarith
  exact norm_eq_zero.mp hzero

/-- **A densely defined bounded symmetric operator is essentially self-adjoint.** -/
theorem essentiallySelfAdjointOn_of_bounded_dense {D : Submodule ℂ F} (T : D →ₗ[ℂ] F)
    (hT : SymmetricOn D T) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x : D, ‖T x‖ ≤ C * ‖(x : F)‖)
    (hdense : Dense (D : Set F)) :
    EssentiallySelfAdjointOn D T := by
  constructor
  · simpa using deficiencyTrivialAt_of_bounded_dense T hT hC0 hC hdense (d := 1) one_ne_zero
  · simpa using deficiencyTrivialAt_of_bounded_dense T hT hC0 hC hdense (d := -1) (by norm_num)

/-! ## Transport along a linear isometry

A core stays a core when the ambient space is enlarged along a linear isometry — in
particular when an incomplete space is replaced by its completion, which is how the sectors
of a Fock space are built below. -/

section Transport

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- The image of a domain under a linear isometry. -/
def pushDom (U : F →ₗᵢ[ℂ] G) (D : Submodule ℂ F) : Submodule ℂ G :=
  Submodule.map U.toLinearMap D

theorem pushDom_mono (U : F →ₗᵢ[ℂ] G) {D₁ D₂ : Submodule ℂ F} (h : D₁ ≤ D₂) :
    pushDom U D₁ ≤ pushDom U D₂ := Submodule.map_mono h

theorem mem_pushDom (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F} (x : D) :
    U (x : F) ∈ pushDom U D := ⟨(x : F), x.2, rfl⟩

/-- An operator transported along a linear isometry: `U T U⁻¹` on the image domain. -/
noncomputable def pushOp (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F} (T : D →ₗ[ℂ] F) :
    pushDom U D →ₗ[ℂ] G :=
  (U.toLinearMap ∘ₗ T) ∘ₗ
    (Submodule.equivMapOfInjective U.toLinearMap U.injective D).symm.toLinearMap




theorem pushOp_apply (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F} (T : D →ₗ[ℂ] F)
    (x : pushDom U D) (x₀ : D) (hx : (x : G) = U (x₀ : F)) :
    pushOp U T x = U (T x₀) := by
  have hxx : (Submodule.equivMapOfInjective U.toLinearMap U.injective D) x₀ = x := by
    apply Subtype.ext; rw [hx]; rfl
  have h2 : (Submodule.equivMapOfInjective U.toLinearMap U.injective D).symm x = x₀ := by
    rw [← hxx]; simp
  exact congrArg (fun z : D => U (T z)) h2

/-- Transported operators are symmetric if the original one is. -/
theorem symmetricOn_pushOp (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F} (T : D →ₗ[ℂ] F)
    (hT : SymmetricOn D T) : SymmetricOn (pushDom U D) (pushOp U T) := by
  intro x y
  obtain ⟨x₀, hx₀, hxe⟩ := x.2
  obtain ⟨y₀, hy₀, hye⟩ := y.2
  have hx' : (x : G) = U ((⟨x₀, hx₀⟩ : D) : F) := hxe.symm
  have hy' : (y : G) = U ((⟨y₀, hy₀⟩ : D) : F) := hye.symm
  rw [pushOp_apply U T x ⟨x₀, hx₀⟩ hx', pushOp_apply U T y ⟨y₀, hy₀⟩ hy', hx', hy',
    U.inner_map_map, U.inner_map_map]
  exact hT ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩

/-- A core is transported to a core. -/
theorem isGraphCore_pushOp (U : F →ₗᵢ[ℂ] G) {D₁ D₂ : Submodule ℂ F} (T : D₂ →ₗ[ℂ] F)
    (hcore : IsGraphCore D₁ T) : IsGraphCore (pushDom U D₁) (pushOp U T) := by
  intro x ε hε
  obtain ⟨x₀, hx₀, hxe⟩ := x.2
  have hx' : (x : G) = U ((⟨x₀, hx₀⟩ : D₂) : F) := hxe.symm
  obtain ⟨y₀, hy₀D₁, hy₁, hy₂⟩ := hcore ⟨x₀, hx₀⟩ ε hε
  refine ⟨⟨U (y₀ : F), mem_pushDom U y₀⟩, ⟨(y₀ : F), hy₀D₁, rfl⟩, ?_, ?_⟩
  · have hh : (x : G) - U (y₀ : F) = U ((⟨x₀, hx₀⟩ : D₂) - y₀ : F) := by
      rw [map_sub, ← hx']
    rw [hh, U.norm_map]
    exact hy₁
  · rw [pushOp_apply U T x ⟨x₀, hx₀⟩ hx',
      pushOp_apply U T ⟨U (y₀ : F), mem_pushDom U y₀⟩ y₀ rfl, ← map_sub, U.norm_map]
    exact hy₂

end Transport

end BookProof.GraphCore


