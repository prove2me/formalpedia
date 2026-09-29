-- Prove2me | Definitions.Def_ChapterFriedrichsExtension
-- name    : ChapterFriedrichsExtension
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T00:02:14.867904+00:00
-- url     : https://prove2.me/theorems/ee86dd24-83f0-446e-b416-752e1fd21185
-- title:
--   `CONSOLIDATED_PLAN.md` §11.4 records two plan items that stand between the proved Hashimoto/shift-invert machinery and t ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.FriedrichsExtension`, source chapter `BookProof/ChapterFriedrichsExtension.lean`).
--
--   `CONSOLIDATED_PLAN.md` §11.4 records two plan items that stand between the proved Hashimoto/shift-invert machinery and the full claim *"the unbounded continuum Weyl-gauge Hamiltonian has a Friedrichs extension, and the infinite Hashimoto/SIRK limit selects exactly it"*. This module closes the first one.
--
--   Until now the Friedrichs theorem entered the project in two forms:
--
--   * as a **named hypothesis** (`BookProof.YangMillsFriedrichs.friedrichs_extension_of_semibounded`), shown consistent only for an operator already defined on the whole space; * **discharged by construction, but only in the bounded regime** (`BookProof.YangMillsFriedrichsLimit.friedrichs_of_bounded`: a densely defined symmetric positive operator with `‖H x‖ ≤ C‖x‖` extends continuously).
--
--   Here the theorem is **proved with no boundedness hypothesis at all**: every densely defined, symmetric, positive operator on a complex Hilbert space has a positive self-adjoint extension. The construction is the classical one, carried out in full:
--
--   **Part A — the form space.** The domain carries the *form inner product* `⟪x, y⟫₁ = ⟪x, y⟫ + ⟪x, H y⟫`. Symmetry makes it Hermitian and positivity makes it positive definite (indeed `‖x‖ ≤ ‖x‖₁`), so `FormDom P` — the domain retyped with that inner product — is an inner product space (`instCore`, `instIPS`), and `FormSpace P`, its completion, is a Hilbert space.
--
--   **Part B — the form space sits inside `F`.** The inclusion `FormDom P → F` is norm-decreasing, so it extends to `formExt P : FormSpace P →L[ℂ] F`. The key identity `inner_coe_eq` — `⟪x, k⟫₁ = ⟪x + H x, formExt k⟫` for a domain vector `x` — is the closability of the form in disguise, and it gives `formExt_injective`: *the form completion adds no ghost vectors*. This is the one place where symmetry and positivity of `H` do analytic work.
--
--   **Part C — Riesz representation.** For `u : F` the functional `k ↦ ⟪u, formExt k⟫` is continuous on the Hilbert space `FormSpace P`, so it is represented by a vector `formRiesz P u`, and `friedrichsResolvent P u = formExt P (formRiesz P u)` is a bounded, injective, positive, self-adjoint operator on `F` with `‖·‖ ≤ 1`. It is `(H + 1)⁻¹` on the nose: `friedrichsResolvent_shift` proves `S (x + H x) = x` for every `x` in the domain.
--
--   **Part D — the extension.** Feeding `S` to the project's own converse construction `BookProof.HashimotoShiftInvert.invShiftOperator` (`A = S⁻¹ − 1`) produces the extension, and `friedrichs_extension_exists` states it in the form the rest of the project consumes, `BookProof.YangMillsFriedrichs.IsPositiveSelfAdjointExtension`. Consequences:
--
--   * `friedrichs_hypothesis_holds` — the named hypothesis of `friedrichs_extension_of_semibounded` is a theorem, not an assumption; * `friedrichs_extension_of_semibounded_below` — the classical statement, for a symmetric operator that is merely *bounded below* (`⟪x, Hx⟫ ≥ −c‖x‖²`), by the shift `H ↦ H + c`; * `weyl_friedrichs_extension_unconditional` — the Weyl-gauge Yang–Mills Hamiltonian `½ Σ πᵢ² + ½ Σ Bₐ²` on any dense domain has a Friedrichs extension, with **no boundedness hypothesis** (plan item §11.4.1); * `weyl_hashimoto_selects_friedrichs` — combining with `hashimoto_shiftInvert_selects_friedrichs`: in the occupation-number (Hermite) realization the extension *exists* and the Hashimoto/SIRK algorithm converges to it and to nothing else; * `unbounded_friedrichs_example` — the construction applied to a genuinely unbounded operator (`A eₙ = n eₙ` on `ℓ²(ℕ, ℂ)`, restricted to the finite-mode domain), so nothing here is vacuous.
--
--   This is the abstract Friedrichs theorem and its application to the Weyl-gauge Hamiltonian *as an operator on a Hilbert space*. It does **not** claim the mass gap, nor a differential (field-space) realization of the magnetic-field operator `B_{i a}` — that is the second, definitional item of §11.4,
--
--   ...
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFriedrichsExtension.lean

import Definitions.Def_ChapterHashimotoShiftInvert
import Mathlib

import Mathlib

/-!
# The Friedrichs extension of an **unbounded** positive symmetric operator

`CONSOLIDATED_PLAN.md` §11.4 records two plan items that stand between the proved
Hashimoto/shift-invert machinery and the full claim *"the unbounded continuum
Weyl-gauge Hamiltonian has a Friedrichs extension, and the infinite
Hashimoto/SIRK limit selects exactly it"*.  This module closes the first one.

Until now the Friedrichs theorem entered the project in two forms:

* as a **named hypothesis**
  (`BookProof.YangMillsFriedrichs.friedrichs_extension_of_semibounded`), shown
  consistent only for an operator already defined on the whole space;
* **discharged by construction, but only in the bounded regime**
  (`BookProof.YangMillsFriedrichsLimit.friedrichs_of_bounded`: a densely defined
  symmetric positive operator with `‖H x‖ ≤ C‖x‖` extends continuously).

Here the theorem is **proved with no boundedness hypothesis at all**: every
densely defined, symmetric, positive operator on a complex Hilbert space has a
positive self-adjoint extension.  The construction is the classical one, carried
out in full:

**Part A — the form space.**  The domain carries the *form inner product*
`⟪x, y⟫₁ = ⟪x, y⟫ + ⟪x, H y⟫`.  Symmetry makes it Hermitian and positivity makes
it positive definite (indeed `‖x‖ ≤ ‖x‖₁`), so `FormDom P` — the domain retyped
with that inner product — is an inner product space (`instCore`, `instIPS`), and
`FormSpace P`, its completion, is a Hilbert space.

**Part B — the form space sits inside `F`.**  The inclusion `FormDom P → F` is
norm-decreasing, so it extends to `formExt P : FormSpace P →L[ℂ] F`.  The key
identity `inner_coe_eq` — `⟪x, k⟫₁ = ⟪x + H x, formExt k⟫` for a domain vector
`x` — is the closability of the form in disguise, and it gives
`formExt_injective`: *the form completion adds no ghost vectors*.  This is the
one place where symmetry and positivity of `H` do analytic work.

**Part C — Riesz representation.**  For `u : F` the functional
`k ↦ ⟪u, formExt k⟫` is continuous on the Hilbert space `FormSpace P`, so it is
represented by a vector `formRiesz P u`, and
`friedrichsResolvent P u = formExt P (formRiesz P u)` is a bounded, injective,
positive, self-adjoint operator on `F` with `‖·‖ ≤ 1`.  It is `(H + 1)⁻¹` on the
nose: `friedrichsResolvent_shift` proves `S (x + H x) = x` for every `x` in the
domain.

**Part D — the extension.**  Feeding `S` to the project's own converse
construction `BookProof.HashimotoShiftInvert.invShiftOperator` (`A = S⁻¹ − 1`)
produces the extension, and `friedrichs_extension_exists` states it in the form
the rest of the project consumes,
`BookProof.YangMillsFriedrichs.IsPositiveSelfAdjointExtension`.  Consequences:

* `friedrichs_hypothesis_holds` — the named hypothesis of
  `friedrichs_extension_of_semibounded` is a theorem, not an assumption;
* `friedrichs_extension_of_semibounded_below` — the classical statement, for a
  symmetric operator that is merely *bounded below* (`⟪x, Hx⟫ ≥ −c‖x‖²`), by the
  shift `H ↦ H + c`;
* `weyl_friedrichs_extension_unconditional` — the Weyl-gauge Yang–Mills
  Hamiltonian `½ Σ πᵢ² + ½ Σ Bₐ²` on any dense domain has a Friedrichs
  extension, with **no boundedness hypothesis** (plan item §11.4.1);
* `weyl_hashimoto_selects_friedrichs` — combining with
  `hashimoto_shiftInvert_selects_friedrichs`: in the occupation-number (Hermite)
  realization the extension *exists* and the Hashimoto/SIRK algorithm converges
  to it and to nothing else;
* `unbounded_friedrichs_example` — the construction applied to a genuinely
  unbounded operator (`A eₙ = n eₙ` on `ℓ²(ℕ, ℂ)`, restricted to the finite-mode
  domain), so nothing here is vacuous.

## Scope

This is the abstract Friedrichs theorem and its application to the Weyl-gauge
Hamiltonian *as an operator on a Hilbert space*.  It does **not** claim the mass
gap, nor a differential (field-space) realization of the magnetic-field operator
`B_{i a}` — that is the second, definitional item of §11.4, settled there in
favour of the occupation-number/Hermite realization.
-/

namespace BookProof.FriedrichsExtension

open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- A **densely definable positive symmetric operator**, bundled so that the form
inner product can be attached to its domain as a type-class structure. -/
structure PosSymOp (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F] where
  /-- The domain of the operator. -/
  dom : Submodule ℂ F
  /-- The operator itself. -/
  op : dom →ₗ[ℂ] F
  /-- The operator is symmetric on its domain. -/
  sym : SymmetricOn dom op
  /-- The operator is positive: its quadratic form is nonnegative. -/
  pos : ∀ x : dom, 0 ≤ quadForm op x

theorem re_inner_self (v : F) : (inner ℂ v v : ℂ).re = ‖v‖ ^ 2 := by
  simp [← Complex.ofReal_pow]

/-! ## Part A — the domain with its form inner product -/

/-- The domain of `P`, retyped so that it carries the **form inner product**
`⟪x, y⟫₁ = ⟪x, y⟫ + ⟪x, H y⟫` instead of the ambient one. -/
def FormDom (P : PosSymOp F) : Type _ := P.dom

namespace FormDom

instance (P : PosSymOp F) : AddCommGroup (FormDom P) := inferInstanceAs (AddCommGroup P.dom)

instance (P : PosSymOp F) : Module ℂ (FormDom P) := inferInstanceAs (Module ℂ P.dom)

/-- The underlying domain vector. -/
def toDom {P : PosSymOp F} (x : FormDom P) : P.dom := x

/-- The underlying ambient vector. -/
def toAmbient {P : PosSymOp F} (x : FormDom P) : F := (toDom x : F)

theorem toAmbient_eq {P : PosSymOp F} (x : FormDom P) :
    toAmbient x = ((toDom x : P.dom) : F) := rfl

@[simp] theorem toAmbient_add {P : PosSymOp F} (x y : FormDom P) :
    toAmbient (x + y) = toAmbient x + toAmbient y := rfl

@[simp] theorem toAmbient_smul {P : PosSymOp F} (r : ℂ) (x : FormDom P) :
    toAmbient (r • x) = r • toAmbient x := rfl

theorem toDom_injective {P : PosSymOp F} : Function.Injective (toDom (P := P)) := fun _ _ h => h

noncomputable instance instInner (P : PosSymOp F) : Inner ℂ (FormDom P) :=
  ⟨fun x y => inner ℂ (toAmbient x) (toAmbient y) + inner ℂ (toAmbient x) (P.op (toDom y))⟩

theorem inner_def {P : PosSymOp F} (x y : FormDom P) :
    (inner ℂ x y : ℂ) = inner ℂ (toAmbient x) (toAmbient y)
      + inner ℂ (toAmbient x) (P.op (toDom y)) := rfl

/-- The form of a positive symmetric operator **is an inner product**: Hermitian
by symmetry of `H`, positive definite because it dominates the ambient norm. -/
noncomputable instance instCore (P : PosSymOp F) : InnerProductSpace.Core ℂ (FormDom P) where
  conj_inner_symm x y := by
    rw [inner_def, inner_def]
    simp only [map_add]
    rw [inner_conj_symm]
    congr 1
    rw [toAmbient_eq, toAmbient_eq, ← P.sym (toDom x) (toDom y), inner_conj_symm]
  re_inner_nonneg x := by
    change 0 ≤ ((inner ℂ x x : ℂ)).re
    rw [inner_def, Complex.add_re, re_inner_self]
    have hp := P.pos (toDom x)
    rw [quadForm, ← toAmbient_eq] at hp
    positivity
  add_left x y z := by
    rw [inner_def, inner_def, inner_def, toAmbient_add, inner_add_left, inner_add_left]
    ring
  smul_left x y r := by
    rw [inner_def, inner_def, toAmbient_smul, inner_smul_left, inner_smul_left]
    ring
  definite x hx := by
    have hre : ((inner ℂ x x : ℂ)).re = 0 := by rw [hx]; simp
    rw [inner_def, Complex.add_re, re_inner_self] at hre
    have hp := P.pos (toDom x)
    rw [quadForm, ← toAmbient_eq] at hp
    have hn : ‖toAmbient x‖ = 0 := by nlinarith [norm_nonneg (toAmbient x)]
    apply toDom_injective
    apply Subtype.ext
    exact (by simpa using hn : toAmbient x = 0)

noncomputable instance instNormed (P : PosSymOp F) : NormedAddCommGroup (FormDom P) :=
  InnerProductSpace.Core.toNormedAddCommGroup (cd := instCore P)

noncomputable instance instIPS (P : PosSymOp F) : InnerProductSpace ℂ (FormDom P) := .ofCore _

theorem norm_sq_eq {P : PosSymOp F} (x : FormDom P) :
    ‖x‖ ^ 2 = ‖toAmbient x‖ ^ 2 + (inner ℂ (toAmbient x) (P.op (toDom x)) : ℂ).re := by
  have h : ‖x‖ ^ 2 = ((inner ℂ x x : ℂ)).re := (re_inner_self (F := FormDom P) x).symm
  rw [h, inner_def, Complex.add_re, re_inner_self]

/-- **The form norm dominates the ambient norm**, `‖x‖ ≤ ‖x‖₁`. -/
theorem norm_toAmbient_le {P : PosSymOp F} (x : FormDom P) : ‖toAmbient x‖ ≤ ‖x‖ := by
  have h := norm_sq_eq x
  have hp := P.pos (toDom x)
  rw [quadForm, ← toAmbient_eq] at hp
  nlinarith [norm_nonneg (toAmbient x), norm_nonneg x]

/-- The inclusion of the form domain into the ambient space. -/
def inclLin (P : PosSymOp F) : FormDom P →ₗ[ℂ] F where
  toFun := toAmbient
  map_add' := toAmbient_add
  map_smul' := toAmbient_smul

/-- The inclusion as a continuous linear map of norm at most one. -/
noncomputable def incl (P : PosSymOp F) : FormDom P →L[ℂ] F :=
  (inclLin P).mkContinuous 1 (fun x => by
    show ‖toAmbient x‖ ≤ 1 * ‖x‖
    rw [one_mul]
    exact norm_toAmbient_le x)



theorem norm_incl_le (P : PosSymOp F) : ‖incl P‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end FormDom

/-! ## Part B — the form completion and its embedding into `F` -/

/-- **The form space**: the completion of the domain in the form norm.  This is
the form domain of the Friedrichs extension. -/
abbrev FormSpace (P : PosSymOp F) : Type _ := UniformSpace.Completion (FormDom P)

namespace FormDom

theorem denseRange_toComplL (P : PosSymOp F) :
    DenseRange (UniformSpace.Completion.toComplL (𝕜 := ℂ) (E := FormDom P)) := by
  simpa [UniformSpace.Completion.coe_toComplL] using
    UniformSpace.Completion.denseRange_coe (α := FormDom P)



variable [CompleteSpace F]

/-- The inclusion of the form domain into `F`, extended to the form completion. -/
noncomputable def formExt (P : PosSymOp F) : FormSpace P →L[ℂ] F :=
  (incl P).extend UniformSpace.Completion.toComplL



theorem norm_formExt_le (P : PosSymOp F) : ‖formExt P‖ ≤ 1 := by
  have h : ‖(incl P).extend (UniformSpace.Completion.toComplL (𝕜 := ℂ) (E := FormDom P))‖
      ≤ (1 : NNReal) * ‖incl P‖ :=
    ContinuousLinearMap.opNorm_extend_le _ (denseRange_toComplL P)
      (fun x => by simp [UniformSpace.Completion.coe_toComplL])
  have := le_trans h (by simpa using norm_incl_le P)
  simpa [formExt] using this

theorem norm_formExt_apply_le (P : PosSymOp F) (k : FormSpace P) : ‖formExt P k‖ ≤ ‖k‖ := by
  have := (formExt P).le_opNorm k
  nlinarith [norm_formExt_le P, norm_nonneg k, norm_nonneg (formExt P k)]







end FormDom

/-! ## Part C — Riesz representation: the resolvent `(H + 1)⁻¹` -/

namespace FormDom

variable [CompleteSpace F]

/-- The **Riesz vector** of `u : F` in the form space: the unique `g` with
`⟪g, k⟫₁ = ⟪u, formExt k⟫` for every `k`. -/
noncomputable def formRiesz (P : PosSymOp F) (u : F) : FormSpace P :=
  (InnerProductSpace.toDual ℂ (FormSpace P)).symm ((innerSL ℂ u).comp (formExt P))

theorem formRiesz_spec (P : PosSymOp F) (u : F) (k : FormSpace P) :
    (inner ℂ (formRiesz P u) k : ℂ) = inner ℂ u (formExt P k) := by
  rw [formRiesz, InnerProductSpace.toDual_symm_apply]
  simp

theorem formRiesz_add (P : PosSymOp F) (u v : F) :
    formRiesz P (u + v) = formRiesz P u + formRiesz P v := by
  refine ext_inner_right ℂ (fun k => ?_)
  rw [formRiesz_spec, inner_add_left, inner_add_left, formRiesz_spec, formRiesz_spec]

theorem formRiesz_smul (P : PosSymOp F) (c : ℂ) (u : F) :
    formRiesz P (c • u) = c • formRiesz P u := by
  refine ext_inner_right ℂ (fun k => ?_)
  rw [formRiesz_spec, inner_smul_left, inner_smul_left, formRiesz_spec]

theorem norm_formRiesz_le (P : PosSymOp F) (u : F) : ‖formRiesz P u‖ ≤ ‖u‖ := by
  have h1 : ‖formRiesz P u‖ ^ 2 = (inner ℂ (formRiesz P u) (formRiesz P u) : ℂ).re :=
    (re_inner_self (F := FormSpace P) _).symm
  rw [formRiesz_spec] at h1
  have h3 : (inner ℂ u (formExt P (formRiesz P u)) : ℂ).re ≤ ‖u‖ * ‖formRiesz P u‖ :=
    le_trans (Complex.re_le_norm _) (le_trans (norm_inner_le_norm _ _)
      (mul_le_mul_of_nonneg_left (norm_formExt_apply_le P _) (norm_nonneg u)))
  nlinarith [norm_nonneg (formRiesz P u), norm_nonneg u]

/-- **The resolvent of the Friedrichs extension at `−1`**, `S = (H + 1)⁻¹`,
built by Riesz representation in the form space. -/
noncomputable def friedrichsResolvent (P : PosSymOp F) : F →L[ℂ] F :=
  LinearMap.mkContinuous
    { toFun := fun u => formExt P (formRiesz P u)
      map_add' := fun u v => by rw [formRiesz_add, map_add]
      map_smul' := fun c u => by rw [formRiesz_smul, map_smul]; rfl } 1
    (fun u => by
      simpa using le_trans (norm_formExt_apply_le P (formRiesz P u)) (norm_formRiesz_le P u))















end FormDom

/-! ## Part D — the Friedrichs extension theorem, with no boundedness -/

open FormDom

variable [CompleteSpace F]







/-! ### The classical statement: symmetric and *bounded below* -/

/-- "`A` on the domain `Dom` is a self-adjoint extension of `H` that is bounded
below by `−c`" — the semibounded analogue of
`BookProof.YangMillsFriedrichs.IsPositiveSelfAdjointExtension`, which is the case
`c = 0`. -/
def IsSemiboundedSelfAdjointExtension (c : ℝ) {D Dom : Submodule ℂ F} (H : D →ₗ[ℂ] F)
    (A : Dom →ₗ[ℂ] F) : Prop :=
  (∀ x : D, ∃ h : (x : F) ∈ Dom, A ⟨(x : F), h⟩ = H x) ∧ SymmetricOn Dom A ∧
    (∀ y : Dom, -c * ‖(y : F)‖ ^ 2 ≤ quadForm A y) ∧
    (∀ w u : F, (∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) u) →
      ∃ h : w ∈ Dom, A ⟨w, h⟩ = u)



/-! ## Part E — the Hashimoto/SIRK limit selects the constructed extension -/

open Filter Topology





/-! ## Part F — the construction is not vacuous: a genuinely unbounded operator -/



end BookProof.FriedrichsExtension


