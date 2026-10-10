-- Prove2me | Definitions.Def_ChapterA2d
-- name    : ChapterA2d
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-10T07:06:15.378696+00:00
-- url     : https://prove2.me/theorems/017bc8b9-bf52-40a6-8661-b936131bef64
-- title:
--   Chapter A2d
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA2d.lean`): generated def bundle for ChapterA2d. See BookProof/ChapterA2d.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA2d.lean

import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
import Definitions.Def_ChapterA1c
import Definitions.Def_ChapterA2
import Mathlib


/-!
# Chapter A, §A.2 — isomorphism criteria (Prop 15), work-package N2 leftover

This file discharges the **Prop 15** leftover of work-package **N2** of
`FORMALIZATION_ROADMAP.md` (§A.2, the commutant classification): the criterion
that identifies R-real Schur systems by their complexifications.

## The framework

In the `BookProof` formalization an *R-real Schur system* is represented by a
complex Schur system `(M, V)` together with a C-conjugation `θ` (`IsConjugation`);
its *real form* is `V_θ = {x : θ x = x}`.  Here the ambient complex system `(M, V)`
plays the role of the *complexification* and the real form `V_θ` the role of the
underlying real system.

A **system isometry** `α : V ≃ₗᵢ[ℂ] W` between complex systems `(M, V)` and
`(N, W)` is a `ℂ`-linear isometric equivalence carrying `M` onto `N` by
conjugation (`N.ops = conjCLM α '' M.ops`).  Two real forms `V_{θ_M}`, `W_{θ_N}`
are isometric (as real systems) **iff** some system isometry additionally
*intertwines the conjugations* (`α ∘ θ_M = θ_N ∘ α`): such an `α` restricts to a
real-linear isometry `V_{θ_M} → W_{θ_N}`, and conversely any real isometry of
real forms complexifies to a conjugation-intertwining system isometry.

Thus **Prop 15** ("two R-real Schur systems are isometric iff their
complexifications are isometric") becomes:

> a system isometry `α : V ≃ₗᵢ[ℂ] W` exists **iff** a *conjugation-intertwining*
> system isometry exists.

The backward direction is trivial (forget the extra property).  The forward
direction is **Lemma 14** (`antiisometry_unique_up_to_phase`): the transported
conjugation `ϑ := α θ_M α⁻¹` is an anti-unitary of the Schur system `(N, W)`, so
`θ_N = c · ϑ` with `‖c‖ = 1`; rescaling `α` by a unit square root `λ` of `c`
(`λ² = c`) turns it into a conjugation-intertwining isometry.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped ComplexConjugate InnerProductSpace

namespace BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-! ## System isometries -/

/-- Conjugation of an operator `m : V →L[ℂ] V` by a `ℂ`-linear isometric
equivalence `α : V ≃ₗᵢ[ℂ] W`, giving `α ∘ m ∘ α⁻¹ : W →L[ℂ] W`. -/
noncomputable def conjCLM (α : V ≃ₗᵢ[ℂ] W) (m : V →L[ℂ] V) : W →L[ℂ] W :=
  (α : V →L[ℂ] W) ∘L m ∘L (α.symm : W →L[ℂ] V)

omit [CompleteSpace V] [CompleteSpace W] in
@[simp] lemma conjCLM_apply (α : V ≃ₗᵢ[ℂ] W) (m : V →L[ℂ] V) (w : W) :
    conjCLM α m w = α (m (α.symm w)) := rfl

/-- A **system isometry** between complex systems `(M, V)` and `(N, W)`: the
`ℂ`-linear isometric equivalence `α` carries `M` onto `N` by conjugation. -/
def IsSystemIso (M : System ℂ V) (N : System ℂ W) (α : V ≃ₗᵢ[ℂ] W) : Prop :=
  N.ops = conjCLM α '' M.ops

/-! ## Conjugating an anti-unitary and scaling an isometry -/

/-- The anti-unitary `α ∘ θ ∘ α⁻¹ : W ≃ₗᵢ⋆[ℂ] W` obtained by transporting an
anti-unitary `θ` of `V` along a `ℂ`-linear isometric equivalence `α : V ≃ₗᵢ[ℂ] W`. -/
noncomputable def conjAU (α : V ≃ₗᵢ[ℂ] W) (θ : AntiUnitary V) : AntiUnitary W :=
  (α.symm.trans θ).trans α

omit [CompleteSpace V] [CompleteSpace W] in
@[simp] lemma conjAU_apply (α : V ≃ₗᵢ[ℂ] W) (θ : AntiUnitary V) (w : W) :
    conjAU α θ w = α (θ (α.symm w)) := rfl

/-- Multiplication by a unit-modulus complex number is a `ℂ`-linear isometric
equivalence. -/
noncomputable def unitScaleEquiv (c : ℂ) (hc : ‖c‖ = 1) : W ≃ₗᵢ[ℂ] W :=
  have hcne : c ≠ 0 := by rintro rfl; simp at hc
  { toLinearEquiv :=
    { toFun := fun x => c • x
      map_add' := by intro x y; simp [smul_add]
      map_smul' := by intro a x; simp [smul_smul, mul_comm]
      invFun := fun x => c⁻¹ • x
      left_inv := by intro x; simp [smul_smul, hcne]
      right_inv := by intro x; simp [smul_smul, hcne] }
    norm_map' := by intro x; simp [norm_smul, hc] }

omit [CompleteSpace W] in
@[simp] lemma unitScaleEquiv_apply (c : ℂ) (hc : ‖c‖ = 1) (x : W) :
    unitScaleEquiv c hc x = c • x := rfl

/-
Every unit-modulus complex number has a unit-modulus complex square root.
-/


/-! ## Prop 15 -/



/-
The transported conjugation `ϑ = α θ_M α⁻¹` commutes with `N` when `α` is a
system isometry and `θ_M` commutes with `M`.
-/


/-
**Prop 15 (R-real systems: isometric ⇔ complexifications isometric).**

Two R-real Schur systems — here complex Schur systems `(M, V)`, `(N, W)` with
C-conjugations `θ_M`, `θ_N` — have isometric real forms **iff** their ambient
complex systems are isometric.  Concretely: a *conjugation-intertwining* system
isometry exists **iff** a system isometry exists.

*Proof.*  Backward is immediate.  Forward: given a system isometry `α`, the
transported conjugation `ϑ := α θ_M α⁻¹` is an anti-unitary of the Schur system
`(N, W)` (`conjAU_commutesAntiUnitary`), so by Lemma 14
(`antiisometry_unique_up_to_phase`) `θ_N = c · ϑ` with `‖c‖ = 1`.  Picking a unit
square root `λ` of `c` (`exists_unit_sqrt`), the rescaled isometry
`β := λ • α` is still a system isometry (`conjCLM_unitScale`) and now intertwines
the conjugations, because `λ = conj λ · c`.
-/


end BookProof.ChapterA


