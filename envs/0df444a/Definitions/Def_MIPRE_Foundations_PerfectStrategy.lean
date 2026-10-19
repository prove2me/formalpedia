-- Prove2me | Definitions.Def_MIPRE_Foundations_PerfectStrategy
-- name    : MIPRE_Foundations_PerfectStrategy
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:54:35.323799+00:00
-- url     : https://prove2.me/theorems/dd511ff4-242d-4447-8c88-dc9d41bbec5f
-- title:
--   Definitions of PerfectStrategy: Perfect strategies reject nothing on the support Every completeness argument in the pipeline needs the same step: a…
-- statement:
--   The definitions of the module `MIPRE.Foundations.PerfectStrategy` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Perfect strategies reject nothing on the support. Every completeness argument in the pipeline needs the same step: a strategy of value `1` does not merely win on average, it assigns probability zero to each rejected answer pair at each question pair the verifier actually asks. That step was used implicitly inside `MIPRE.tracialValue_le_one` and nowhere available as a lemma; this file states it. * `sum_re_tracial` — at a fixed question pair the outcome probabilities sum to one. This was a `have` inside `tracialValue_le_one`; it is the reason the value is at most one, and it is wanted on its…
--
--   **Definitions** (1): `MIPRE.SyncStrategy.push` (The projective measurement obtained by relabelling outcomes along `f`: the operator for `a'` is the sum over the fibre of `f` above `a'`.).
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `orthogonal`, `push_apply`, `sum_flat`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.PerfectStrategy` (`MIPRE/Foundations/PerfectStrategy.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 3 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/PerfectStrategy.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/PerfectStrategy.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Theorems.Thm_MIPRE_ProjectiveMeasurement_consistency

/-!
# Perfect strategies reject nothing on the support

Every completeness argument in the pipeline needs the same step: a strategy of value `1` does
not merely win on average, it assigns probability zero to each rejected answer pair at each
question pair the verifier actually asks. That step was used implicitly inside
`MIPRE.tracialValue_le_one` and nowhere available as a lemma; this file states it.

* `sum_re_tracial` — at a fixed question pair the outcome probabilities sum to one. This was a
  `have` inside `tracialValue_le_one`; it is the reason the value is at most one, and it is
  wanted on its own.
* `re_eq_zero_of_tracialValue_eq_one` — the characterization: if the value is `1` then
  `τ(M^x_a M^y_b) = 0` whenever `μ(x, y) > 0` and `(a, b)` is rejected.

Both are at the generic tracial level, so they serve synchronous and commuting strategies
alike; `SyncStrategy.re_eq_zero_of_value_eq_one` is the synchronous spelling, with the
normalized trace written out as `Tr(M^x_a M^y_b)/d`.
-/

namespace MIPRE

open Finset
open scoped ComplexOrder

variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]

omit [DecidableEq A] in
/-- Flattening the fourfold sum of a value into one sum over a product type. -/
theorem sum_flat (F : X → X → A → A → ℝ) :
    ∑ x, ∑ y, ∑ a, ∑ b, F x y a b
      = ∑ p : X × X × A × A, F p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  simp [Fintype.sum_prod_type]

namespace SyncStrategy

variable {G : SynchronousGame X A}

/-! ## Faithfulness, and orthogonality of a projective measurement

The normalized trace on matrices is *faithful*, which the generic tracial level cannot see.
Two consequences that completeness arguments need at the operator level rather than the state
level, and which the paper uses without comment: a rejected outcome of a value-one strategy is
not merely improbable but the zero operator, and distinct outcomes at one question are exactly
orthogonal. -/

open scoped Matrix in
/-- **Distinct outcomes of a projective measurement are orthogonal.** The tracial statement
`ProjectiveMeasurement.consistency` says the *probability* is zero; on matrices, faithfulness
of the trace upgrades that to the operator identity, which is what a commutation obligation at
a repeated question needs. -/
theorem orthogonal (S : SyncStrategy G) (x : X) {a b : A} (hab : a ≠ b) :
    S.P.M x a * S.P.M x b = 0 := by
  have hd : ((Fintype.card (Fin S.d) : ℂ))⁻¹ ≠ 0 := by
    simp [Fintype.card_fin, S.d_pos.ne']
  have hτ := ProjectiveMeasurement.consistency S.P
    (normalizedTrace (Fin S.d) (hn := Fin.pos_iff_nonempty.mp S.d_pos)) x hab
  rw [normalizedTrace_apply] at hτ
  have htr : (S.P.M x a * S.P.M x b).trace = 0 := (mul_eq_zero.mp hτ).resolve_left hd
  -- `(M^x_b M^x_a)ᴴ (M^x_b M^x_a) = M^x_a M^x_b M^x_a`, whose trace is that of `M^x_a M^x_b`
  have hzero : S.P.M x b * S.P.M x a = 0 := by
    refine Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp ?_
    have hH : (S.P.M x b * S.P.M x a)ᴴ * (S.P.M x b * S.P.M x a)
        = S.P.M x a * S.P.M x b * S.P.M x a := by
      rw [Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose,
        ← Matrix.star_eq_conjTranspose, S.P.selfAdjoint, S.P.selfAdjoint]
      calc S.P.M x a * S.P.M x b * (S.P.M x b * S.P.M x a)
          = S.P.M x a * (S.P.M x b * S.P.M x b) * S.P.M x a := by noncomm_ring
        _ = S.P.M x a * S.P.M x b * S.P.M x a := by rw [S.P.projective]
    rw [hH]
    have e1 : S.P.M x a * S.P.M x b * S.P.M x a
        = S.P.M x a * (S.P.M x b * S.P.M x a) := by noncomm_ring
    have e2 : S.P.M x b * S.P.M x a * S.P.M x a = S.P.M x b * S.P.M x a := by
      rw [Matrix.mul_assoc, S.P.projective]
    rw [e1, Matrix.trace_mul_comm, e2, Matrix.trace_mul_comm, htr]
  have hconj : S.P.M x a * S.P.M x b = (S.P.M x b * S.P.M x a)ᴴ := by
    rw [Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose,
      ← Matrix.star_eq_conjTranspose, S.P.selfAdjoint, S.P.selfAdjoint]
  rw [hconj, hzero, Matrix.conjTranspose_zero]

/-! ## The value through `MIPRE.ntr`

`MIPRE.ntr` is the real part of the normalized trace, the form in which the closeness calculus
of `MIPRE/Foundations/Closeness.lean` manipulates outcome probabilities. These four lemmas are
the bridge. -/

/-! ## Pushing a measurement forward along a map of outcome sets

Soundness arguments need to *relabel* outcomes: to group the answers that fail a parse into
one distinguished outcome, or to read an oracle's pair-valued answer as one of its components.
A sum over a fibre is again a projection precisely because distinct outcomes are orthogonal,
which is `SyncStrategy.orthogonal` above and is unavailable at the generic tracial level. -/

/-- The projective measurement obtained by relabelling outcomes along `f`: the operator for
`a'` is the sum over the fibre of `f` above `a'`. -/
noncomputable def push (S : SyncStrategy G) {A' : Type*} [Fintype A'] [DecidableEq A']
    (f : A → A') : ProjectiveMeasurement X A' (Matrix (Fin S.d) (Fin S.d) ℂ) where
  M x a' := ∑ u ∈ univ.filter fun u => f u = a', S.P.M x u
  selfAdjoint x a' := by
    rw [star_sum]
    exact Finset.sum_congr rfl fun u _ => S.P.selfAdjoint x u
  projective x a' := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    refine Finset.sum_eq_single_of_mem u hu ?_ |>.trans (S.P.projective x u)
    intro v _ hvu
    exact S.orthogonal x (Ne.symm hvu)
  normalized x := by
    rw [Finset.sum_fiberwise_of_maps_to (fun u _ => mem_univ (f u))]
    exact S.P.normalized x

@[simp] theorem push_apply (S : SyncStrategy G) {A' : Type*} [Fintype A'] [DecidableEq A']
    (f : A → A') (x : X) (a' : A') :
    (S.push f).M x a' = ∑ u ∈ univ.filter fun u => f u = a', S.P.M x u := rfl

end SyncStrategy

end MIPRE


