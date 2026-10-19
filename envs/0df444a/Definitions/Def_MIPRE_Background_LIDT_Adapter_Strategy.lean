-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy
-- name    : MIPRE_Background_LIDT_Adapter_Strategy
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:56:55.308664+00:00
-- url     : https://prove2.me/theorems/e2e577dc-2ead-425a-9df0-0f14ec4d29f2
-- title:
--   Definitions of Strategy: The seeded-CL adapter, part 4: the question and answer maps The reduction plays a strategy for the seeded CL test as a…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.Adapter.Strategy` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The seeded-CL adapter, part 4: the question and answer maps. The reduction plays a strategy for the seeded CL test as a strategy for the canonical-line test, through `MIPRE.TensorProductStrategy.adapt`. That needs two maps, and this file defines them and the bookkeeping that identifies them. `qmap hm σ` sends a question of the canonical-line test to the seeded question it is played through: * a point `u` to the point `ρ u`, reversal exchanging the two diagonal conventions; * an axis-parallel line to `(ρ ℓ.1, s)` — no `rep` is needed, the two tests' base points agree exactly there…
--
--   **Definitions** (6): `MIPRE.LIDT.Adapter.amap` (The canonical-line answer a seeded answer becomes.); `MIPRE.LIDT.Adapter.axisIdx` (The direction index of an axis-parallel line.); `MIPRE.LIDT.Adapter.diagIdx` (The `χ`-index the adapter uses for a diagonal line: the first nonzero coordinate of the reversed direction, which is the pivot of its span…); `MIPRE.LIDT.Adapter.idx0` (A default index, for the branches of the maps below that the support never reaches.); `MIPRE.LIDT.Adapter.qmap` (The seeded question a canonical-line question is played through, for the seed choice `σ` and the direction scale `c`.); `MIPRE.LIDT.Adapter.shiftOf` (The shift between the two presentations of a line.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `axisIdx_eq`, `single_inj`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.Adapter.Strategy` (`MIPRE/Background/LIDT/Adapter/Strategy.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 11 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Adapter/Strategy.lean; blueprint lem:lidt-cl-adapter-maps

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Strategy.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam

/-!
# The seeded-CL adapter, part 4: the question and answer maps

The reduction plays a strategy for the seeded CL test as a strategy for the canonical-line
test, through `MIPRE.TensorProductStrategy.adapt`. That needs two maps, and this file defines
them and the bookkeeping that identifies them.

`qmap hm σ` sends a question of the canonical-line test to the seeded question it is played
through:

* a point `u` to the point `ρ u`, reversal exchanging the two diagonal conventions;
* an axis-parallel line to `(ρ ℓ.1, s)` — no `rep` is needed, the two tests' base points agree
  exactly there (`rep_single_eq_through`) — with `s` the chosen seed of the fibre over
  `rev (axisIdx ℓ)`;
* a diagonal line to `(rep (ρ ℓ.2) (ρ ℓ.1), s, ρ ℓ.2)`, carrying the direction *unrescaled*.
  That is legitimate because the seeded test's `DLine` questions carry the raw direction, and it
  is what makes the answer conversion a pure shift rather than a shift and a scaling.

`amap` sends a seeded answer to a canonical-line answer, and depends on the question — the
shift does. Its unreachable branches are unreachable because `clGame` *rejects* an answer
whose format does not match its question's type; before that was repaired the branches would
have been live.

`shiftOf ℓ` is the shift, read off `rep_eq`: the two base points differ by `shiftOf ℓ` times the
direction (`rep_rev_eq`), so the two parameters of a point of the line differ by `shiftOf ℓ`.
-/

namespace MIPRE.LIDT.Adapter

open Finset Submodule Module MIPRE.CL MIPRE.LIDT MIPRE.LIDT.CL

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]

/-! ## Reading the direction off a line -/

omit [Fintype F] [DecidableEq F] [NeZero m] in
theorem single_inj {i j : Fin m} (h : (Pi.single i 1 : Point F m) = Pi.single j 1) : i = j := by
  by_contra hne
  have hi := congrFun h i
  rw [Pi.single_eq_same, Pi.single_apply, if_neg hne] at hi
  exact one_ne_zero hi

/-- A default index, for the branches of the maps below that the support never reaches. -/
def idx0 : Fin m := ⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩

/-- The direction index of an axis-parallel line. -/
noncomputable def axisIdx (ℓ : Line F m) : Fin m :=
  if h : ∃ i : Fin m, ℓ.2 = Pi.single i 1 then h.choose else idx0

omit [Fintype F] in
@[simp] theorem axisIdx_eq (b : Point F m) (i : Fin m) :
    axisIdx ((b, Pi.single i 1) : Line F m) = i := by
  have h : ∃ j : Fin m, ((b, Pi.single i 1) : Line F m).2 = Pi.single j 1 := ⟨i, rfl⟩
  rw [axisIdx, dif_pos h]
  exact (single_inj h.choose_spec).symm

/-- The `χ`-index the adapter uses for a diagonal line: the first nonzero coordinate of the
reversed direction, which is the pivot of its span and so the coordinate `rep` zeroes.

The fallback for a *singleton* line (direction zero) is `rev idx0 = m - 1`, not `idx0`, and the
choice is forced by the weight bookkeeping rather than free. The seeded test's `DLine` samples
with `zeroBelow (χ s) V = 0` number `q^{χ s}`, so its mass on `(u₀, s, 0)` grows with `χ s`;
the canonical-line test puts mass `≈ 1/(6 m q^m q)` on a singleton line, which only the largest
`χ` can dominate. Sending singleton lines to `χ = 0` costs a factor `q^{m-1}`, which the error
term of `thm:lidt-cl-soundness` does not allow. See `planning/lidt-cl-adapter.md`. -/
noncomputable def diagIdx (ℓ : Line F m) : Fin m :=
  if h : ∃ j, (revPoint ℓ.2) j ≠ 0 then Fin.find (fun j => (revPoint ℓ.2) j ≠ 0) h
  else Fin.rev idx0

/-- The shift between the two presentations of a line. -/
noncomputable def shiftOf (ℓ : Line F m) : F :=
  if h : ∃ j, (revPoint ℓ.2) j ≠ 0 then
    (revPoint ℓ.1) (Fin.find (fun j => (revPoint ℓ.2) j ≠ 0) h)
      / (revPoint ℓ.2) (Fin.find (fun j => (revPoint ℓ.2) j ≠ 0) h)
  else 0

/-! ## The seeded test's base point, in terms of the shift -/

/-! ## The two maps -/

/-- The seeded question a canonical-line question is played through, for the seed choice `σ` and
the direction scale `c`.

The scale is averaged over along with the seed, and it has to be: the seeded test's `DLine`
questions carry the raw direction, so one geometric line has `q - 1` of them, and an adapter
using only one would concentrate its push-forward on a `1/(q-1)` fraction of them and need a
`q`-dependent constant. See the second correction in `planning/lidt-cl-adapter.md`.

Scaling the direction does not move the base point, `rep` depending only on the span. -/
noncomputable def qmap (hm : m ∣ Fintype.card F) (σ : Fin m → Fin (Fintype.card F / m))
    (c : F) : Question F m → CL.Question F m
  | .point u => .point (revPoint u)
  | .axisLine ℓ =>
      .aline (revPoint ℓ.1) (seedOf hm (Fin.rev (axisIdx ℓ)) (σ (Fin.rev (axisIdx ℓ))))
  | .diagLine ℓ =>
      .dline (revPoint ℓ.1 - shiftOf ℓ • revPoint ℓ.2)
        (seedOf hm (diagIdx ℓ) (σ (diagIdx ℓ))) (c • revPoint ℓ.2)

/-- The canonical-line answer a seeded answer becomes. It depends on the question because the
shift does, and on the scale `c`; the branches not listed are the ones `clGame` rejects on
format.

A point of the line at the target's parameter `t` sits at the source's parameter
`(t + shiftOf ℓ) / c`, so the substitution to undo is `t ↦ c⁻¹ t + c⁻¹ · shiftOf ℓ`. -/
noncomputable def amap (c : F) : Question F m → CL.Answer F m d 1 → Answer F m d
  | .point _, .values a => .value (a 0)
  | .axisLine _, .apolys f => .axisPoly (f 0)
  | .diagLine ℓ, .dpolys f => .diagPoly (reparam c⁻¹ (c⁻¹ * shiftOf ℓ) (f 0))
  | _, _ => .value 0

/-! ## The support of the canonical-line test's distribution -/

/-! ## Transporting membership through the reversal -/

/-! ## Reading the answer format off the acceptance -/

/-! ## `hD`: acceptance survives the two maps

One lemma per case of `Sample`, since the source's acceptance says something different in each.
-/

variable (hm : m ∣ Fintype.card F) (σ : Fin m → Fin (Fintype.card F / m)) {c : F}

/-! ### The swapped cases

Each test hands the line to either player, so the two mirrored cases have to be done too. The
proofs are the previous two with the roles exchanged; both games' predicates carry the mirrored
clause explicitly. -/

/-! ### `hD`, assembled

The five cases above are exactly the five shapes a question pair of positive weight can have, so
this is the hypothesis `MIPRE.TensorProductStrategy.one_sub_value_adapt_le` asks for. Note it is
asked *only* on the support: off it the claim is false, since a pair of two line questions is a
real question pair of the seeded test and the canonical-line test has no subtest for it. -/

end MIPRE.LIDT.Adapter


