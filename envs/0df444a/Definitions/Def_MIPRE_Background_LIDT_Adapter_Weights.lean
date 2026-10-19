-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_Adapter_Weights
-- name    : MIPRE_Background_LIDT_Adapter_Weights
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:57:41.429372+00:00
-- url     : https://prove2.me/theorems/0cb401fb-050f-4b54-a2c4-2a646060e82e
-- title:
--   Definitions of Weights: The seeded-CL adapter, part 5: both tests' distributions, as counts The reduction's remaining obligation is a…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.Adapter.Weights` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The seeded-CL adapter, part 5: both tests' distributions, as counts. The reduction's remaining obligation is a push-forward bound between the two tests' question distributions, and both are defined as sums over a `Sample` type against an indicator. So the first thing to do is to turn each into a *count*, after which the bound is arithmetic on cardinalities rather than on sums. * `clGame`'s distribution is uniform over its samples, so it is the number of samples producing the question pair, over the total (`clGame_μ_eq`). * `lidtGame`'s is not uniform — its three subtests are weighted `1/3`…
--
--   **Definitions** (8): `MIPRE.LIDT.Adapter.Seed` (The averaging family: a fibre position for each direction index, and one global nonzero direction scale.); `MIPRE.LIDT.Adapter.blk` (The block size, as a real.); `MIPRE.LIDT.Adapter.clSwap` (Exchanging the two players' types in a seeded sample.); `MIPRE.LIDT.Adapter.clSwapEquiv` (The type exchange as an equivalence of seeded samples.); `MIPRE.LIDT.Adapter.diagKey` (The key `(j, c)` of a diagonal sample, read at a coordinate `p`.); `MIPRE.LIDT.Adapter.qmapS` (The seeded question a canonical-line question is played through, for a family member.); `MIPRE.LIDT.Adapter.swapEquiv` (The swap as an equivalence of samples.); `MIPRE.LIDT.Adapter.swapSample` (Flipping a sample's swap bit.).
--
--   **Embedded lemmas** (10): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `clSwap_clSwap`, `extend_zero`, `qmapS_axis`, `qmapS_diag`, `qmapS_point`, `revPoint_zero`, `swapSample_questions`, `swapSample_swapSample`, `swapSample_weight`, `through_zero`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.Adapter.Weights` (`MIPRE/Background/LIDT/Adapter/Weights.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 12 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Adapter/Weights.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Weights.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy

/-!
# The seeded-CL adapter, part 5: both tests' distributions, as counts

The reduction's remaining obligation is a push-forward bound between the two tests' question
distributions, and both are defined as sums over a `Sample` type against an indicator. So the
first thing to do is to turn each into a *count*, after which the bound is arithmetic on
cardinalities rather than on sums.

* `clGame`'s distribution is uniform over its samples, so it is the number of samples producing
  the question pair, over the total (`clGame_μ_eq`).
* `lidtGame`'s is not uniform — its three subtests are weighted `1/3` each and its diagonal
  directions carry a factor `q^{-(j+1)}` — so the best that can be said in general is that it is
  the sum of the weights of the samples producing the pair (`lidtGame_μ_eq`). That sum is a
  singleton for the point and axis-parallel shapes and a geometric series over the admissible
  `j` for the diagonal one, which is where the `q^{χ s}` against `q^{j+1}` matching of
  `planning/lidt-cl-adapter.md` lives.
-/

namespace MIPRE.LIDT.Adapter

open Finset MIPRE.LIDT MIPRE.LIDT.CL

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]

/-! ## The canonical-line test, shape by shape

Each shape needs the set of samples producing a given question pair. For the point and
axis-parallel shapes it is a singleton and the weight is read off directly; the diagonal shape is
the one where several samples contribute. -/

/-! ## The diagonal shape

Here several samples contribute, so the weight is a sum. It does **not** have to be evaluated:
in the push-forward bound the canonical-line weight appears only on the larger side, so an upper
bound suffices, and bounding the sum by `count × largest term` costs only a factor `m` in the
constant --- which `δ_CL` absorbs, being allowed a prefactor polynomial in `m` and `d`. What it
may *not* absorb is a factor growing with `q`, so the `q`-exponent has to be right, and that is
what `le_rev_diagIdx_of_questions` pins down. -/

/-- The key `(j, c)` of a diagonal sample, read at a coordinate `p`. Two samples producing the
same line with the same key are equal, which is what bounds the count. -/
noncomputable def diagKey (p : Fin m) : Sample F m → Fin m × F
  | .diag _ _ j v => (j, (Sample.extend v : Point F m) p)
  | _ => (idx0, 0)

/-! ## The seeded test, shape by shape

Only **lower** bounds are needed here, since the seeded weight sits on the smaller side of the
push-forward bound, and a lower bound on a count is an injection *into* the set of contributing
samples. That is much cheaper than an exact count, and it is why this section is short. -/

/-! ## From fibres of the question map to samples

The push-forward bound is stated over *fibres* of the question map, but the canonical-line test's
weight lives on *samples*, and only five shapes of question pair carry any weight at all. This
lemma moves the whole thing onto samples, where the case analysis is a case analysis on a
constructor. -/

/-! ## Counting the seed choices

With the push-forward on samples, the average over the family becomes a weight times a *count of
family members*, and that is what the shapes differ in: a point question's image does not depend
on the family member at all, while a line question's pins the seed at one index (and, for a
diagonal, the scale). -/

/-- The averaging family: a fibre position for each direction index, and one global nonzero
direction scale. The scale is there because of the second correction in
`planning/lidt-cl-adapter.md`. -/
abbrev Seed (F : Type*) [Field F] [Fintype F] (m : ℕ) : Type _ :=
  (Fin m → Fin (Fintype.card F / m)) × {c : F // c ≠ 0}

/-- The seeded question a canonical-line question is played through, for a family member. -/
noncomputable def qmapS (hm : m ∣ Fintype.card F) (σc : Seed F m) :
    Question F m → CL.Question F m :=
  qmap hm σc.1 σc.2.1

@[simp] theorem qmapS_point (hm : m ∣ Fintype.card F) (σc : Seed F m) (u : Point F m) :
    qmapS hm σc (.point u) = .point (revPoint u) := rfl

/-! ### The point shape

Only the self-consistency sample can contribute, and its image does not depend on the family
member, so averaging neither helps nor hurts here: the requirement is the unaveraged
`1/(3 q^m) ≤ C · 1/(9 q^m)`, i.e. `C ≥ 3`. -/

/-! ### Cardinalities

Three counts enter the arithmetic: the point space, the seeded test's sample space and the
averaging family. Only the first has to be known as a power of `q`; the other two enter as
symbols that cancel. -/

/-! ### The shape of every one of the bounds

All four nonzero shapes are bounded the same way: the contributing samples lie in one finite set
`T` that does not depend on the family member, each of them has weight at most `B`, and each is
picked out by at most `M` family members. -/

/-! ### The mirrored shapes come for free

Both tests are symmetric under exchanging the two players --- `lidtGame`'s swap bit and
`clGame`'s ordered type pair --- so a bound for `(x, y)` is a bound for `(y, x)`, and only the
shapes with the *line* on the left have to be done by hand. -/

/-- Flipping a sample's swap bit. -/
def swapSample : Sample F m → Sample F m
  | .axis b u i => .axis (!b) u i
  | .selfConsistency u => .selfConsistency u
  | .diag b u j v => .diag (!b) u j v

omit [Fintype F] [NeZero m] in
@[simp] theorem swapSample_questions (s : Sample F m) :
    (swapSample s).questions = s.questions.swap := by
  cases s with
  | axis b u i => cases b <;> rfl
  | selfConsistency u => rfl
  | diag b u j v => cases b <;> rfl

omit [Field F] [DecidableEq F] [NeZero m] in
@[simp] theorem swapSample_weight (s : Sample F m) : (swapSample s).weight = s.weight := by
  cases s <;> rfl

omit [Field F] [Fintype F] [DecidableEq F] [NeZero m] in
@[simp] theorem swapSample_swapSample (s : Sample F m) : swapSample (swapSample s) = s := by
  cases s with
  | axis b u i => cases b <;> rfl
  | selfConsistency u => rfl
  | diag b u j v => cases b <;> rfl

/-- The swap as an equivalence of samples. -/
def swapEquiv : Sample F m ≃ Sample F m :=
  ⟨swapSample, swapSample, swapSample_swapSample, swapSample_swapSample⟩

/-- Exchanging the two players' types in a seeded sample. -/
def clSwap (sm : CL.Sample F m) : CL.Sample F m := {sm with tyA := sm.tyB, tyB := sm.tyA}

omit [Field F] [Fintype F] [DecidableEq F] [NeZero m] in
@[simp] theorem clSwap_clSwap (sm : CL.Sample F m) : clSwap (clSwap sm) = sm := rfl

/-- The type exchange as an equivalence of seeded samples. -/
def clSwapEquiv : CL.Sample F m ≃ CL.Sample F m := ⟨clSwap, clSwap, clSwap_clSwap, clSwap_clSwap⟩

/-! ### The seed counts

A line question's image pins the family's fibre position at exactly one index --- and, for a
diagonal, the scale as well. That is the whole content of the averaging: the family has
`(q/m)^m (q-1)` members and only `(q/m)^{m-1} (q-1)` or `(q/m)^{m-1}` of them can contribute. -/

@[simp] theorem qmapS_axis (hm : m ∣ Fintype.card F) (σc : Seed F m) (ℓ : Line F m) :
    qmapS hm σc (.axisLine ℓ)
      = .aline (revPoint ℓ.1)
          (seedOf hm (Fin.rev (axisIdx ℓ)) (σc.1 (Fin.rev (axisIdx ℓ)))) := rfl

@[simp] theorem qmapS_diag (hm : m ∣ Fintype.card F) (σc : Seed F m) (ℓ : Line F m) :
    qmapS hm σc (.diagLine ℓ)
      = .dline (revPoint ℓ.1 - shiftOf ℓ • revPoint ℓ.2)
          (seedOf hm (diagIdx ℓ) (σc.1 (diagIdx ℓ))) ((σc.2 : F) • revPoint ℓ.2) := rfl

/-! ### The axis-parallel shape

The seed determines the direction index, so the contributing sample is unique and the constraint
on the family is at one index. -/

/-! ### The arithmetic facts

Each shape ends in an inequality between two explicit rationals in `q`, `m` and `q/m`. These are
the casts and positivity facts they all need. -/

/-- The block size, as a real. -/
noncomputable abbrev blk (F : Type*) [Fintype F] (m : ℕ) : ℝ := ((Fintype.card F / m : ℕ) : ℝ)

/-! ### The axis-parallel bound -/

/-! ### The point bound

Here the averaging is neutral: the image of a point question does not depend on the family
member, so both sides carry the same factor `|Seed|` and the requirement is the unaveraged
`1/(3 q^m) ≤ C/(9 q^m)`. -/

/-! ### The diagonal shape

Two cases, and they are genuinely different. A *nondegenerate* diagonal question determines the
line, the scale and the seed index, so the family is pinned twice over and only `(q/m)^{m-1}` of
its members contribute. A *singleton* question (direction zero) pins the seed index but not the
scale --- scaling the zero direction does nothing --- and is paid for instead by `diagIdx`
sending singleton lines to `χ = m - 1`, where the seeded test has `q^{m-1}` samples rather
than one. -/

omit [Fintype F] [DecidableEq F] [NeZero m] in
@[simp] theorem revPoint_zero : (revPoint (0 : Point F m) : Point F m) = 0 := by
  funext k; rfl

omit [Fintype F] [DecidableEq F] [NeZero m] in
@[simp] theorem extend_zero (j : Fin m) :
    (Sample.extend (0 : Fin ((j : ℕ) + 1) → F) : Point F m) = 0 := by
  funext k
  rw [Sample.extend]
  by_cases h : (k : ℕ) ≤ (j : ℕ)
  · rw [dif_pos h]; rfl
  · rw [dif_neg h]; rfl

omit [Fintype F] [NeZero m] in
@[simp] theorem through_zero (u : Point F m) :
    Line.through u (0 : Point F m) = (u, 0) := by
  rw [Line.through, dif_neg]
  rintro ⟨j, hj⟩
  exact hj rfl

/-! ### The nondegenerate diagonal shape

Here the question determines the line, the scale *and* the seed index, so the family is pinned
twice and only `(q/m)^{m-1}` of its members contribute. That second pinning is what the scale
averaging bought. -/

/-! ### The pairs of lines, and the assembly

`lidtGame`'s only same-type subtest is point self-consistency, so no sample asks two lines and
the four remaining shapes carry no weight at all. That is the piece of luck this route runs on:
it needs no line-synchronicity transfer, hence no Schwartz--Zippel and no `d/q` term. -/

end MIPRE.LIDT.Adapter


