-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_Presentation
-- name    : MIPRE_Background_LIDT_Presentation
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:54:49.356989+00:00
-- url     : https://prove2.me/theorems/3cdd045f-e1b4-4877-bb2e-6e66312d7139
-- title:
--   Definitions of Presentation: The seeded low-degree questions as CL functions, on any registers The paper's typed CL functions `L_Point`, `L_ALine`,…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.Presentation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The seeded low-degree questions as CL functions, on any registers. The paper's typed CL functions `L_Point`, `L_ALine`, `L_DLine` (`ldt.tex`, `eq:cl-ptf` to `eq:cl-dlnf`) act on three registers of an ambient space: a point register `V_pt ≅ F^n`, a coordinate (seed) register `V_coord ≅ F` and a direction register `V_dir ≅ F^n`. The answer-reduced sampler (`sec:ar-verifier`) uses six copies of them on *overlapping* registers of one ambient space, so the registers are data here: `Regs ι n` places them in the coordinates `ι` of the ambient space by two injections and a coordinate. Every type gets…
--
--   **Definitions** (19): `MIPRE.LIDT.CL.Regs` (The three registers of a copy of the low-degree test in an ambient space with coordinates `ι`: the point and direction registers, each `n`…); `MIPRE.LIDT.CL.Regs.coordSet` (The seed register.); `MIPRE.LIDT.CL.Regs.dirLin` (`π_i` of the direction register.); `MIPRE.LIDT.CL.Regs.dirOf` (The direction a vector carries.); `MIPRE.LIDT.CL.Regs.dirSet` (The direction register.); `MIPRE.LIDT.CL.Regs.finalLin` (The third stage: the canonical base point of the line through the point.); `MIPRE.LIDT.CL.Regs.finalSet` (Everything else: the point register and the coordinates no copy of the test reads.); `MIPRE.LIDT.CL.Regs.pres` (**The three-level presentation** of the question of type `t`: seed, then direction, then the point register and everything else.); `MIPRE.LIDT.CL.Regs.ptLin` (A linear map of the point register, as a map on the final register.); `MIPRE.LIDT.CL.Regs.ptOf` (The point a vector carries.); `MIPRE.LIDT.CL.Regs.putDir` (Write a direction into the direction register, zero elsewhere.); `MIPRE.LIDT.CL.Regs.putPt` (Write a point into the point register, zero elsewhere.); `MIPRE.LIDT.CL.Regs.questionOf` (Read the question of type `t` off a vector, the seed decoded by the selector's permutation.); `MIPRE.LIDT.CL.Regs.sampleOf` (The sample a vector carries, with both types `t`, the seed decoded by the selector's permutation.); `MIPRE.LIDT.CL.Regs.secondLin` (The second stage: `π_{χ(s)}` of the direction, for the diagonal type.); and -3 more.
--
--   **Embedded lemmas** (11): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `dirOf_putDir`, `dirOf_putPt`, `ptOf_putDir`, `ptOf_putPt`, `putDir_coord`, `putDir_dir`, `putDir_of_not`, `putPt_coord`, `putPt_of_not`, `putPt_pt`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.Presentation` (`MIPRE/Background/LIDT/Presentation.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 7 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Presentation.lean; blueprint def:ar-pcp-sampler

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Presentation.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Theorems.Thm_MIPRE_LIDT_CL_card_chi_fiber

/-!
# The seeded low-degree questions as CL functions, on any registers

The paper's typed CL functions `L_Point`, `L_ALine`, `L_DLine` (`ldt.tex`, `eq:cl-ptf` to
`eq:cl-dlnf`) act on three registers of an ambient space: a point register `V_pt ≅ F^n`, a
coordinate (seed) register `V_coord ≅ F` and a direction register `V_dir ≅ F^n`. The answer-reduced
sampler (`sec:ar-verifier`) uses six copies of them on *overlapping* registers of one ambient
space, so the registers are data here: `Regs ι n` places them in the coordinates `ι` of the
ambient space by two injections and a coordinate.

Every type gets a three-level presentation (`pres`), the levels being the seed, then the
direction, then everything else; the paper's one- and two-level functions are the same with
trivial levels, as in `QLD.PauliCL.presentation`. The presentations are exact on the whole space
(`pres_exactlyOn`), and their full evaluation, read back through the registers (`questionOf`), is
the seeded test's question `LIDT.CL.Sample.question` for the sample the registers carry
(`questionOf_eval`).
-/

noncomputable section

namespace MIPRE.CL

open Finset

end MIPRE.CL

namespace MIPRE.LIDT.CL

open Finset MIPRE.CL

/-- The three registers of a copy of the low-degree test in an ambient space with coordinates
`ι`: the point and direction registers, each `n` coordinates, and the seed coordinate. -/
structure Regs (ι : Type*) (n : ℕ) where
  /-- The point register. -/
  pt : Fin n → ι
  /-- The direction register. -/
  dir : Fin n → ι
  /-- The coordinate (seed) register. -/
  coord : ι
  pt_injective : Function.Injective pt
  dir_injective : Function.Injective dir
  pt_ne_dir : ∀ i j, pt i ≠ dir j
  pt_ne_coord : ∀ i, pt i ≠ coord
  dir_ne_coord : ∀ j, dir j ≠ coord

/-- **A seed selector**: the block index `χ(s)` a sampler computes from a seed, with a
permutation `π` of the seeds under which it is the test's own `chi`. The test's `chi` numbers the
field by `Fintype.equivFin`, which no program can compute; an effective sampler uses an explicit
selector with the same block sizes, and the permutation, which only the analysis sees, carries
its questions to the test's (`questionOf_eval`). `Sel.canonical` is the test's own selector. -/
structure Sel (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) [NeZero n]
    (hn : n ∣ Fintype.card F) where
  /-- The selector. -/
  χ : F → Fin n
  /-- The permutation of the seeds. -/
  π : F ≃ F
  chi_π : ∀ s, chi hn (π s) = χ s

namespace Sel

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} [NeZero n]

omit [DecidableEq F] in
/-- **Any selector with blocks of size `q / n`** is a seed selector: the permutation matching it
to the test's `chi` exists. -/
theorem exists_perm (hn : n ∣ Fintype.card F) (χ : F → Fin n)
    (hχ : ∀ i, (Finset.univ.filter fun s => χ s = i).card = Fintype.card F / n) :
    ∃ π : F ≃ F, ∀ s, chi hn (π s) = χ s := by
  classical
  have hfib : ∀ i : Fin n, {s // χ s = i} ≃ {s // chi hn s = i} := fun i =>
    Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype, hχ i, card_chi_fiber hn i])
  exact ⟨Equiv.ofFiberEquiv hfib, fun s => Equiv.ofFiberEquiv_map hfib s⟩

/-- The seed selector of a selector with blocks of size `q / n`. -/
noncomputable def ofSelector (hn : n ∣ Fintype.card F) (χ : F → Fin n)
    (hχ : ∀ i, (Finset.univ.filter fun s => χ s = i).card = Fintype.card F / n) : Sel F n hn :=
  ⟨χ, (exists_perm hn χ hχ).choose, (exists_perm hn χ hχ).choose_spec⟩

end Sel

namespace Regs

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F]

/-! ## Reading and writing registers -/

/-- The point a vector carries. -/
def ptOf (x : ι → F) : Point F n := fun i => x (R.pt i)

/-- The direction a vector carries. -/
def dirOf (x : ι → F) : Point F n := fun i => x (R.dir i)

/-- Write a point into the point register, zero elsewhere. -/
def putPt : Point F n →ₗ[F] (ι → F) := Function.ExtendByZero.linearMap F R.pt

/-- Write a direction into the direction register, zero elsewhere. -/
def putDir : Point F n →ₗ[F] (ι → F) := Function.ExtendByZero.linearMap F R.dir

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem putPt_pt (w : Point F n) (i : Fin n) : R.putPt w (R.pt i) = w i := by
  simp [putPt, R.pt_injective.extend_apply]

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem putDir_dir (w : Point F n) (i : Fin n) : R.putDir w (R.dir i) = w i := by
  simp [putDir, R.dir_injective.extend_apply]

omit [DecidableEq ι] [Fintype ι] in
theorem putPt_of_not {c : ι} (h : ∀ i, R.pt i ≠ c) (w : Point F n) : R.putPt w c = 0 := by
  simp only [putPt, Function.ExtendByZero.linearMap_apply]
  rw [Function.extend_apply' _ _ _ fun ⟨i, hi⟩ => h i hi]
  rfl

omit [DecidableEq ι] [Fintype ι] in
theorem putDir_of_not {c : ι} (h : ∀ i, R.dir i ≠ c) (w : Point F n) : R.putDir w c = 0 := by
  simp only [putDir, Function.ExtendByZero.linearMap_apply]
  rw [Function.extend_apply' _ _ _ fun ⟨i, hi⟩ => h i hi]
  rfl

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem ptOf_putPt (w : Point F n) : R.ptOf (R.putPt w) = w := by
  funext i; simp [ptOf]

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem dirOf_putDir (w : Point F n) : R.dirOf (R.putDir w) = w := by
  funext i; simp [dirOf]

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem dirOf_putPt (w : Point F n) : R.dirOf (R.putPt w) = 0 := by
  funext j; exact R.putPt_of_not (fun i => R.pt_ne_dir i j) w

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem ptOf_putDir (w : Point F n) : R.ptOf (R.putDir w) = 0 := by
  funext i; exact R.putDir_of_not (fun j h => R.pt_ne_dir i j h.symm) w

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem putPt_coord (w : Point F n) : R.putPt w R.coord = 0 :=
  R.putPt_of_not R.pt_ne_coord w

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem putDir_coord (w : Point F n) : R.putDir w R.coord = 0 :=
  R.putDir_of_not R.dir_ne_coord w

/-! ## The register sets -/

/-- The seed register. -/
def coordSet : Finset ι := {R.coord}

/-- The direction register. -/
def dirSet : Finset ι := univ.image R.dir

/-- Everything else: the point register and the coordinates no copy of the test reads. -/
def finalSet : Finset ι := (univ \ R.coordSet) \ R.dirSet

/-! ## The stage maps -/

/-- `π_i`, zeroing the first `i` coordinates, as a linear map. -/
def zeroBelowLin (i : Fin n) : Point F n →ₗ[F] Point F n where
  toFun := zeroBelow i
  map_add' x y := by funext k; simp only [zeroBelow, Pi.add_apply]; split_ifs <;> simp
  map_smul' c x := by funext k; simp only [zeroBelow, Pi.smul_apply]; split_ifs <;> simp

/-- A linear map of the point register, as a map on the final register. -/
def ptLin (A : Point F n →ₗ[F] Point F n) : RegLinear F R.finalSet :=
  RegLinear.ofLinearMap R.finalSet (R.putPt ∘ₗ A ∘ₗ LinearMap.funLeft F F R.pt)

/-- `π_i` of the direction register. -/
def dirLin (i : Fin n) : RegLinear F R.dirSet :=
  RegLinear.ofLinearMap R.dirSet (R.putDir ∘ₗ zeroBelowLin i ∘ₗ LinearMap.funLeft F F R.dir)

variable [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F} (S : Sel F n hn)

/-- The first stage: the seed, for the two line types. -/
def seedLin : Ty → RegLinear F R.coordSet
  | .point => 0
  | _ => RegLinear.id _

/-- The second stage: `π_{χ(s)}` of the direction, for the diagonal type. -/
def secondLin : Ty → F → RegLinear F R.dirSet
  | .dline, s => R.dirLin (S.χ s)
  | _, _ => 0

/-- The third stage: the canonical base point of the line through the point. -/
def finalLin : Ty → F → Point F n → RegLinear F R.finalSet
  | .point, _, _ => R.ptLin LinearMap.id
  | .aline, s, _ => R.ptLin (MIPRE.CL.canonLin (Submodule.span F {Pi.single (S.χ s) 1}))
  | .dline, _, v => R.ptLin (MIPRE.CL.canonLin (Submodule.span F {v}))

/-- **The three-level presentation** of the question of type `t`: seed, then direction, then
the point register and everything else. -/
def pres (t : Ty) : CLFun F ι 3 :=
  .cons R.coordSet (R.seedLin t) fun y =>
    .cons R.dirSet (R.secondLin S t (y R.coord)) fun z =>
      .cons R.finalSet (R.finalLin S t (y R.coord) (R.dirOf z)) fun _ => .zero

/-- Read the question of type `t` off a vector, the seed decoded by the selector's permutation. -/
def questionOf (t : Ty) (x : ι → F) : Question F n :=
  match t with
  | .point => .point (R.ptOf x)
  | .aline => .aline (R.ptOf x) (S.π (x R.coord))
  | .dline => .dline (R.ptOf x) (S.π (x R.coord)) (R.dirOf x)

/-- The sample a vector carries, with both types `t`, the seed decoded by the selector's
permutation. -/
def sampleOf (t : Ty) (x : ι → F) : Sample F n := ⟨t, t, R.ptOf x, S.π (x R.coord), R.dirOf x⟩

/-! ## The law of the sample -/

end Regs

end MIPRE.LIDT.CL

end


