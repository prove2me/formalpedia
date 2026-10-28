-- Prove2me | Definitions.Def_OAIQ18Pg013
-- name    : OAIQ18Pg013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T16:07:43.768277+00:00
-- url     : https://prove2.me/theorems/f0a66516-6a6f-4adc-92d5-24b00c6dd71e
-- title:
--   Definitions bundle OAIQ18Pg013 of the split of OpenAI, An infinite finitely presented periodic group
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SourceBurnside.thm_main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented periodic group*, OpenAI Math Release, September 23, 2026, result family 247, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory/PeriodicGroups, in whole or in part: [`PeriodicGroups_Steinberg_DiagonalActions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/PeriodicGroups/PeriodicGroups/Steinberg/DiagonalActions.lean).
--
--   **Imports.** It imports the published bundle `Def_PeriodicGroup`; the bundle `OAIQ18Pg010` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ18Pg014`.
-- source:
--   OpenAI, An infinite finitely presented periodic group, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 247; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-infinite-finitely-presented-periodic-group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/PeriodicGroups at commit adc7f12

import Mathlib
import Definitions.Def_PeriodicGroup
import Definitions.Def_OAIQ18Pg010

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_DiagonalActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SourceBurnside.Stability.SteinbergAction
noncomputable section
open Classical Steinberg MatrixGenerators
variable {n : ℕ} {R : Type*} [Ring R]

lemma diagonal_conjugate_e (u : Fin n → Rˣ) (p : Root n) (a : R) :
    diagonal u * Elementary.e p a * (diagonal u)⁻¹ =
      Elementary.e p ((u p.row).val*a*(u p.col).inv) := by
  apply Units.ext
  change Matrix.diagonal (fun i => (u i).val) * (1+Matrix.single p.row p.col a) *
    Matrix.diagonal (fun i => (u i).inv) = 1+Matrix.single p.row p.col _
  rw [mul_add,add_mul,Matrix.mul_one,Matrix.diagonal_mul_diagonal]
  have hd : Matrix.diagonal (fun i => (u i).val*(u i).inv) = (1 : Matrix (Fin n) (Fin n) R) := by
    simp
  rw [hd]
  congr 1
  ext i j
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.single_apply]
  split_ifs with h
  · rw [h.1,h.2]
  · simp

lemma representation_scale (u : Fin n → Rˣ) (g : Steinberg n R) :
    Elementary.representation (scale u g) = diagonal u * Elementary.representation g * (diagonal u)⁻¹ := by
  have hh : Elementary.representation.comp (scale u).toMonoidHom =
      (MulAut.conj (diagonal u)).toMonoidHom.comp Elementary.representation := by
    apply Steinberg.hom_ext
    intro p a
    simp only [MonoidHom.comp_apply,MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,
      scale_x,Elementary.representation_x]
    exact (diagonal_conjugate_e u p a).symm
  exact DFunLike.congr_fun hh g

end
end SourceBurnside.Stability.SteinbergAction

end
section
namespace SourceBurnside.Stability.SteinbergAction
noncomputable section
open Classical Steinberg MatrixGenerators
variable {n : ℕ} {R : Type*} [Ring R]

lemma generator_equivariant (s : GLGenerator (n := n) (R := R)) (g : Steinberg n R) :
    Elementary.representation (generatorAction s g) = s.matrix * Elementary.representation g * s.matrix⁻¹ := by
  cases s with
  | root i j h a =>
    change Elementary.representation (x ⟨i,j,h⟩ a * g * (x ⟨i,j,h⟩ a)⁻¹) = _
    simp only [map_mul,map_inv,Elementary.representation_x,SmallPresentation.Generator.matrix]
    rfl
  | diag i u => exact representation_scale (fun j => if j=i then u else 1) g

lemma word_equivariant (w : FreeGroup (GLGenerator (n := n) (R := R))) (g : Steinberg n R) :
    Elementary.representation (wordAction w g) =
      SmallPresentation.matrixWord w * Elementary.representation g * (SmallPresentation.matrixWord w)⁻¹ := by
  induction w using OAI.freeGroupInductionOn generalizing g with
  | one => simp
  | of s =>
    simp only [wordAction_of,SmallPresentation.matrixWord,FreeGroup.lift_apply_of]
    exact generator_equivariant s g
  | inv_of s ih =>
    rw [map_inv,map_inv,inv_inv]
    have hh := ih ((wordAction (FreeGroup.of s))⁻¹ g)
    have hh' := congrArg (fun h => (SmallPresentation.matrixWord (FreeGroup.of s))⁻¹ * h *
      SmallPresentation.matrixWord (FreeGroup.of s)) hh
    simpa only [MulAut.apply_inv_self,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,
      inv_mul_cancel,mul_one] using hh'.symm
  | mul w z hw hz =>
    rw [map_mul,map_mul,mul_inv_rev]
    change Elementary.representation (wordAction w (wordAction z g)) = _
    rw [hw,hz]
    group

end
end SourceBurnside.Stability.SteinbergAction

end
section
namespace SourceBurnside.Stability.MatrixK1
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators

end
end SourceBurnside.Stability.MatrixK1

end

end OAI
end


