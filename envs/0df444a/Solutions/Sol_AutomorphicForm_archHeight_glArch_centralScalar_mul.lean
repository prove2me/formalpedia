-- Prove2me | solution 1 for AutomorphicForm.archHeight_glArch_centralScalar_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/c87664e0-ff00-5781-ac42-416598646a34

import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_archHeight_glArch_centralScalar_mul

noncomputable section
p2m_open "NumberField AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel Matrix"

namespace M4aP3B
namespace Rows

variable (F : Type) [Field F] [NumberField F]

private theorem centralScalar_entries (z : (AdeleRing (𝓞 F) F)ˣ) (i j : Fin 2) :
    ((centralScalar (𝓞 F) F z : AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j
      = if i = j then (z : AdeleRing (𝓞 F) F) else 0 := by
  show (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F)) i j = _
  rw [Matrix.scalar_apply]
  by_cases h : i = j
  · subst h; rw [Matrix.diagonal_apply_eq, if_pos rfl]
  · rw [Matrix.diagonal_apply_ne _ h, if_neg h]

theorem archHeight_glArch_centralScalar_mul_impl
    (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    archHeight F (glArch (𝓞 F) F (centralScalar (𝓞 F) F z * g))
      = archHeight F (glArch (𝓞 F) F g) := by
  rw [map_mul]
  refine archHeight_scalar_entries_mul F
    (z := adeleArch (𝓞 F) F (z : AdeleRing (𝓞 F) F)) ?_ ?_ ?_ ?_ ?_ (glArch (𝓞 F) F g)
  · intro v
    have h1 : IsUnit (adeleArch (𝓞 F) F (z : AdeleRing (𝓞 F) F)) :=
      IsUnit.map (adeleArch (𝓞 F) F) z.isUnit
    have h2 : IsUnit (archEval F v (adeleArch (𝓞 F) F (z : AdeleRing (𝓞 F) F))) :=
      IsUnit.map (archEval F v) h1
    have h__af := h2.ne_zero
    simp at h__af
    exact h__af
  · rw [glArch_apply, centralScalar_entries, if_pos rfl]; rfl
  · rw [glArch_apply, centralScalar_entries,
      if_neg (by decide : ¬ ((0 : Fin 2) = 1))]; rfl
  · rw [glArch_apply, centralScalar_entries,
      if_neg (by decide : ¬ ((1 : Fin 2) = 0))]; rfl
  · rw [glArch_apply, centralScalar_entries, if_pos rfl]; rfl

end M4aP3B.Rows

end

#print axioms M4aP3B.Rows.archHeight_glArch_centralScalar_mul_impl

theorem solution (F : Type) [Field F] [NumberField F]
    (z : (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)ˣ)
    (g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers F) F) :
    AutomorphicForm.WindowedSiegel.archHeight F
        (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers F) F
          (AutomorphicForm.centralScalar (NumberField.RingOfIntegers F) F z * g))
      = AutomorphicForm.WindowedSiegel.archHeight F
          (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers F) F g) := by
  exact M4aP3B.Rows.archHeight_glArch_centralScalar_mul_impl F z g

end S_AutomorphicForm_archHeight_glArch_centralScalar_mul
end P2MW
export P2MW.S_AutomorphicForm_archHeight_glArch_centralScalar_mul (solution)
