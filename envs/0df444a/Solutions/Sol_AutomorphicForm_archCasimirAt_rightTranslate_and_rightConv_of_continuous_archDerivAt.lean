-- Prove2me | solution 1 for AutomorphicForm.archCasimirAt_rightTranslate_and_rightConv_of_continuous_archDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/c8ca7710-1275-5108-b229-0a2222eceafe

import Theorems.Thm_AutomorphicForm_archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne
import Theorems.Thm_AutomorphicForm_archCasimirAt_rightTranslate_archRealGLAt
import Theorems.Thm_AutomorphicForm_archCasimirAt_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_archCasimirAt_rightTranslate_and_rightConv_of_continuous_archDerivAt

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent NumberField.InfinitePlace.Completion

theorem solution
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAt hw x)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d x))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x))) :
    (∀ (w' : InfinitePlace K) (k : rowIsometrySubgroup₀ w'.Completion),
        IsArchSmoothAt hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) ∧
        (∀ d : ArchDir, Continuous (archDerivAt hw d (rightTranslate K (rowIsometryInclAt₀ K w' k) x))) ∧
        (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d'
          (rightTranslate K (rowIsometryInclAt₀ K w' k) x)))) ∧
        archCasimirAt hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) =
          rightTranslate K (rowIsometryInclAt₀ K w' k) (archCasimirAt hw x)) ∧
    (∀ (f : AdelicGL2 (𝓞 K) K → ℂ) (tys : AutomorphicForm.ArchTypeFamily K),
        IsFactorizableTestFn K f → IsArchBiFinite K tys f →
        IsArchSmoothAt hw (rightConv K x f) ∧
        (∀ d : ArchDir, Continuous (archDerivAt hw d (rightConv K x f))) ∧
        (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' (rightConv K x f)))) ∧
        archCasimirAt hw (rightConv K x f) = rightConv K (archCasimirAt hw x) f) := by
  classical
  refine ⟨?_, AutomorphicForm.archCasimirAt_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAt K w hw x hxc hxs hD1 hD2⟩
  intro w' k
  by_cases hw' : w' = w
  · subst hw'

    set e := ringEquivRealOfIsReal hw with he
    let m : GL (Fin 2) ℝ := glEquivOfRingEquiv e (k : GL (Fin 2) w'.Completion)
    have hkm : rowIsometryInclAt₀ K w' k = archRealGLAt hw m := by
      show adelicArchGLInclAt K w' (k : GL (Fin 2) w'.Completion) =
        adelicArchGLInclAt K w' (glEquivOfRingEquiv e.symm (glEquivOfRingEquiv e (k : GL (Fin 2) w'.Completion)))
      congr 1
      apply Units.ext; ext i j
      show ((k : GL (Fin 2) w'.Completion) : Matrix (Fin 2) (Fin 2) w'.Completion) i j =
        e.symm (e (((k : GL (Fin 2) w'.Completion) : Matrix (Fin 2) (Fin 2) w'.Completion) i j))
      exact (e.symm_apply_apply _).symm
    rw [hkm]
    exact AutomorphicForm.archCasimirAt_rightTranslate_archRealGLAt K w' hw x hxc hxs hD1 hD2 m
  · exact AutomorphicForm.archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne K w hw x hxc hxs hD1 hD2 w' hw' k

end S_AutomorphicForm_archCasimirAt_rightTranslate_and_rightConv_of_continuous_archDerivAt
end P2MW
export P2MW.S_AutomorphicForm_archCasimirAt_rightTranslate_and_rightConv_of_continuous_archDerivAt (solution)
