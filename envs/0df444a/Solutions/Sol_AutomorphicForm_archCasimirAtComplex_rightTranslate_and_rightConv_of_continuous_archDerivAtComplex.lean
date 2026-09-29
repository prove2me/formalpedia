-- Prove2me | solution 1 for AutomorphicForm.archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/4b221a25-6556-599b-8e1d-a4d808875404

import Theorems.Thm_AutomorphicForm_archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne
import Theorems.Thm_AutomorphicForm_archCasimirAtComplex_rightTranslate_archComplexGLAt
import Theorems.Thm_AutomorphicForm_archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplexAPI
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

open NumberField.InfinitePlace.Completion

theorem solution
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAtComplex hw x)
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) :
    (∀ (w' : InfinitePlace K) (k : rowIsometrySubgroup₀ w'.Completion),
        IsArchSmoothAtComplex hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) ∧
        (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d (rightTranslate K (rowIsometryInclAt₀ K w' k) x))) ∧
        (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d'
          (rightTranslate K (rowIsometryInclAt₀ K w' k) x)))) ∧
        archCasimirAtComplex hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) =
          rightTranslate K (rowIsometryInclAt₀ K w' k) (archCasimirAtComplex hw x) ∧
        archCasimirBarAtComplex hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) =
          rightTranslate K (rowIsometryInclAt₀ K w' k) (archCasimirBarAtComplex hw x)) ∧
    (∀ (f : AdelicGL2 (𝓞 K) K → ℂ) (tys : AutomorphicForm.ArchTypeFamily K),
        IsFactorizableTestFn K f → IsArchBiFinite K tys f →
        IsArchSmoothAtComplex hw (rightConv K x f) ∧
        (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d (rightConv K x f))) ∧
        (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' (rightConv K x f)))) ∧
        archCasimirAtComplex hw (rightConv K x f) = rightConv K (archCasimirAtComplex hw x) f ∧
        archCasimirBarAtComplex hw (rightConv K x f) = rightConv K (archCasimirBarAtComplex hw x) f) := by
  classical
  refine ⟨?_, AutomorphicForm.archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex
    K w hw x hxc hxs hD1 hD2⟩
  intro w' k
  by_cases hw' : w' = w
  · subst hw'

    have hkm : rowIsometryInclAt₀ K w' k =
        archComplexGLAt hw (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw) (k : GL (Fin 2) w'.Completion)) := by
      rw [rowIsometryInclAt₀_apply, archComplexGLAt_glEquivOfRingEquiv]
    rw [hkm]
    exact AutomorphicForm.archCasimirAtComplex_rightTranslate_archComplexGLAt K w' hw x hxc hxs hD1 hD2 _
  · exact AutomorphicForm.archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne K w hw x hxc hxs hD1 hD2 w' hw' k

end S_AutomorphicForm_archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex
end P2MW
export P2MW.S_AutomorphicForm_archCasimirAtComplex_rightTranslate_and_rightConv_of_continuous_archDerivAtComplex (solution)
