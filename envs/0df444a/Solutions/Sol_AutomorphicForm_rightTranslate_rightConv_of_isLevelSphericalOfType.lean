-- Prove2me | solution 1 for AutomorphicForm.rightTranslate_rightConv_of_isLevelSphericalOfType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/604200be-4f2a-57a6-8e13-6b517d355d58

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchSpherical
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_rightConv_rightTranslate_eq_rightTranslate_rightConv_conj
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_rightTranslate_rightConv_of_isLevelSphericalOfType

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent
open scoped BigOperators

theorem solution
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F) (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsLevelSphericalOfType F tys U f)
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    rightTranslate F (rowIsometryInclAt₀ F w k) (rightConv F φ f) =
      rightConv F (rightTranslate F (rowIsometryInclAt₀ F w k) φ) f := by
  obtain ⟨fa, -, -, hconj, hfac⟩ := hf
  have hinv : (fun y => f (rowIsometryInclAt₀ F w k * y * (rowIsometryInclAt₀ F w k)⁻¹)) = f := by
    funext y
    rw [hfac (rowIsometryInclAt₀ F w k * y * (rowIsometryInclAt₀ F w k)⁻¹), hfac y]
    simp only [_root_.map_mul, _root_.map_inv, glArch_rowIsometryInclAt₀, glFin_rowIsometryInclAt₀, hconj,
      one_mul, inv_one, mul_one]
  rw [AutomorphicForm.CuspidalConstituent.rightConv_rightTranslate_eq_rightTranslate_rightConv_conj, hinv]

end S_AutomorphicForm_rightTranslate_rightConv_of_isLevelSphericalOfType
end P2MW
export P2MW.S_AutomorphicForm_rightTranslate_rightConv_of_isLevelSphericalOfType (solution)
