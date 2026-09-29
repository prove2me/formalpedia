-- Prove2me | solution 1 for AutomorphicForm.archDerivAtComplex_iH_eq_smul_of_hasCircleWeightAt_of_isArchSmoothAtComplex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/fc141504-ede0-5639-80b5-92039127330b

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplexAPI
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_archDerivAtComplex_iH_eq_smul_of_hasCircleWeightAt_of_isArchSmoothAtComplex

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex) (n : ℤ)
    (ψ : AdelicGL2 (𝓞 K) K → ℂ) (hψ : IsArchSmoothAtComplex hw ψ)
    (hwt : HasCircleWeightAt hw n ψ) :
    archDerivAtComplex hw .iH ψ = (Complex.I * (n : ℂ)) • ψ := by
  funext g
  show deriv (fun t : ℝ => ψ (g * archFlowAtComplex hw .iH t)) 0 = ((Complex.I * (n : ℂ)) • ψ) g
  rw [Pi.smul_apply, smul_eq_mul]

  have hflow : ∀ t : ℝ, archFlowAtComplex hw .iH t =
      archCircleAt hw (Units.mk0 (Complex.exp ((t : ℂ) * Complex.I)) (Complex.exp_ne_zero _)) := by
    intro t
    show archComplexGLAt hw (archFlowMatrixComplex .iH t) =
      archComplexGLAt hw (circleGL2 (Units.mk0 (Complex.exp ((t : ℂ) * Complex.I)) (Complex.exp_ne_zero _)))
    congr 1
    refine Units.ext ?_
    show (splitTorusGL2Complex ((t : ℂ) * Complex.I) : Matrix (Fin 2) (Fin 2) ℂ) =
      (circleGL2 (Units.mk0 (Complex.exp ((t : ℂ) * Complex.I)) (Complex.exp_ne_zero _)) : Matrix (Fin 2) (Fin 2) ℂ)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [splitTorusGL2Complex, circleGL2, Units.val_inv_eq_inv_val, Complex.exp_neg]
  have hnorm : ∀ t : ℝ, ‖((Units.mk0 (Complex.exp ((t : ℂ) * Complex.I)) (Complex.exp_ne_zero _) : ℂˣ) : ℂ)‖ = 1 :=
    fun t => by simp [Complex.norm_exp_ofReal_mul_I]
  have hfun : (fun t : ℝ => ψ (g * archFlowAtComplex hw .iH t)) =
      fun t : ℝ => Complex.exp ((t : ℂ) * ((n : ℂ) * Complex.I)) * ψ g := by
    funext t
    rw [hflow t, hwt _ (hnorm t) g, Units.val_mk0, ← Complex.exp_int_mul]
    congr 2
    ring
  rw [hfun]
  have hd : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * ((n : ℂ) * Complex.I)) * ψ g)
      (((n : ℂ) * Complex.I) * ψ g) 0 :=
    (AutomorphicForm.hasDerivAt_cexp_ofReal_mul_const ((n : ℂ) * Complex.I)).mul_const (ψ g)
  rw [hd.deriv]
  ring

end S_AutomorphicForm_archDerivAtComplex_iH_eq_smul_of_hasCircleWeightAt_of_isArchSmoothAtComplex
end P2MW
export P2MW.S_AutomorphicForm_archDerivAtComplex_iH_eq_smul_of_hasCircleWeightAt_of_isArchSmoothAtComplex (solution)
