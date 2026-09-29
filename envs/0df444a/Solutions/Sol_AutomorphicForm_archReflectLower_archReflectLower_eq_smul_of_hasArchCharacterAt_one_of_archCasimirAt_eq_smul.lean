-- Prove2me | solution 1 for AutomorphicForm.archReflectLower_archReflectLower_eq_smul_of_hasArchCharacterAt_one_of_archCasimirAt_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/72980b4c-61c5-519e-a233-ecf1c78784b9

import Theorems.Thm_AutomorphicForm_isArchSmoothAt_reflectedLowering_and_archCasimirAt_eq_and_reflectedLowering_reflectedLowering_eq_smul
import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.Analysis.MellinTransform
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_archReflectLower_archReflectLower_eq_smul_of_hasArchCharacterAt_one_of_archCasimirAt_eq_smul

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace LanglandsTunnell.RealArchParam
open scoped nonZeroDivisors

set_option autoImplicit false

theorem Ws47.JSPLIT.archRealGLAt_J_mul_J {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal) :
    archRealGLAt hw UpperHalfPlane.J * archRealGLAt hw UpperHalfPlane.J = (1 : AdelicGL2 (𝓞 F) F) := by
  rw [← map_mul]
  have : (UpperHalfPlane.J : GL (Fin 2) ℝ) * UpperHalfPlane.J = 1 := by
    ext i j
    rw [Units.val_mul]
    fin_cases i <;> fin_cases j <;> simp [UpperHalfPlane.J, Matrix.mul_apply, Fin.sum_univ_two]
  rw [this, map_one]

theorem solution
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal) (lam : ℂ)
    (x : AdelicGL2 (𝓞 F) F → ℂ)
    (_hsm : IsArchSmoothAt hw x)
    (_hwt : HasArchCharacterAt₀ F w (archWeightCharAt hw 1) x)
    (_hcas : archCasimirAt hw x = lam • x) :
    let T : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ) := fun y g =>
      (archDerivAt hw ArchDir.H y - Complex.I • (archDerivAt hw ArchDir.E y + archDerivAt hw ArchDir.Fm y))
        (g * archRealGLAt hw UpperHalfPlane.J)
    T (T x) = (1 - 4 * lam) • x ∧

    ∀ κ : ℂ, κ ^ 2 * (1 - 4 * lam) = 1 →
      ∀ g : AdelicGL2 (𝓞 F) F,
        (x + κ • T x) (g * archRealGLAt hw UpperHalfPlane.J)
          = κ * (archDerivAt hw ArchDir.H (x + κ • T x)
                  - Complex.I • (archDerivAt hw ArchDir.E (x + κ • T x) + archDerivAt hw ArchDir.Fm (x + κ • T x))) g := by
  intro T
  obtain ⟨-, hTsm, -, -, hTT⟩ := AutomorphicForm.isArchSmoothAt_reflectedLowering_and_archCasimirAt_eq_and_reflectedLowering_reflectedLowering_eq_smul F w hw T rfl x _hsm
  have h1 : T (T x) = (1 - 4 * lam) • x := hTT lam _hcas _hwt
  refine ⟨h1, fun κ hκ g => ?_⟩
  have hJJ := Ws47.JSPLIT.archRealGLAt_J_mul_J (F := F) hw

  have hL : ∀ (y : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F),
      (archDerivAt hw ArchDir.H y - Complex.I • (archDerivAt hw ArchDir.E y + archDerivAt hw ArchDir.Fm y)) g
        = T y (g * archRealGLAt hw UpperHalfPlane.J) := by
    intro y g
    show _ = (archDerivAt hw ArchDir.H y - Complex.I • (archDerivAt hw ArchDir.E y + archDerivAt hw ArchDir.Fm y))
      (g * archRealGLAt hw UpperHalfPlane.J * archRealGLAt hw UpperHalfPlane.J)
    rw [mul_assoc, hJJ, mul_one]
  have hTxs : IsArchSmoothAt hw (κ • T x) := hTsm.smul κ
  have hadd : ∀ d : ArchDir, archDerivAt hw d (x + κ • T x) = archDerivAt hw d x + κ • archDerivAt hw d (T x) := by
    intro d; rw [archDerivAt_add _hsm hTxs, archDerivAt_smul]
  have e1 := hL x g
  have e2 := hL (T x) g
  rw [h1] at e2
  rw [hadd ArchDir.H, hadd ArchDir.E, hadd ArchDir.Fm]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
  linear_combination (-κ) * e1 + (-(κ ^ 2)) * e2 - (x (g * archRealGLAt hw UpperHalfPlane.J)) * hκ

end S_AutomorphicForm_archReflectLower_archReflectLower_eq_smul_of_hasArchCharacterAt_one_of_archCasimirAt_eq_smul
end P2MW
export P2MW.S_AutomorphicForm_archReflectLower_archReflectLower_eq_smul_of_hasArchCharacterAt_one_of_archCasimirAt_eq_smul (solution)
