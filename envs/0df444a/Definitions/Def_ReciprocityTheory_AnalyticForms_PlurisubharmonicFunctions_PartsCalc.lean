-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
-- name    : ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:45.280555+00:00
-- url     : https://prove2.me/theorems/c8211141-9c4c-45a5-849c-51bc42d3bfb3
-- title:
--   Parts Calc
-- statement:
--   Definitions and structural lemmas for Parts Calc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsCalc.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix
noncomputable section
abbrev BilinSp (D : ℕ) := (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ
def evalL {D : ℕ} (x w : Fin D → ℂ) : BilinSp D →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ w).comp (ContinuousLinearMap.apply ℝ ((Fin D → ℂ) →L[ℝ] ℝ) x)
def hessEntry {D : ℕ} (a b : Fin D) : BilinSp D →L[ℝ] ℂ :=
  (1 / 4 : ℂ) • (Complex.ofRealCLM.comp
      (evalL (Pi.single a 1) (Pi.single b 1) +
        evalL (Complex.I • Pi.single a 1) (Complex.I • Pi.single b 1)) +
    Complex.I • Complex.ofRealCLM.comp
      (evalL (Pi.single a 1) (Complex.I • Pi.single b 1) -
        evalL (Complex.I • Pi.single a 1) (Pi.single b 1)))
def hessMat {D : ℕ} : BilinSp D →ₗ[ℝ] Matrix (Fin D) (Fin D) ℂ where
  toFun H := Matrix.of fun a b => hessEntry a b H
  map_add' H K := by ext a b; simp
  map_smul' c H := by ext a b; simp
end
end ReciprocityTheory.AnForm.A


