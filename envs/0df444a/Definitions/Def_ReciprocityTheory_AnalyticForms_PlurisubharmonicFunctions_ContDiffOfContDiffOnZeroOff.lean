-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
-- name    : ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:58.541257+00:00
-- url     : https://prove2.me/theorems/2dcba4cf-616e-483a-b491-f023786d9971
-- title:
--   Cont Diff Of Cont Diff On Zero Off
-- statement:
--   Definitions and structural lemmas for Cont Diff Of Cont Diff On Zero Off, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
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
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
def gReg (ε : ℝ) (ζ : ℂ) : ℝ := (1 / 2) * Real.log (‖ζ‖ ^ 2 + ε)
def cReg (ε : ℝ) (ζ : ℂ) : ℝ := ε / (2 * (‖ζ‖ ^ 2 + ε) ^ 2)
variable {n : ℕ}
def kDens (n : ℕ) : ℝ := ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1)
def minorDens (i : Fin (n + 1)) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (z : Fin (n + 1) → ℂ) : ℝ :=
  (mdisc (fun k => (hessC (φ k) z).submatrix i.succAbove i.succAbove)).re
def psiRef (n : ℕ) : Fin n → (Fin (n + 1) → ℂ) → ℝ := fun _ z => ∑ i, Complex.normSq (z i)
def hDens (i : Fin (n + 1)) (v : (Fin (n + 1) → ℂ) → ℝ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ)
    (z : Fin (n + 1) → ℂ) : ℝ :=
  v z * minorDens i φ z
end
end ReciprocityTheory.AnForm.A


