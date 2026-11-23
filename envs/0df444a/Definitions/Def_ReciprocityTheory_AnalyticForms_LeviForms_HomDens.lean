-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDens
-- name    : ReciprocityTheory_AnalyticForms_LeviForms_HomDens
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:50.726806+00:00
-- url     : https://prove2.me/theorems/96e15523-5dcd-465f-b2bd-694fd75d2daa
-- title:
--   Hom Dens
-- statement:
--   Definitions and structural lemmas for Hom Dens, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDens.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.P
open MeasureTheory
noncomputable section
def CellMatZeroStatement : Prop := ∀ N : ℕ, cellMat N 0 = 1
def LeviHalfLogAbsStatement : Prop :=
  ∀ {ι : Type} [Fintype ι] (f : (ι → ℂ) → ℝ) (z : ι → ℂ), ContDiffAt ℝ 2 f z → f z ≠ 0 →
    fderiv ℝ f z = 0 → ∀ w : ι → ℂ,
      levi (fun x => (1 / 2) * Real.log |f x|) z w = levi f z w / (2 * f z)
def detGram (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (z : Pairs N → ℂ) : ℝ :=
  ((Matrix.submatrix ((cellMat N z).conjTranspose * Matrix.diagonal (fun k => (hd k : ℂ)) *
      cellMat N z) (Fin.castLE hm) (Fin.castLE hm)).det).re
section HomDensHelp
open Matrix Polynomial
def sW (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (v : Pairs N → ℂ) : ℝ :=
  ∑ i : Fin N, ∑ k : Fin N,
    if i.val < m ∧ m ≤ k.val then hd k / hd i * ‖zMat N v k i‖ ^ 2 else 0
end HomDensHelp
def LogDetFlagEqStatement : Prop :=
  ∀ (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N),
    logDetFlag N hd m hm = fun z => (1 / 2) * Real.log |detGram N hd m hm z|
def DetGramDerivStatement : Prop :=
  ∀ (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N),
    ContDiff ℝ 2 (detGram N hd m hm) ∧
      detGram N hd m hm 0 = ∏ a : Fin m, hd (Fin.castLE hm a) ∧ fderiv ℝ (detGram N hd m hm) 0 = 0
def DetGramLeviStatement : Prop :=
  ∀ (N : ℕ) (hd : Fin N → ℝ), (∀ k, hd k ≠ 0) → ∀ (m : ℕ) (hm : m ≤ N) (w : Pairs N → ℂ),
    levi (detGram N hd m hm) 0 w = (∏ a : Fin m, hd (Fin.castLE hm a)) *
      ∑ p : Pairs N, if p.1.1.val < m ∧ m ≤ p.1.2.val then hd p.1.2 / hd p.1.1 * ‖w p‖ ^ 2 else 0
end
end ReciprocityTheory.AnForm.P


