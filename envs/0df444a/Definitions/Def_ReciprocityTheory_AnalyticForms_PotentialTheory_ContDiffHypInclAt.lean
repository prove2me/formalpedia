-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffHypInclAt
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffHypInclAt
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T12:53:16.389654+00:00
-- url     : https://prove2.me/theorems/d5ab3fab-8e11-521a-84b6-6b3bb2770777
-- title:
--   Cont Diff Hyp Incl At
-- statement:
--   Definitions and structural lemmas for Cont Diff Hyp Incl At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffHypInclAt.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
import Theorems.Thm_ReciprocityTheory_AnForm_A_integrableOn_image_iff_analytic
import Theorems.Thm_ReciprocityTheory_AnForm_A_integral_image_eq_integral_normSq_det_smul
import Theorems.Thm_ReciprocityTheory_AnForm_A_maDens_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M.PLAux
open MeasureTheory FinHolAtlas Filter Topology
open ReciprocityTheory.AnForm.A (hypInclAt densHypAt jacC maDens_comp integral_image_eq_integral_normSq_det_smul
  integrableOn_image_iff_analytic)
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
def removeCLM (i : Fin (e + 1)) : (Fin (e + 1) → ℂ) →L[ℂ] (Fin e → ℂ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (i.succAbove k)
section Slice
variable {A : FinHolAtlas (e + 1) X} {W : Set X} {ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)}
  {i : Fin (e + 1)}
end Slice
section SliceMain
variable [T2Space X] [CompactSpace X] {A : FinHolAtlas (e + 1) X} {W : Set X} [CompactSpace W]
  {ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)} {i : Fin (e + 1)}
def sliceMap (ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)) (i : Fin (e + 1))
    (c : OpenPartialHomeomorph W (Fin e → ℂ)) (y : Fin e → ℂ) : Fin e → ℂ :=
  Fin.removeNth i (ψ ((c.symm y : W) : X))
end SliceMain
section SliceInt
variable [T2Space X] [CompactSpace X] {A : FinHolAtlas (e + 1) X} {W : Set X} [CompactSpace W]
  {ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)} {i : Fin (e + 1)}
open Classical in

def extW (W : Set X) (χ : W → ℝ) (p : X) : ℝ := if h : p ∈ W then χ ⟨p, h⟩ else 0
def sliceDens (Φ : Fin e → LocPot X) (x : X) (ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ))
    (i : Fin (e + 1)) : Fin e → (Fin e → ℂ) → ℝ :=
  fun k => ((Φ k).φ x ∘ ψ.symm) ∘ hypInclAt i
def sliceF (W : Set X) (χ : W → ℝ) (v : X → ℝ) (ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ))
    (i : Fin (e + 1)) (φ : Fin e → (Fin e → ℂ) → ℝ) (z : Fin e → ℂ) : ℝ :=
  extW W χ (ψ.symm (hypInclAt i z)) * v (ψ.symm (hypInclAt i z)) * maDens φ z
end SliceInt
end
end ReciprocityTheory.AnForm.M.PLAux


