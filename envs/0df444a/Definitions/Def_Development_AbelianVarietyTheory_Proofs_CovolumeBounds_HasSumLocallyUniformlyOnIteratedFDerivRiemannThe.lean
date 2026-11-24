-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:34.143797+00:00
-- url     : https://prove2.me/theorems/eaaf5a3b-fb40-482d-b855-40328b6c44d7
-- title:
--   Has Sum Locally Uniformly On Iterated FDeriv Riemann The
-- statement:
--   Definitions and structural lemmas for Has Sum Locally Uniformly On Iterated FDeriv Riemann The, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HasSumLocallyUniformlyOnIteratedFDerivRiemannThe.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped Real
noncomputable section
namespace GlobalTheory
variable {ι : Type*} [Fintype ι]
def riemannThetaJointForm (a : ι → ℝ) (n : ι → ℤ) : ((ι → ℂ) × (ι → ι → ℂ)) →L[ℂ] ℂ :=
  (riemannThetaForm a n).coprod (∑ i, ∑ j, (π * I * (((n i : ℂ) + a i) * ((n j : ℂ) + a j))) •
    (ContinuousLinearMap.proj j : (ι → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ι → ℂ) i))
section Families
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Families
def symmSingle {ι : Type*} [DecidableEq ι] (i j : ι) : Matrix ι ι ℂ :=
  of fun k l => if k = i ∧ l = j ∨ k = j ∧ l = i then 1 else 0
section Upper
variable {ι : Type*} [LinearOrder ι]
def symmOfUpper (x : {p : ι × ι // p.1 ≤ p.2} → ℂ) : Matrix ι ι ℂ :=
  of fun i j => x ⟨(min i j, max i j), min_le_max⟩
def siegelUpperCoords (ι : Type*) [LinearOrder ι] : Set ({p : ι × ι // p.1 ≤ p.2} → ℂ) :=
  symmOfUpper ⁻¹' siegelUpperHalfSpace ι
variable [Fintype ι]
end Upper
end GlobalTheory


