-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFrameOfIsPeriod
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFrameOfIsPeriod
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:37:22.02797+00:00
-- url     : https://prove2.me/theorems/042dbaa3-cf96-404f-bab1-a396f9228970
-- title:
--   Exists Frame Of Is Period
-- statement:
--   Definitions and structural lemmas for Exists Frame Of Is Period, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsFrameOfIsPeriod.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqIffConjNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexOrder ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.PeriodOnto
def sgnMat (r q : ℕ) : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun a => ((FD.sgn q a : ℝ) : ℂ)
def kap (q a : ℕ) : ℂ →ₗ[ℝ] ℂ := if a < q then Complex.conjAe.toLinearMap else LinearMap.id
section Block
variable {ι : Type} [Fintype ι] {g r : ℕ} (idx : Fin g ≃ ι × Fin r) (q : ℕ)
def blockOf (t : ι) : (Fin g → ℂ) →ₗ[ℝ] (Fin r → ℂ) :=
  LinearMap.pi fun a => (kap q a).comp (LinearMap.proj (idx.symm (t, a)))
open Classical in

def ofBlock (t : ι) (w : Fin r → ℂ) : Fin g → ℂ :=
  fun k => if (idx k).1 = t then kap q (idx k).2 (w (idx k).2) else 0
variable {Λ : Type} (P : Λ → Fin g → ℂ) (hspan : Submodule.span ℝ (Set.range P) = ⊤)
  (e : ι → Λ → Fin r → ℂ) (M : ι → Matrix (Fin r) (Fin r) ℂ)
  (hM : ∀ v t, blockOf idx q t (P v) = M t *ᵥ e t v)
end Block
section Field
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]
end Field
end GlobalTheory.PeriodOnto
namespace GlobalTheory
open PeriodOnto
end GlobalTheory


