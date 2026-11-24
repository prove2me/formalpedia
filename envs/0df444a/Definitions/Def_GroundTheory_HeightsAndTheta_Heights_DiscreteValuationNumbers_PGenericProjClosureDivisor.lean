-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDivisor
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDivisor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:36.88337+00:00
-- url     : https://prove2.me/theorems/606cd4ec-8aa2-445d-8385-2fa070a35bb0
-- title:
--   PGeneric Proj Closure Divisor
-- statement:
--   Definitions and structural lemmas for PGeneric Proj Closure Divisor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDivisor.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericProjClosureDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExpress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GenericProjClosureDivisor
section PointIdeal
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {O : Type} [CommRing O] {Φ : Type} [Field Φ] [Algebra O Φ]
end PointIdeal
section Forms
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {N M M' : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
  {Φ : Type} [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
def vdeg (α : K → ℕ) : Option (Option K) → ℕ
  | some (some k) => α k
  | _ => 0
def chartMonoZ (O : Type) [CommRing O] (M M' : ℕ) (c : ∀ k, ι k) (α : K → ℕ) :
    MRing (bundleIdx (bundleIdx ι M) M') O :=
  ∏ k, X (⟨some (some k), c k⟩ : Σ o, bundleIdx (bundleIdx ι M) M' o) ^ α k
def genVal (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ) (ψ : Module.Dual Ω E) : Φ :=
  ∑ i, t i * algebraMap Ω Φ (ψ (e i))
variable [∀ k, Fintype (ι k)]
def IsZPair (a₀ a₀' : K → ℤ) (z : (Σ o, bundleIdx (bundleIdx ι M) M' o) → Φ)
    (f g : MRing (bundleIdx (bundleIdx ι M) M') O) : Prop :=
  (∃ bf bg : Option (Option K) → ℕ, IsMultiHomog f bf ∧ IsMultiHomog g bg ∧
    (fun o => (bf o : ℤ) - bg o) = zetaFirst a₀ - zetaSecond a₀') ∧ aeval z f = aeval z g
end Forms
end GenericProjClosureDivisor
end
end GroundTheory.Heights₂.Heights.NumbersDVR


