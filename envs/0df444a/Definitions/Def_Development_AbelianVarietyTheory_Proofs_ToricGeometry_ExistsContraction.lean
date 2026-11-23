-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction
-- name    : Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:10.84122+00:00
-- url     : https://prove2.me/theorems/5b7337ab-e6ab-41ff-8aea-77c202150e23
-- title:
--   Exists Contraction
-- statement:
--   Definitions and structural lemmas for Exists Contraction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.PeriodChart
section Abstract
variable {V : Type} [AddCommGroup V] [Module ℂ V]
end Abstract
section Mat
variable {g : ℕ}
noncomputable def sesq (G : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (hermForm G)
    (fun x y z => by simp [hermForm]) (fun c x z => by simp [hermForm])
    (fun x y z => by simp [hermForm, mulVec_add]) (fun c x z => by simp [hermForm, mulVec_smul])
noncomputable def anti (Z : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ⋆[ℂ] (Fin g → ℂ) where
  toFun z := Z *ᵥ star z
  map_add' x y := by simp [mulVec_add]
  map_smul' c x := by simp [mulVec_smul]
variable {M : Type} [AddCommGroup M]
end Mat
section Period
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}
noncomputable def dg (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) : Matrix (Fin g) (Fin g) ℂ :=
  diagonal fun i => ty i (a : E)
variable {D : Datum H} {ty : Fin g → (E →+* ℂ)}
end Period
end GlobalTheory.PeriodChart


