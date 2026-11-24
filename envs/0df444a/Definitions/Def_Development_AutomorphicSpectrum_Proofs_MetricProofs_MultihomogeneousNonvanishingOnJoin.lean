-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MultihomogeneousNonvanishingOnJoin
-- name    : Development_AutomorphicSpectrum_Proofs_MetricProofs_MultihomogeneousNonvanishingOnJoin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:03:17.456264+00:00
-- url     : https://prove2.me/theorems/b195e608-fdb8-47b2-b7ee-9d512d06d735
-- title:
--   Multihomogeneous Nonvanishing On Join
-- statement:
--   Definitions and structural lemmas for Multihomogeneous Nonvanishing On Join, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/MultihomogeneousNonvanishingOnJoin.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Proportional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
namespace GlobalTheory.CompanionTheory.Ar.Giv
namespace ResProj
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
variable {M : ℕ}
local notation "𝔅" => (fun _ : Unit => Fin M)
section Forms
variable {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ _ : Unit, Fin M) → Ω) {G : Fin M → MRing ι} {g : K → ℕ}
end Forms
noncomputable def subst (G : Fin M → MRing ι) : MRing (joinIdx ι 𝔅) →ₐ[ℤ] MRing ι :=
  aeval (joinVec (fun q => X q) fun q => G q.2)
end ResProj
end GlobalTheory.CompanionTheory.Ar.Giv


