-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_HomogeneousFormNonvanishingPoint
-- name    : Development_AutomorphicSpectrum_Proofs_GeometryProofs_HomogeneousFormNonvanishingPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:19.655802+00:00
-- url     : https://prove2.me/theorems/cce2f581-5aae-43cf-b307-ebd226ffcd70
-- title:
--   Homogeneous Form Nonvanishing Point
-- statement:
--   Definitions and structural lemmas for Homogeneous Form Nonvanishing Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/HomogeneousFormNonvanishingPoint.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_SncChartPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.SncRes
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.SegreChart
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def segForm {N : ℕ} (E : Fin (N + 1) ≃ ((k : K) → ι k)) (Gz : MvPolynomial (Fin (N + 1)) ℤ) : MRing ι :=
  aeval (fun j => ∏ k, (X ⟨k, E j k⟩ : MRing ι)) Gz
section Join
variable {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
end Join
section Chart
variable {Ω : Type} [Field Ω] [CharZero Ω] {r : ℕ}
abbrev joinPt (y : (Σ k, ι k) → Ω) (x' : Fin (r + 1) → Ω) :
    (Σ k, joinIdx ι (fun _ : Unit => Fin (r + 1)) k) → Ω :=
  joinVec y fun p : (Σ _ : Unit, Fin (r + 1)) => x' p.2
end Chart
end GlobalTheory.CompanionTheory.Ar.SegreChart


