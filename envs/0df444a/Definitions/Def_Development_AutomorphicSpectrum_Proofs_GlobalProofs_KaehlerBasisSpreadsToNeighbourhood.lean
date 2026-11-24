-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_KaehlerBasisSpreadsToNeighbourhood
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_KaehlerBasisSpreadsToNeighbourhood
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:50.189499+00:00
-- url     : https://prove2.me/theorems/71621ce5-8fbb-4887-97cd-c9061236cbd9
-- title:
--   Kaehler Basis Spreads To Neighbourhood
-- statement:
--   Definitions and structural lemmas for Kaehler Basis Spreads To Neighbourhood, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/KaehlerBasisSpreadsToNeighbourhood.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
namespace GlobalTheory.CompanionTheory.KaehlerSpread
open KaehlerDifferential
noncomputable abbrev diffMap (K : Type) {A : Type} [Field K] [CommRing A] [Algebra K A] {n : ℕ}
    (x : Fin n → A) : (Fin n →₀ A) →ₗ[A] Ω[A⁄K] :=
  Finsupp.linearCombination A fun i => D K A (x i)
end GlobalTheory.CompanionTheory.KaehlerSpread


