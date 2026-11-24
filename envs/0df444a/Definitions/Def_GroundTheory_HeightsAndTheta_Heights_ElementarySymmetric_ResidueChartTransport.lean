-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_ResidueChartTransport
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_ResidueChartTransport
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:37.104967+00:00
-- url     : https://prove2.me/theorems/ec0bd8a2-c35b-4e44-9580-ea1482de166a
-- title:
--   Residue Chart Transport
-- statement:
--   Definitions and structural lemmas for Residue Chart Transport, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/ResidueChartTransport.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_ResidueChartModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.KeyFormula
open Complex Matrix MvPolynomial
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman (Poly GradedMod gradedH gradedSys cechC cechZ)
noncomputable section
open RigSymForm
def ResidueChartTransport.Statement : Prop :=
  ∀ (P : RigSymForm ℂ) (a b r : ℕ) (x : Fin (r + 1) → P.Fn) (𝓜 : ResidueChartModel P a b x) (c₀ : ℤ),
    (∀ i : ℕ, 1 ≤ i → ∀ c : ℤ, c₀ ≤ c → Subsingleton (gradedH ℂ r 𝓜.M 𝓜.G i c)) →
    ∀ c : ℕ, c₀ ≤ c → ∀ (q : ℕ) (φ : Finset (Fin (r + 1)) → P.Fn),
      P.IsCocycle a (b + a * c) (q + 1) x φ → P.IsCoboundary a (b + a * c) q x φ
end
end GroundTheory.Heights₂.Heights.KeyFormula


