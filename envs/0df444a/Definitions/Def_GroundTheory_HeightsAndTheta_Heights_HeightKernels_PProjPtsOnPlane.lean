-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjPtsOnPlane
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjPtsOnPlane
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:33.081579+00:00
-- url     : https://prove2.me/theorems/a8424be8-a9ac-44ad-8365-993f4d9685d9
-- title:
--   PProj Pts On Plane
-- statement:
--   Definitions and structural lemmas for PProj Pts On Plane, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjPtsOnPlane.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
namespace ProjectivePointsOnPlane
variable {K : Type} [Field K] [NumberField K] {i : ℕ}
def mulMat (α : 𝓞 K) (m n : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) : ℤ :=
  (RingOfIntegers.basis K).repr (α * RingOfIntegers.basis K m) n
def lin (α : 𝓞 K) (Z : ProjIdx K i → ℂ) : ProjIdx K i → ℂ :=
  fun q => ∑ n, (mulMat α q.1 n : ℂ) * Z (n, q.2)
def lform (α : 𝓞 K) (q : ProjIdx K i) : MRing (projBlocks K i) :=
  ∑ n, C (mulMat α q.1 n) * X ⟨(), (n, q.2)⟩
def quad (α : 𝓞 K) (p q : ProjIdx K i) : MRing (projBlocks K i) :=
  X ⟨(), p⟩ * lform α q - lform α p * X ⟨(), q⟩
end ProjectivePointsOnPlane
end
end GroundTheory.Heights₂.Heights


