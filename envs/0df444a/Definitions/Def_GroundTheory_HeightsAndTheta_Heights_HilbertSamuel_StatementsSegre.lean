-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegre
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegre
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:29:25.553531+00:00
-- url     : https://prove2.me/theorems/e1df9207-3e96-4885-b1a0-659deb70ae1a
-- title:
--   Statements Segre
-- statement:
--   Definitions and structural lemmas for Statements Segre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsSegre.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsMultiDegreePositive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} (F : Type) [Field F]
def segreMap : MRing (fun _ : Unit => ∀ k, ι k) F →ₐ[F] MRing ι F :=
  aeval fun v => ∏ k, X ⟨k, v.2 k⟩
def segrePrime (q : Ideal (MRing ι F)) : Ideal (MRing (fun _ : Unit => ∀ k, ι k) F) :=
  q.comap (segreMap F)
instance segrePrime.isPrime (q : Ideal (MRing ι F)) [q.IsPrime] : (segrePrime F q).IsPrime :=
  Ideal.comap_isPrime _ _
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


