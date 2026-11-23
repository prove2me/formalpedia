-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsForallAbvSubLt
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsForallAbvSubLt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:32.153538+00:00
-- url     : https://prove2.me/theorems/f4cd7c77-0342-48ef-8a09-d3a3061bfea0
-- title:
--   Exists Forall Abv Sub Lt
-- statement:
--   Definitions and structural lemmas for Exists Forall Abv Sub Lt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsForallAbvSubLt.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
namespace GlobalTheory.LocalQuad.Approx
variable {F : Type} [Field F] [NumberField F]
noncomputable def abv (T : Finset (HeightOneSpectrum (𝓞 F))) :
    T ⊕ (F →+* ℝ) → AbsoluteValue F ℝ
  | Sum.inl v => NumberField.HeightOneSpectrum.adicAbv F v.1
  | Sum.inr σ => (InfinitePlace.mk (Complex.ofRealHom.comp σ)).1
end GlobalTheory.LocalQuad.Approx


