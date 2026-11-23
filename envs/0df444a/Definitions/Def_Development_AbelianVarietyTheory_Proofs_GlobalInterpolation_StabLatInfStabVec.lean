-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_StabLatInfStabVec
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_StabLatInfStabVec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:15.029607+00:00
-- url     : https://prove2.me/theorems/76f99ae6-ea8c-494b-9c5f-d9056573b678
-- title:
--   Stab Lat Inf Stab Vec
-- statement:
--   Definitions and structural lemmas for Stab Lat Inf Stab Vec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/StabLatInfStabVec.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
namespace GlobalTheory.UnitVectorStabEq
section General
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
end General
section Place
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))
end Place
end GlobalTheory.UnitVectorStabEq


