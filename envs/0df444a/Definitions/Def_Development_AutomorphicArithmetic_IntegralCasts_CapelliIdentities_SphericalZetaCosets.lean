-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SphericalZetaCosets
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SphericalZetaCosets
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:25.110875+00:00
-- url     : https://prove2.me/theorems/2ecb4609-e083-4c5b-b66f-2315146d2cb1
-- title:
--   Spherical Zeta Cosets
-- statement:
--   Definitions and structural lemmas for Spherical Zeta Cosets, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SphericalZetaCosets.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ValuativeRel
namespace UpperTheory.Reformulated.B.SphericalZetaCosets
section Sums
end Sums
section Hermite
variable {R : Type} [CommRing R] {c : ℕ}
abbrev Row (π : R) (i : Fin c) : Type :=
  Σ n : ℕ, ({j : Fin c // i < j} → R ⧸ Ideal.span {π ^ n})
noncomputable def rowFn (π : R) (i : Fin c) (x : Row π i) (j : Fin c) : R :=
  if h : i < j then (x.2 ⟨j, h⟩).out else if j = i then π ^ x.1 else 0
noncomputable def hnf (π : R) (p : ∀ i : Fin c, Row π i) : Matrix (Fin c) (Fin c) R :=
  Matrix.of fun i j => rowFn π i (p i) j
end Hermite
end UpperTheory.Reformulated.B.SphericalZetaCosets


