-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemHHaOfCoeffFunctional
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemHHaOfCoeffFunctional
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:43.204801+00:00
-- url     : https://prove2.me/theorems/988006ef-195c-4912-a102-95145e743f1e
-- title:
--   Mem HHa Of Coeff Functional
-- statement:
--   Definitions and structural lemmas for Mem HHa Of Coeff Functional, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MemHHaOfCoeffFunctional.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CoeffFunctional
open MvPolynomial
variable {σ K L : Type} [Field K] [Field L] [Algebra K L]
def coeffMap (φ : L →ₗ[K] K) (P : MvPolynomial σ L) : MvPolynomial σ K :=
  ∑ μ ∈ P.support, monomial μ (φ (P.coeff μ))
variable {T : Type} (r : T → ℕ) (n : ℕ)
end GlobalTheory.CoeffFunctional


