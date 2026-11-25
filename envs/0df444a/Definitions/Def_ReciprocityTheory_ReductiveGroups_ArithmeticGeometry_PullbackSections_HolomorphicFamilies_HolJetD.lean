-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T14:42:52.197817+00:00
-- url     : https://prove2.me/theorems/42ef3b80-4a80-4aa8-9fd1-0ef9d6bb4a68
-- title:
--   Hol Jet D
-- statement:
--   Definitions and structural lemmas for Hol Jet D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetD.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
section JetAlg
variable {K : Type} [Field K] {ι : Type} {m : ℕ}
end JetAlg
variable {g : ℕ} {Y : Scheme.{0}}
def jetScaleP (m : ℕ) (c : Fin g → ℂ) : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m :=
  jetMap (fun p => MvPolynomial.C (c p.2) * MvPolynomial.X p)
    fun p => Ideal.mul_mem_left _ _ (X_mem_orig p)
end ReciprocityTheory.ChartRestriction.G.PullbackSections


