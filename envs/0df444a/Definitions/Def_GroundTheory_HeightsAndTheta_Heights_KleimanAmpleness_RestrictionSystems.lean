-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionSystems
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionSystems
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:30:19.818278+00:00
-- url     : https://prove2.me/theorems/851bda20-083b-4ed1-98a0-eb8fe63e5c51
-- title:
--   Restriction Systems
-- statement:
--   Definitions and structural lemmas for Restriction Systems, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionSystems.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionPowers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
def redSys (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (P : SubSystem k x Ω) (γ : Ω) : SubSystem k y K' where
  sub I := Submodule.span (chartRing k y I)
    ((fun q => redAt k x y (q / γ)) '' P.sub (liftChart hxy I))
  mono I J h z hz := by
    refine Submodule.span_induction (p := fun z _ => z ∈ Submodule.span (chartRing k y J)
      ((fun q => redAt k x y (q / γ)) '' P.sub (liftChart hxy J))) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, rfl⟩
      exact Submodule.subset_span ⟨q, P.mono _ _ h q hq, rfl⟩
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro a z _ hz; exact Submodule.smul_mem _ (chartIncl h a) hz
def RedGood (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (P : SubSystem k x Ω) (γ : Ω) : Prop :=
  ∀ (I : Chart y), ∀ q ∈ P.sub (liftChart hxy I), q / γ ∈ locAt k x y
variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
include hsp
end
end GroundTheory.Heights₂.Heights.Kleiman


