-- Prove2me | Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_Transport
-- name    : ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_Transport
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:03:22.031797+00:00
-- url     : https://prove2.me/theorems/03425096-271b-4e32-91a6-974b1a78687f
-- title:
--   Transport
-- statement:
--   Definitions and structural lemmas for Transport, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/Transport.lean

import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA
import Theorems.Thm_P2M_ReciprocityTheory_Gal_ContAction_comp__44f330b68efd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.Neutral.Bridge
open ReciprocityTheory.Gal
variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R] {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
def FinCd2 (rho : Representation R G M) : Prop :=
  Finite (H0 rho) ∧ Finite (H1 rho) ∧ Finite (H2 rho) ∧ ∀ n, 3 ≤ n → Subsingleton (Hn rho n)
def DualityFor (χ : G →* Rˣ) (rho : Representation R G M) (hrho : ContAction rho) : Prop :=
  Nonempty (H2 (charRep χ) ≃ₗ[R] R) ∧
    Function.Bijective (cupH0H2TwistedDual χ rho (MonoidHom.id _)) ∧
    Function.Bijective (cupH1H1TwistedDual χ rho (MonoidHom.id _) (hrho.comp' continuous_id)) ∧
    Function.Bijective (cupH1H1TwistedDual χ rho (MonoidHom.id _) (hrho.comp' continuous_id)).flip ∧
    Function.Bijective (cup20 χ rho (MonoidHom.id _))
theorem contAction_comp (e : G ≃ₜ* G') {rho : Representation R G' M} (h : ContAction rho) :
    ContAction (rho.comp (e : G →* G')) := by
  unfold ReciprocityTheory.Gal.ContAction at h ⊢
  exact h.comp ((map_continuous e).prodMap continuous_id)
end ReciprocityTheory.Neutral.Bridge


