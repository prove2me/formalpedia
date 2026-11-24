-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCechDSq
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCechDSq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:34.471725+00:00
-- url     : https://prove2.me/theorems/54be7818-ad9a-4fe8-89a7-59c88fea66ac
-- title:
--   Statements Cech DSq
-- statement:
--   Definitions and structural lemmas for Statements Cech DSq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StatementsCechDSq.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
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
universe u v
def CechDSq.Statement : Prop :=
  ∀ (n : ℕ) (U : Finset (Fin n)) (R : Type u) [CommRing R] (G : Cell U → Type v)
    [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] (ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J),
    (∀ (I J K : Cell U) (hIJ : I.1 ⊆ J.1) (hJK : J.1 ⊆ K.1),
      (ρ J K hJK).comp (ρ I J hIJ) = ρ I K (hIJ.trans hJK)) →
    ∀ (i : ℕ) (s : Cech.Cochain G i), Cech.d G ρ (i + 1) (Cech.d G ρ i s) = 0
section Hypotheses
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
end Hypotheses
end
end GroundTheory.Heights₂.Heights.Kleiman


