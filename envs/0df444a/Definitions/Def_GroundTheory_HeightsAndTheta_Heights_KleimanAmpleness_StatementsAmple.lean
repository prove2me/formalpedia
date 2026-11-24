-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsAmple
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsAmple
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:38.259667+00:00
-- url     : https://prove2.me/theorems/923c4a3f-2ade-406e-87ea-223723525722
-- title:
--   Statements Ample
-- statement:
--   Definitions and structural lemmas for Statements Ample, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StatementsAmple.lean

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
universe u w
def AmpleCover.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (H : LineBundle S x) (A : AmpleData S x H) (F : SubSystem S x Ω),
    (∀ (j : Fin (A.r + 1)) (I : Chart x) (y : Ω), y ∈ F.sub I → ∃ e : ℕ,
      y * A.h j ^ e ∈
        Submodule.span (chartRing S x I) (F.secs : Set Ω) * (H.pow (A.m * e)).sub I) →
    F.Generated
def AmpleTwistLocal.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (H : LineBundle S x) (A : AmpleData S x H) (Q : LineBundle S x) (b : ℕ)
    (j : Fin (A.r + 1)),
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (I : Chart x) (y : Ω), y ∈ (Q.twist (H.pow (b + A.m * n))).sub I →
      ∃ e : ℕ, y * A.h j ^ e ∈
        Submodule.span (chartRing S x I) ((Q.twist (H.pow (b + A.m * n))).secs : Set Ω) *
          (H.pow (A.m * e)).sub I
section Hypotheses
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (x : Fin (N + 1) → Ω)
variable (k : Type u) [Field k]
end Hypotheses
end
end GroundTheory.Heights₂.Heights.Kleiman


