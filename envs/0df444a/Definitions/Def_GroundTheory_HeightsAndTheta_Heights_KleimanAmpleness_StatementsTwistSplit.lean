-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSplit
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSplit
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T05:56:09.31339+00:00
-- url     : https://prove2.me/theorems/e41c7054-e4be-5ca8-9582-59e5e982d622
-- title:
--   Statements Twist Split
-- statement:
--   Definitions and structural lemmas for Statements Twist Split, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StatementsTwistSplit.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
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
universe u v w
def TwistSplit.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (M₀ : FinGradedSub (S := S) (x := x) Ω) (G B : SubSystem S x Ω) (r : ℕ)
    (η : Fin (r + 1) → Ω), (∀ I, M₀.tilde 0 I = G.sub I) →
    (∀ j, η j ∈ B.secs) → (∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) →
    ∃ (M : Type w) (_ : AddCommGroup M) (_ : Module (Poly (MvPolynomial (Fin (r + 1)) S) N) M)
      (_ : Module (MvPolynomial (Fin (r + 1)) S) M)
      (_ : IsScalarTower (MvPolynomial (Fin (r + 1)) S) (Poly (MvPolynomial (Fin (r + 1)) S) N) M)
      (𝓜 : GradedPMod (MvPolynomial (Fin (r + 1)) S) N M),
      Module.Finite (Poly (MvPolynomial (Fin (r + 1)) S) N) M ∧
      ∀ (b : ℕ) (c : ℤ) (i : ℕ),
        ∃ (ι : ((G.twist (B.pow b)).twist (twistSys S x c)).H i →+ cohom 𝓜 i c)
          (π : cohom 𝓜 i c →+ ((G.twist (B.pow b)).twist (twistSys S x c)).H i), ∀ z, π (ι z) = z
section Hypotheses
variable (k : Type u) [Field k] (N : ℕ)
end Hypotheses
end
end GroundTheory.Heights₂.Heights.Kleiman


