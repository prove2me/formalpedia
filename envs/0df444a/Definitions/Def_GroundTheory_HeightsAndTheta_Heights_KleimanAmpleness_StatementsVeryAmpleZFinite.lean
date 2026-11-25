-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsVeryAmpleZFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsVeryAmpleZFinite
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:30:28.672215+00:00
-- url     : https://prove2.me/theorems/5b3434c9-7ceb-4153-ae96-416594df87c4
-- title:
--   Statements Very Ample ZFinite
-- statement:
--   Definitions and structural lemmas for Statements Very Ample ZFinite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StatementsVeryAmpleZFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleCechObj
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
open Filter
noncomputable section
universe u v w
def VeryAmpleZExtend.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E) (H : SubSystem S x Ω) (r : ℕ) (h : Fin (r + 1) → Ω), (∀ l, h l ∈ H.secs) →
    ∀ (J : Chart h) (j : Fin (r + 1)), j ∈ J.1 → ∀ c ∈ ampleRing H 1 (h j), ∀ K : Chart x,
      (∀ I : Chart x, ∃ e : ℕ, c ^ e * (xProd I ^ K.1.card / xProd K ^ I.1.card) ∈ ampleChart H 1 (h j) I) →
      ∀ f ∈ F.sub K, ∀ᶠ M in atTop, c ^ M • f ∈ secsOnZ F.toSubSystem H h J
def VeryAmpleZChartSpan.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubSystem S x E) (H : SubSystem S x Ω) (r : ℕ) (h : Fin (r + 1) → Ω), (∀ l, h l ∈ H.secs) →
    ∀ (I : Chart x) (J : Chart h) (g : Finset E), F.sub I ≤ Submodule.span (chartRing S x I) (g : Set E) →
      ∀ e ∈ secsOnZChart F H h I J, ∃ β : E → Ω,
        (∀ y ∈ g, β y ∈ ampleChart H J.1.card (xProd J) I) ∧ e = ∑ y ∈ g, β y • y
def VeryAmpleZChartRing.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (H : LineBundle S x) (r : ℕ) (h : Fin (r + 1) → Ω), IsVeryAmpleBy H.toSubSystem h →
    ∀ (J : Chart h) (j : Fin (r + 1)), j ∈ J.1 → ∀ c ∈ ampleRing H.toSubSystem 1 (h j), ∀ K : Chart x,
      (∀ I : Chart x, ∃ e : ℕ,
        c ^ e * (xProd I ^ K.1.card / xProd K ^ I.1.card) ∈ ampleChart H.toSubSystem 1 (h j) I) →
      ∀ α ∈ ampleChart H.toSubSystem J.1.card (xProd J) K, ∀ᶠ M in atTop, c ^ M * α ∈ chartRing S h J
theorem genericPt_one_zero_ne_zero (k : Type u) [Field k] : genericPt k 1 0 ≠ 0 := by
  intro h0
  have := (map_eq_zero_iff _ (IsFractionRing.injective (Poly k 1) (FractionRing (Poly k 1)))).mp h0
  exact MvPolynomial.X_ne_zero _ this
def lineChartZero (k : Type u) [Field k] : Chart (genericPt k 1) := singleChart (genericPt_one_zero_ne_zero k)
end
end GroundTheory.Heights₂.Heights.Kleiman


