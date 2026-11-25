-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSectionObj
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSectionObj
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:02:10.556021+00:00
-- url     : https://prove2.me/theorems/da022e74-1fbe-476b-93bd-a3b8217cb7e1
-- title:
--   Snapper Section Obj
-- statement:
--   Definitions and structural lemmas for Snapper Section Obj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/SnapperSectionObj.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
variable (S x) in

def spanBundle (s : Ω) (hs : s ≠ 0) : LineBundle S x where
  sub I := Submodule.span (chartRing S x I) {s}
  mono I J h y hy := by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact Submodule.mem_span_singleton.mpr ⟨chartIncl h a, rfl⟩
  mem_iff I J h y := by
    constructor
    · intro hy
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
      obtain ⟨a, ha, hab⟩ := exists_isUnit_mul_mem h b
      refine ⟨a, ha, Submodule.mem_span_singleton.mpr ⟨⟨_, hab⟩, ?_⟩⟩
      rw [chartRing_smul_def, chartRing_smul_def, smul_eq_mul, mul_assoc]
    · rintro ⟨a, ⟨u, hu⟩, hay⟩
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hay
      have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
        have := congrArg Subtype.val (Units.inv_mul u)
        rw [hu] at this
        exact this
      refine Submodule.mem_span_singleton.mpr ⟨(↑u⁻¹ : chartRing S x J) * chartIncl h c, ?_⟩
      rw [chartRing_smul_def, Subalgebra.coe_mul, mul_assoc]
      change (↑u⁻¹ : chartRing S x J).1 * ((c : Ω) * s) = y
      rw [← chartRing_smul_def c s, hc, smul_eq_mul, ← mul_assoc, hinv, one_mul]
  fg _ := Submodule.fg_span_singleton s
  invertible I := ⟨Submodule.span (chartRing S x I) {s⁻¹}, by
    rw [Submodule.span_mul_span, Set.singleton_mul_singleton, mul_inv_cancel₀ hs, ← Submodule.one_eq_span]⟩
variable {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
def SubFamily.sup (F G : SubFamily S x E) : SubFamily S x E where
  sub I := F.sub I ⊔ G.sub I
  mono I J h y hy := by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    exact Submodule.mem_sup.mpr ⟨a, F.mono I J h a ha, b, G.mono I J h b hb, rfl⟩
  mem_iff I J h y := by
    constructor
    · intro hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨u, hu, hua⟩ := (F.mem_iff I J h a).mp ha
      obtain ⟨v, hv, hvb⟩ := (G.mem_iff I J h b).mp hb
      refine ⟨u * v, by rw [map_mul]; exact hu.mul hv, ?_⟩
      have : ((u * v : chartRing S x I) : Ω) • (a + b) = v • ((u : Ω) • a) + u • ((v : Ω) • b) := by
        rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_smul, smul_smul, Subalgebra.coe_mul, smul_add,
          mul_comm (v : Ω) (u : Ω)]
      rw [this]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ v hua))
        (Submodule.mem_sup_right (Submodule.smul_mem _ u hvb))
    · rintro ⟨a, ⟨u, hu⟩, hay⟩
      have hJ : (a : Ω) • y ∈ F.sub J ⊔ G.sub J := by
        obtain ⟨c, hc, d, hd, hcd⟩ := Submodule.mem_sup.mp hay
        exact Submodule.mem_sup.mpr ⟨c, F.mono I J h c hc, d, G.mono I J h d hd, hcd⟩
      have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
        have := congrArg Subtype.val (Units.inv_mul u)
        rw [hu] at this
        exact this
      have hy : y = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • y) := by
        rw [Subalgebra.smul_def, smul_smul, hinv, one_smul]
      rw [hy]
      exact Submodule.smul_mem _ _ hJ
end
end GroundTheory.Heights₂.Heights.Kleiman


