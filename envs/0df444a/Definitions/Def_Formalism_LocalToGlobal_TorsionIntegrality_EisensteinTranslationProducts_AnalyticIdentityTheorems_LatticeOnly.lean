-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_LatticeOnly
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_LatticeOnly
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:56:20.700643+00:00
-- url     : https://prove2.me/theorems/02781812-0819-474c-8b77-4affa88d64bb
-- title:
--   Lattice Only
-- statement:
--   Definitions and structural lemmas for Lattice Only, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/LatticeOnly.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.F
namespace LatOnly
variable {L L' : PeriodPair}
end LatOnly
namespace Homog
variable (L : PeriodPair) (c : ℂ) (hc : c ≠ 0)
lemma mem_scale (z : ℂ) : z ∈ (scalePair L c hc).lattice ↔ c⁻¹ * z ∈ L.lattice := by
  rw [PeriodPair.mem_lattice, PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, hmn⟩
    refine ⟨m, n, ?_⟩
    change (m : ℂ) * (c * L.ω₁) + (n : ℂ) * (c * L.ω₂) = z at hmn
    rw [← hmn, show c⁻¹ * ((m : ℂ) * (c * L.ω₁) + (n : ℂ) * (c * L.ω₂))
        = (c⁻¹ * c) * ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) by ring, inv_mul_cancel₀ hc, one_mul]
  · rintro ⟨m, n, hmn⟩
    refine ⟨m, n, ?_⟩
    change (m : ℂ) * (c * L.ω₁) + (n : ℂ) * (c * L.ω₂) = z
    rw [show (m : ℂ) * (c * L.ω₁) + (n : ℂ) * (c * L.ω₂) = c * ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) by ring,
      hmn, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
def scaleEquiv : L.lattice ≃ (scalePair L c hc).lattice where
  toFun l := ⟨c * (l : ℂ), (mem_scale L c hc _).2 (by rw [inv_mul_cancel_left₀ hc]; exact l.2)⟩
  invFun l := ⟨c⁻¹ * (l : ℂ), (mem_scale L c hc _).1 l.2⟩
  left_inv l := by ext; simp [hc]
  right_inv l := by ext; simp [hc]
end Homog
end Formalism.L2.Th1.F


