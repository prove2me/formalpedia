-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__HeckeFunctionalEquationAbs_56207734e1ed91e8
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__HeckeFunctionalEquationAbs_56207734e1ed91e8
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:01:17.169412+00:00
-- url     : https://prove2.me/theorems/aa3c2e82-b8f2-479e-8432-3d765b41c48a
-- title:
--   Hecke Functional Equation Abs
-- statement:
--   Definitions and structural lemmas for Hecke Functional Equation Abs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/HeckeFunctionalEquationAbs.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds
namespace GlobalTheory.Published
def HeckeFunctionalEquationAbs : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (χ : HChar E) (n : I → ℤ) (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) (Λ Λ' : ℂ → ℂ), IsUnitary χ →
      Formalism.L2.Host.HChar.HasInf χ φ n → (∃ i, n i ≠ 0) → (∀ v, ExpAt χ v (a v)) → IsCompletedL χ n Λ →
      IsCompletedL χ⁻¹ (fun i => -n i) Λ' → ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ s : ℂ,
        Λ s = ε * ((((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℂ) ^ (1 / 2 - s)) * Λ' (1 - s)
end GlobalTheory.Published
end


