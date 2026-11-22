-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuInf
-- name    : Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuInf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:46:20.05389+00:00
-- url     : https://prove2.me/theorems/a0ad0370-7137-4b68-86af-9ea3b5f4a2ec
-- title:
--   Nu Inf
-- statement:
--   Definitions and structural lemmas for Nu Inf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/NuInf.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace KStar.Tree
variable {Γ : Type} [Group Γ] (l : ℕ) [Fact l.Prime] (ε : Γ →* ℤ_[l]ˣ) (n : ℕ)
def nuOf : ℕ := sInf {k : ℕ | ∃ g, ¬ (l : ℤ_[l]) ^ (k + 1) ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1}
def nuInf : ℕ∞ := ⨅ g, emultiplicity (l : ℤ_[l]) (((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1)
def cyc (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] : (Ω ≃ₐ[E] Ω) →* ℤ_[l]ˣ :=
  (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (Ω ≃ₐ[E] Ω) Ω)
end KStar.Tree


