-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolicBase
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolicBase
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:33:18.746604+00:00
-- url     : https://prove2.me/theorems/b2c18423-ec94-4d10-aec7-79ff1b70bb06
-- title:
--   GGMirabolic Base
-- statement:
--   Definitions and structural lemmas for GGMirabolic Base, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GGMirabolicBase.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.SG.GGMirabolic
noncomputable section
open Classical
section One
variable {F : Type} [Field F] [Fintype F] (k : ℕ)
def IsUni (x : GL (Fin k) F) : Prop :=
  (∀ i : Fin k, (x : Matrix (Fin k) (Fin k) F) i i = 1) ∧
    ∀ i j : Fin k, j < i → (x : Matrix (Fin k) (Fin k) F) i j = 0
def superdiag (x : Matrix (Fin k) (Fin k) F) : F :=
  ∑ i : Fin k, ∑ j : Fin k, if (j : ℕ) = (i : ℕ) + 1 then x i j else 0
variable {k}
def psiU (ψ₀ : AddChar F ℂ) (u : GL (Fin k) F) : ℂ := ψ₀ (superdiag k (u : Matrix (Fin k) (Fin k) F))
def IsWhit (ψ₀ : AddChar F ℂ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin k) F) V) (ℓ : Module.Dual ℂ V) : Prop :=
  ∀ u : GL (Fin k) F, IsUni k u → ∀ v : V, ℓ (π u v) = psiU ψ₀ u * ℓ v
end One
def GelfandGraevMultOne : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (ψ₀ : AddChar F ℂ), ψ₀ ≠ 1 →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (π : Representation ℂ (GL (Fin k) F) V), π.IsIrreducible →
      ∀ ℓ₁ ℓ₂ : Module.Dual ℂ V, IsWhit ψ₀ π ℓ₁ → IsWhit ψ₀ π ℓ₂ → ℓ₁ ≠ 0 → ∃ c : ℂ, ℓ₂ = c • ℓ₁
end
end Formalism.L2.SG.GGMirabolic


