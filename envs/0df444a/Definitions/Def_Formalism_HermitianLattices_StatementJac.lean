-- Prove2me | Definitions.Def_Formalism_HermitianLattices_StatementJac
-- name    : Formalism_HermitianLattices_StatementJac
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:45:55.802808+00:00
-- url     : https://prove2.me/theorems/ae94b0ed-7306-4476-a22b-41c78c0528a5
-- title:
--   Statement Jac
-- statement:
--   Definitions and structural lemmas for Statement Jac, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/StatementJac.lean

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
namespace Formalism.HermitianLatticesTheory
def UnimodUnramUnique : Prop :=
  ∀ (R : Type) [CommRing R] (σ : R ≃+* R), (∀ x, σ (σ x) = x) →
    ∀ (R₀ : Subring R), (∀ x, x ∈ R₀ ↔ σ x = x) →
    ∀ [HenselianLocalRing R₀] [Finite (IsLocalRing.ResidueField R₀)],
    (∃ θ : R, IsUnit (θ - σ θ)) →
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) R), (A.map σ).transpose = A → IsUnit A.det →
      ∃ g : Matrix (Fin n) (Fin n) R, IsUnit g.det ∧ (g.map σ).transpose * A * g = 1
end Formalism.HermitianLatticesTheory


