-- Prove2me | Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowstLemmas
-- name    : Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowstLemmas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:53:35.762801+00:00
-- url     : https://prove2.me/theorems/eacf6bdc-87d8-454d-a4a8-fa5670feb2e0
-- title:
--   LRowst Lemmas
-- statement:
--   Definitions and structural lemmas for LRowst Lemmas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LRowstLemmas.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.GradedWeylDivisibility
section General
variable {R : Type*} [CommRing R] {σ τ M : Type*} [AddCommMonoid M]
end General
def rowActO (R : Type*) [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R) :
    MvPolynomial (Option (Fin r × Fin n)) R →ₐ[R] MvPolynomial (Option (Fin r × Fin n)) R :=
  aeval fun o => Option.elim o (X none) (fun v => ∑ b : Fin r, C (g v.1 b) * X (some (b, v.2)))
def rowWO (r n : ℕ) : Option (Fin r × Fin n) → (Fin r → ℕ) :=
  fun o => Option.elim o 0 (fun v => Pi.single v.1 1)
end Formalism.GradedWeylDivisibility


