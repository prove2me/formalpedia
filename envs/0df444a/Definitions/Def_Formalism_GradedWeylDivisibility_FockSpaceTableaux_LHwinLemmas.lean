-- Prove2me | Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwinLemmas
-- name    : Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwinLemmas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:56:55.002669+00:00
-- url     : https://prove2.me/theorems/b5154f1e-4d1a-43c9-9a23-fbc16d79cd7c
-- title:
--   LHwin Lemmas
-- statement:
--   Definitions and structural lemmas for LHwin Lemmas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwinLemmas.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
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
def lhwinHt (r n : ℕ) : Fin r × Fin n → ℤ := fun v => (v.1.val : ℤ)
def LhwinShift {R : Type*} [CommRing R] {r n : ℕ} (P : Polynomial (MvPolynomial (Fin r × Fin n) R))
    (μ δ : ℤ) : Prop :=
  ∀ k : ℕ, IsWeightedHomogeneous (lhwinHt r n) (P.coeff k) (μ + k * δ)
end Formalism.GradedWeylDivisibility


