-- Prove2me | Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
-- name    : Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:47.037901+00:00
-- url     : https://prove2.me/theorems/fc4f22e4-4ded-4e4e-bae2-d5a9d05a08b8
-- title:
--   LEhw Lemmas
-- statement:
--   Definitions and structural lemmas for LEhw Lemmas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LEhwLemmas.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylDominanceOf
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
def LehwShift {R : Type*} [CommRing R] {r n : ℕ} (w : Fin r × Fin n → ℤ)
    (P : Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ δ : ℤ) : Prop :=
  ∀ k : ℕ, IsWeightedHomogeneous w (P.coeff k) (μ + k * δ)
def lehwP {r n : ℕ} (a : Fin r) : Fin r × Fin n → ℤ := fun v => if v.1.val ≤ a.val then 1 else 0
end Formalism.GradedWeylDivisibility


