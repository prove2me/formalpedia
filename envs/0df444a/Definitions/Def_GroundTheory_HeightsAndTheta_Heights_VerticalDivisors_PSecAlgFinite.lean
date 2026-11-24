-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecAlgFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecAlgFinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:05.064889+00:00
-- url     : https://prove2.me/theorems/c82722c3-87c0-49b4-bd64-f5c2296ebbb5
-- title:
--   PSec Alg Finite
-- statement:
--   Definitions and structural lemmas for PSec Alg Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecAlgFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
namespace SecAlgFinite
variable {k E : Type} [Field k] [Field E] [Algebra k E] {n e : ℕ}
def lineSub (y : Par e n → E) (m : Fin n) (ij : Fin (e + 1) × Fin n) : Polynomial E :=
  Fin.cases (motive := fun _ => Polynomial E)
    (Polynomial.C (y (.inr ij.2)) * Polynomial.X - if ij.2 = m then 1 else 0)
    (fun i => Polynomial.C (y (.inl (i, ij.2)))) ij.1
def transVar (m : Fin n) (ij : Fin (e + 1) × Fin n) : MvPolynomial (Par e n) k :=
  Fin.cases (motive := fun _ => MvPolynomial (Par e n) k)
    (X (.inr ij.2) - if ij.2 = m then 1 else 0) (fun i => X (.inl (i, ij.2))) ij.1
def transVarInv (m : Fin n) : Par e n → MvPolynomial (Fin (e + 1) × Fin n) k
  | .inl ij => X (ij.1.succ, ij.2)
  | .inr j => X (0, j) + if j = m then 1 else 0
end SecAlgFinite
end
end GroundTheory.Heights₂.Heights.Vertical


