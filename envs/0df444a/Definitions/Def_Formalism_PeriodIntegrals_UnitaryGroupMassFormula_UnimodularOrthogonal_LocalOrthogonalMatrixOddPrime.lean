-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularOrthogonal_LocalOrthogonalMatrixOddPrime
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularOrthogonal_LocalOrthogonalMatrixOddPrime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:41.987867+00:00
-- url     : https://prove2.me/theorems/a1f350b6-27ff-4d23-aa50-d217cd108611
-- title:
--   Local Orthogonal Matrix Odd Prime
-- statement:
--   Definitions and structural lemmas for Local Orthogonal Matrix Odd Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularOrthogonal/LocalOrthogonalMatrixOddPrime.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularOrthogonal_MatOrthoLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnimodularOrthogonalQuadratic.Loc
open Matrix
section Star
variable {S : Type} [CommRing S] [StarRing S]
structure LocHyp (S : Type) [CommRing S] [StarRing S] : Prop where
  two : IsUnit (2 : S)
  add : ∀ x y : S, star x = x → star y = y → ¬IsUnit x → ¬IsUnit y → ¬IsUnit (x + y)
  norm : ∀ x : S, star x = x → IsUnit x → ∃ u, u * star u = x
def q {n : ℕ} (H : Matrix (Fin n) (Fin n) S) (v : Fin n → S) : S :=
  ∑ l, (∑ k, v k * H k l) * star (v l)
def elim {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) S) : Matrix (Fin (n + 1)) (Fin (n + 1)) S :=
  Matrix.of (Fin.cons (Pi.single 0 1 : Fin (n + 1) → S)
    fun i : Fin n => (Fin.cons (-A i.succ 0) (Pi.single i 1 : Fin n → S) : Fin (n + 1) → S))
def blk {n : ℕ} (P : Matrix (Fin n) (Fin n) S) : Matrix (Fin (n + 1)) (Fin (n + 1)) S :=
  Matrix.of (Fin.cons (Pi.single 0 1 : Fin (n + 1) → S)
    fun i : Fin n => (Fin.cons (0 : S) (P i) : Fin (n + 1) → S))
end Star
end PI.UnimodularOrthogonalQuadratic.Loc
namespace PI.UnimodularOrthogonalQuadratic
open Matrix
end PI.UnimodularOrthogonalQuadratic


