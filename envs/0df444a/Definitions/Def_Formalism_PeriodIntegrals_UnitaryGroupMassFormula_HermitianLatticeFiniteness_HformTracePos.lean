-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianLatticeFiniteness_HformTracePos
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianLatticeFiniteness_HformTracePos
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:40:52.563536+00:00
-- url     : https://prove2.me/theorems/a5fa8224-e930-4075-95a0-4a432f80da72
-- title:
--   Hform Trace Pos
-- statement:
--   Definitions and structural lemmas for Hform Trace Pos, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianLatticeFiniteness/HformTracePos.lean

import Definitions.Def_Formalism_PeriodIntegrals_HermLatFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped ComplexOrder
noncomputable section
namespace PI.HermLatFin.UnitaryGroupMassFormula
variable {E : Type} [Field E] [NumberField E]
@[instance_reducible]
def starOf (σ : E →+* E) (h2 : ∀ a, σ (σ a) = a) : StarRing E where
  star := σ
  star_involutive := h2
  star_mul a b := by
    show σ (a * b) = σ b * σ a
    rw [map_mul, mul_comm]
  star_add a b := map_add σ a b
section Form
variable [StarRing E] {n : ℕ}
def hform (J : Matrix (Fin n) (Fin n) E) : (Fin n → E) →ₗ⋆[E] (Fin n → E) →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E)
    (fun x y => ∑ i, ∑ j, star (x i) * J i j * y j)
    (fun x x' y => by
      simp only [Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, star_mul', starRingEnd_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring)
    (fun x y y' => by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring)
end Form
section Pos
variable [StarRing E] {n : ℕ}
end Pos
end PI.HermLatFin.UnitaryGroupMassFormula


