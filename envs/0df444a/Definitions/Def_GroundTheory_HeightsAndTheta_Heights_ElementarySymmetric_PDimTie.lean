-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PDimTie
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PDimTie
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:23:20.337605+00:00
-- url     : https://prove2.me/theorems/1d2abc8a-f196-4dde-a6e5-3c4f30ed6dab
-- title:
--   PDim Tie
-- statement:
--   Definitions and structural lemmas for PDim Tie, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PDimTie.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Algebra Cardinal
noncomputable section
universe u w
namespace DimTie
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
abbrev ratioRing (y : Fin (N + 1) → Ω) : Subalgebra k Ω :=
  Algebra.adjoin k {a | ∃ i j, y i ≠ 0 ∧ a = y j / y i}
theorem ratio_mem (y : Fin (N + 1) → Ω) {i : Fin (N + 1)} (hi : y i ≠ 0) (j : Fin (N + 1)) :
    y j / y i ∈ ratioRing (k := k) y :=
  Algebra.subset_adjoin ⟨i, j, hi, rfl⟩
section Cone
variable (y : Fin (N + 1) → Ω) {i₀ : Fin (N + 1)} (hi₀ : y i₀ ≠ 0)
def ratio (j : Fin (N + 1)) : ratioRing (k := k) y := ⟨y j / y i₀, ratio_mem y hi₀ j⟩
def dehom : Poly k N →ₐ[k] Polynomial (ratioRing (k := k) y) :=
  aeval fun j => Polynomial.C (ratio y hi₀ j) * Polynomial.X
variable (i₀) in

def rehom : Polynomial (ratioRing (k := k) y) →ₐ[k] Polynomial Ω :=
  ((Polynomial.aeval (R := Ω) (Polynomial.C (y i₀) * Polynomial.X)).restrictScalars k).comp
    (Polynomial.mapAlgHom (ratioRing (k := k) y).val)
end Cone
end DimTie
end
end GroundTheory.Heights₂.Heights.Kleiman


