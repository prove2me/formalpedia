-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_DenseChart
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_DenseChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:28.685333+00:00
-- url     : https://prove2.me/theorems/50b7861b-cd9b-467b-bf90-83a8d41db72f
-- title:
--   Dense Chart
-- statement:
--   Definitions and structural lemmas for Dense Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/DenseChart.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace ArithVariety
variable (P : ArithVariety n)
abbrev CoordRing : Type := MvPolynomial (Coord n) ℤ ⧸ P.ideal
instance isPrime_ideal : P.ideal.IsPrime := P.isPrime
instance : IsDomain P.CoordRing := Ideal.Quotient.isDomain _
instance : CharZero P.CoordRing :=
  charZero_of_inj_zero fun m hm ↦ by
    have h : (C (m : ℤ) : MvPolynomial (Coord n) ℤ) ∈ P.ideal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa using hm
    exact_mod_cast P.horizontal _ h
abbrev FunField : Type := FractionRing P.CoordRing
def mkF : MvPolynomial (Coord n) ℤ →+* P.FunField :=
  (algebraMap P.CoordRing P.FunField).comp (Ideal.Quotient.mk P.ideal)
variable (c : (k : ι) → Fin (n k + 1))
def chartCoord (v : Coord n) : P.FunField := P.mkF (X v) / P.mkF (X ⟨v.1, c v.1⟩)
def chartMap : MvPolynomial (Coord n) ℚ →ₐ[ℚ] P.FunField := aeval (P.chartCoord c)
abbrev ChartAlg : Subalgebra ℚ P.FunField := (P.chartMap c).range
instance : Algebra.FiniteType ℚ (P.ChartAlg c) :=
  Algebra.FiniteType.of_surjective (P.chartMap c).rangeRestrict (AlgHom.rangeRestrict_surjective _)
def chartPoint (ψ : P.ChartAlg c →ₐ[ℚ] AlgebraicClosure ℚ) : Cone n (AlgebraicClosure ℚ) :=
  fun k i ↦ ψ ((P.chartMap c).rangeRestrict (X ⟨k, i⟩))
end ArithVariety
end
end GroundTheory.Heights₂.Heights


