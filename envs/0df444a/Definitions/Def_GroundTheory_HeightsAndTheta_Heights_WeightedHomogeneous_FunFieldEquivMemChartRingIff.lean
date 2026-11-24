-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_FunFieldEquivMemChartRingIff
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_FunFieldEquivMemChartRingIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:56.264593+00:00
-- url     : https://prove2.me/theorems/4c63f587-4db6-441d-8d4e-ae7be0f9057d
-- title:
--   Fun Field Equiv Mem Chart Ring Iff
-- statement:
--   Definitions and structural lemmas for Fun Field Equiv Mem Chart Ring Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/FunFieldEquivMemChartRingIff.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
def funFieldEquiv (P : ArithVariety n) : P.FunField ≃+* FunField P :=
  (IsLocalization.algEquiv (nonZeroDivisors (CoordRing P)) P.FunField (FunField P)).toRingEquiv
def GenSystem.ofIsHomogGenerators {P : ArithVariety n} {r : ℕ}
    {G : Fin r → MvPolynomial (Coord n) ℤ} {δ : Fin r → ι → ℕ} (h : P.IsHomogGenerators G δ) :
    GenSystem P where
  r := r
  f := G
  δ := δ
  homog := h.homog
  span_eq := h.span_eq
omit [Fintype ι] in

theorem GenSystem.isHomogGenerators {P : ArithVariety n} (Γ : GenSystem P) :
    P.IsHomogGenerators Γ.f Γ.δ :=
  ⟨Γ.homog, Γ.span_eq⟩
def genSystemEquiv (P : ArithVariety n) :
    GenSystem P ≃ Σ r : ℕ, {p : (Fin r → MvPolynomial (Coord n) ℤ) × (Fin r → ι → ℕ) //
      P.IsHomogGenerators p.1 p.2} where
  toFun Γ := ⟨Γ.r, (Γ.f, Γ.δ), Γ.isHomogGenerators⟩
  invFun p := GenSystem.ofIsHomogGenerators p.2.2
  left_inv _ := rfl
  right_inv _ := rfl
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close


