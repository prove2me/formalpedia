-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StDominantPrimitiveFibres
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StDominantPrimitiveFibres
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:57.281456+00:00
-- url     : https://prove2.me/theorems/9ea4265d-4326-45a1-b1d8-28b20a611a76
-- title:
--   St Dominant Primitive Fibres
-- statement:
--   Definitions and structural lemmas for St Dominant Primitive Fibres, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StDominantPrimitiveFibres.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
def DominantPrimitiveFibres.Statement : Prop :=
  ∀ (n d : ℕ) (Q : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), Q.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) ≤ ((d : ℕ) : WithBot ℕ∞) →
    Function.Injective (ComplexSets.projHom Q A) →
      ∃ (c : Fin n → ℂ) (m : Polynomial (MvPolynomial (Fin d) ℂ)) (Δ : MvPolynomial (Fin d) ℂ)
        (S : Fin n → Polynomial (MvPolynomial (Fin d) ℂ)),
        Δ ≠ 0 ∧ ∀ y : Fin d → ℂ, eval y Δ ≠ 0 →
          (m.map (eval y)).natDegree = m.natDegree ∧ (m.map (eval y)).Separable ∧
          (∀ x ∈ ComplexSets.fibre Q A y, (m.map (eval y)).IsRoot (∑ j, c j * x j) ∧
            ∀ j, eval y Δ * x j = ((S j).map (eval y)).eval (∑ k, c k * x k)) ∧
          ∀ τ : ℂ, (m.map (eval y)).IsRoot τ → ∃ x ∈ ComplexSets.fibre Q A y, ∑ j, c j * x j = τ
end GroundTheory.Heights₂.Heights


