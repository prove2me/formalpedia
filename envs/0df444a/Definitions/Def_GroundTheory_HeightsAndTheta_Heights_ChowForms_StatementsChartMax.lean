-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:12.700647+00:00
-- url     : https://prove2.me/theorems/b6796632-7507-4c41-95e0-ac41a5f4746a
-- title:
--   Statements Chart Max
-- statement:
--   Definitions and structural lemmas for Statements Chart Max, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsChartMax.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
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
def ChartHomogenise.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (Q : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F),
    Q.IsPrime → linForm t - 1 ∈ Q →
      ∃ W : Ideal (MvPolynomial (Fin n) F), IsProjPrime W ∧ linForm t ∉ W ∧
        W ⊔ Ideal.span {linForm t - 1} = Q ∧
        ∀ J : Ideal (MvPolynomial (Fin n) F), IsHomogIdeal J → J ≤ Q → J ≤ W
def ChartDehomog.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (W : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F)
    (G : MvPolynomial (Fin n) F) (d : ℕ),
    W.IsPrime → IsHomogIdeal W → linForm t ∉ W → G.IsHomogeneous d →
      G ∈ W ⊔ Ideal.span {linForm t - 1} → G ∈ W
def ComponentOfIncIdeal.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I W : Ideal (MvPolynomial (Fin n) F)) (u : Fin n → F)
    (q : MvPolynomial (Fin e × Fin n) F),
    IsProjPrime I → ringKrullDim (MvPolynomial (Fin n) F ⧸ I) = ((e + 1 : ℕ) : WithBot ℕ∞) →
      linForm u ∉ I → IsProjPrime W → I ⊔ Ideal.span {linForm u} ≤ W → Prime q →
        incIdeal W e ≤ Ideal.span {q} →
          W ∈ relComps (I ⊔ Ideal.span {linForm u}) ∧ incIdeal W e = Ideal.span {q}
section Inhabitants
def pointIdealZeroOne : Ideal (MvPolynomial (Fin 2) ℚ) :=
  RingHom.ker (MvPolynomial.eval ![(0 : ℚ), 1])
def substZeroOne : MvPolynomial (Fin 1 × Fin 2) ℚ →ₐ[ℚ] MvPolynomial (Fin 1 × Fin 2) ℚ :=
  aeval fun ij => if ij = ((0 : Fin 1), (1 : Fin 2)) then 0 else X ij
end Inhabitants
end
end GroundTheory.Heights₂.Heights


