-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:37.967097+00:00
-- url     : https://prove2.me/theorems/b8e3cd4f-335a-488c-9152-b16b300de02b
-- title:
--   Statements Green Reg
-- statement:
--   Definitions and structural lemmas for Statements Green Reg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsGreenReg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
variable {n : ℕ}
def fsLogReg (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) (y : Fin n → ℂ) : ℝ :=
  Real.log ((‖∑ j, u j * y j‖ ^ 2 + ε * h.dualNorm y ^ 2) / h.dualNorm y ^ 2) / 2
open Classical in

def formInt (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) (e : ℕ)
    (a b : (Fin n → ℂ) → ℝ) : ℝ :=
  if hℓ : ∃ ℓ : Fin n → ℂ, linForm ℓ ∉ W then
    varInt (W ⊔ Ideal.span {linForm hℓ.choose - 1}) (e + 1) a
      (vecCons b fun _ x => Real.log (h.dualNorm x))
  else 0
def FormIntSymm.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) (u u' : Fin n → ℂ) (ε δ : ℝ),
    IsProjPrime W → (∃ g : MvPolynomial (Fin (e + 2) × Fin n) ℂ, IsChowForm W (e + 2) g) →
    0 < ε → 0 < δ →
      formInt h W e (fsLogReg h u δ) (fsLogReg h u' ε) =
        formInt h W e (fsLogReg h u' ε) (fsLogReg h u δ)
def FormIntPos.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) (u u' : Fin n → ℂ)
    (ε δ δ' : ℝ),
    IsProjPrime W → (∃ g : MvPolynomial (Fin (e + 2) × Fin n) ℂ, IsChowForm W (e + 2) g) →
    0 < ε → 0 < δ → δ ≤ δ' →
      formInt h W e (fsLogReg h u δ) (fsLogReg h u' ε) + coneIntegral h W (e + 1) (fsLogReg h u δ) ≤
        formInt h W e (fsLogReg h u δ') (fsLogReg h u' ε) +
          coneIntegral h W (e + 1) (fsLogReg h u δ')
def FormIntLelong.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) (u u' : Fin n → ℂ) (δ : ℝ),
    IsProjPrime W → (∃ g : MvPolynomial (Fin (e + 2) × Fin n) ℂ, IsChowForm W (e + 2) g) →
    linForm u' ∉ W → 0 < δ →
      Tendsto (fun ε => formInt h W e (fsLogReg h u δ) (fsLogReg h u' ε)) (𝓝[>] 0)
        (𝓝 (cycleIntegral h (divCycle W u') e (fsLogReg h u δ) -
          coneIntegral h W (e + 1) (fsLogReg h u δ)))
def RegConeLimit.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    IsProjPrime J → (∃ g : MvPolynomial (Fin (e + 1) × Fin n) ℂ, IsChowForm J (e + 1) g) →
    linForm u ∉ J →
      Tendsto (fun ε => coneIntegral h J e (fsLogReg h u ε)) (𝓝[>] 0)
        (𝓝 (coneIntegral h J e (fsLog h u)))
end
end GroundTheory.Heights₂.Heights


