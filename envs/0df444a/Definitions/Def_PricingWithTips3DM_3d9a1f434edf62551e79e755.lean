-- Prove2me | Definitions.Def_PricingWithTips3DM_3d9a1f434edf62551e79e755
-- name    : PricingWithTips3DM_3d9a1f434edf62551e79e755
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T00:31:29.74882+00:00
-- url     : https://prove2.me/theorems/0e2d4d91-f3cf-4225-854d-a159a041fcbe
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorFinalConstraintValiditySource
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_2bcd89d3b71b94d506b871ee
import Definitions.Def_PricingWithTips3DM_12d2e8cf841ea25263d0c142
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Raw-input source for final validity constraint wires

The closed validity-output coordinates form one polynomial affine
progression.  Its delimiter-bearing output is exactly the forward validity
sublist collected by the verifier's final conjunction.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- First final-conjunction validity source wire. -/
def verifierValidityOutputBasePolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    Polynomial Nat :=
  verifierTableauInputPolynomial W + 2 +
    verifierValidityOutputOffsetPolynomial W

@[simp] theorem verifierValidityOutputBasePolynomial_eval
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) (n : Nat) :
    (verifierValidityOutputBasePolynomial W).eval n =
      tableauInputCount W.machine.tm
          ((verifierHeight W).eval n) ((verifierHorizon W).eval n) + 2 +
        (validCfgOutputOffsetPolynomial W.machine.tm).eval
          ((verifierHeight W).eval n) := by
  simp [verifierValidityOutputBasePolynomial, Polynomial.eval_add]

/-- Forward delimiter-bearing validity source blocks. -/
def verifierValidityOutputSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  exactPolynomialAffineUnaryProgressionFrameStream
    (verifierValidityOutputBasePolynomial W)
    (verifierValidityRowCostPolynomial W)
    (verifierValidityRowCountPolynomial W) input

/-- The affine source is exactly the semantic validity-output list. -/
theorem verifierValidityOutputSource_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityOutputSource W input =
      encodeAffineConjunctionSources
        (List.ofFn (verifierValidity W input).outputs) := by
  unfold verifierValidityOutputSource
    exactPolynomialAffineUnaryProgressionFrameStream
    affineUnaryProgressionFrameStream affineUnaryProgressionValues
    exactPolynomialAffineUnaryProgression
  rw [affineUnaryProgressionValuesFrom_eq_ofFn]
  simp only [verifierValidityRowCountPolynomial_eval,
    verifierValidityOutputBasePolynomial_eval,
    verifierValidityRowCostPolynomial_eval]
  unfold encodeAffineConjunctionSources encodeUnaryFrame
  congr 1
  apply List.ofFn_inj.mpr
  funext row
  rw [verifierValidity_output_eq]
  simp only [Fin.val_cast]
  ring

/-- A fixed polynomial-time TM2 emits every validity output source directly
from the original verifier word. -/
noncomputable def verifierValidityOutputSource_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityOutputSource W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact
    exactPolynomialAffineUnaryProgressionFrameStream_computableInPolyTime
      (verifierValidityOutputBasePolynomial W)
      (verifierValidityRowCostPolynomial W)
      (verifierValidityRowCountPolynomial W)

end CLRS.Chapter34.Turing.CookLevin


