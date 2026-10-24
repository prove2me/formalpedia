-- Prove2me | Definitions.Def_PricingWithTips3DM_e95d94ec9e595ab958ca2dea
-- name    : PricingWithTips3DM_e95d94ec9e595ab958ca2dea
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T00:34:54.340453+00:00
-- url     : https://prove2.me/theorems/0937a926-3c2a-4014-a96c-4af3fe763fde
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorFinalConstraintTransitionSource
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_5ec6efe3c13ebba9e8487e8d
import Definitions.Def_PricingWithTips3DM_12d2e8cf841ea25263d0c142
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Raw-input source for final transition constraint wires

The transition outputs form a second exact polynomial affine progression,
starting at the completed-validity endpoint.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- First final-conjunction transition source wire. -/
def verifierTransitionOutputBasePolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    Polynomial Nat :=
  verifierTransitionStartPolynomial W +
    verifierTransitionOutputOffsetPolynomial W

/-- Forward delimiter-bearing transition source blocks. -/
def verifierTransitionOutputSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  exactPolynomialAffineUnaryProgressionFrameStream
    (verifierTransitionOutputBasePolynomial W)
    (verifierTransitionCostPolynomial W)
    (verifierHorizon W) input

/-- The affine source is exactly the semantic transition-output list. -/
theorem verifierTransitionOutputSource_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionOutputSource W input =
      encodeAffineConjunctionSources
        (List.ofFn (verifierTransitions W input).outputs) := by
  unfold verifierTransitionOutputSource
    exactPolynomialAffineUnaryProgressionFrameStream
    affineUnaryProgressionFrameStream affineUnaryProgressionValues
    exactPolynomialAffineUnaryProgression
  rw [affineUnaryProgressionValuesFrom_eq_ofFn]
  simp only [verifierTransitionOutputBasePolynomial,
    Polynomial.eval_add, verifierTransitionCostPolynomial_eval]
  unfold encodeAffineConjunctionSources encodeUnaryFrame
  congr 1
  apply List.ofFn_inj.mpr
  funext step
  rw [verifierTransitions_output_eq]
  ring

/-- A fixed polynomial-time TM2 emits every transition output source from the
original verifier word. -/
noncomputable def verifierTransitionOutputSource_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionOutputSource W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact
    exactPolynomialAffineUnaryProgressionFrameStream_computableInPolyTime
      (verifierTransitionOutputBasePolynomial W)
      (verifierTransitionCostPolynomial W)
      (verifierHorizon W)

end CLRS.Chapter34.Turing.CookLevin


