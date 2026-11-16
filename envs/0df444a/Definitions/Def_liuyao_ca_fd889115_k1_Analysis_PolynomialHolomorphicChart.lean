-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_PolynomialHolomorphicChart
-- name    : liuyao_ca_fd889115_k1_Analysis_PolynomialHolomorphicChart
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:52:56.873193+00:00
-- url     : https://prove2.me/theorems/53d3bb5a-7517-4b5c-b8d7-0496be49d537
-- title:
--   Computable analysis · PolynomialHolomorphicChart · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/PolynomialHolomorphicChart.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_HolomorphicJet
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexInterval

set_option autoImplicit true

/-!
# Polynomial holomorphic charts

Finite rational-complex polynomials are the first complete chart family: both
their value and derivative are evaluated by paired Horner recurrences, and
rational complex boxes enclose both outputs simultaneously.
-/

namespace ComputableAnalysis

namespace CPoly

/-- Horner recurrence for the exact derivative value. -/
def evalDerivative : Coeffs -> QComplex -> QComplex
  | [], _point => QComplex.zero
  | _constant :: tail, point =>
      QComplex.add (eval tail point)
        (QComplex.mul point (evalDerivative tail point))

/-- Paired exact Horner evaluation as a first jet. -/
def evalJet : Coeffs -> QComplex -> HolomorphicJet.FirstJet
  | [], _point => HolomorphicJet.constant QComplex.zero
  | constant :: tail, point =>
      HolomorphicJet.add (HolomorphicJet.constant constant)
        (HolomorphicJet.mul (HolomorphicJet.identity point)
          (evalJet tail point))

theorem evalJet_value (coefficients : Coeffs) (point : QComplex) :
    (evalJet coefficients point).value = eval coefficients point := by
  induction coefficients with
  | nil => rfl
  | cons constant tail ih =>
      simp only [evalJet, HolomorphicJet.add_value,
        HolomorphicJet.mul_value, HolomorphicJet.constant,
        HolomorphicJet.identity, eval, List.foldr_cons, ih]

theorem evalJet_derivative (coefficients : Coeffs) (point : QComplex) :
    (evalJet coefficients point).derivative =
      evalDerivative coefficients point := by
  induction coefficients with
  | nil => rfl
  | cons constant tail ih =>
      simp only [evalJet, HolomorphicJet.add_derivative,
        HolomorphicJet.mul_derivative, HolomorphicJet.constant,
        HolomorphicJet.identity, evalDerivative]
      rw [evalJet_value tail point, ih, QComplex.one_mul_cert,
        QComplex.zero_add_cert]

end CPoly

namespace QBox

/-- A rational complex box for both components of a first jet. -/
structure FirstJetBox where
  value : QBox
  derivative : QBox
deriving Repr, DecidableEq

namespace FirstJetBox

def point (jet : HolomorphicJet.FirstJet) : FirstJetBox where
  value := QBox.point jet.value
  derivative := QBox.point jet.derivative

def Contains (box : FirstJetBox) (jet : HolomorphicJet.FirstJet) : Prop :=
  box.value.lo <= jet.value /\ jet.value <= box.value.hi /\
    box.derivative.lo <= jet.derivative /\
      jet.derivative <= box.derivative.hi

theorem extensionality (left right : FirstJetBox)
    (hvalue : left.value = right.value)
    (hderivative : left.derivative = right.derivative) :
    left = right := by
  cases left
  cases right
  simp_all

end FirstJetBox

/-- Paired interval Horner evaluation.  The derivative recurrence is
`p' = tail + z * tail'`. -/
def evalPolyJet : CPoly.Coeffs -> QBox -> FirstJetBox
  | [], _input => FirstJetBox.point
      (HolomorphicJet.constant QComplex.zero)
  | constant :: tail, input =>
      let tailJet := evalPolyJet tail input
      { value := add (QBox.point constant) (mul input tailJet.value)
        derivative := add tailJet.value (mul input tailJet.derivative) }

theorem evalPolyJet_point (coefficients : CPoly.Coeffs) (z : QComplex) :
    evalPolyJet coefficients (QBox.point z) =
      FirstJetBox.point (CPoly.evalJet coefficients z) := by
  induction coefficients with
  | nil => rfl
  | cons constant tail ih =>
      simp only [evalPolyJet, ih, FirstJetBox.point, CPoly.evalJet,
        HolomorphicJet.add, HolomorphicJet.mul,
        HolomorphicJet.constant, HolomorphicJet.identity]
      apply FirstJetBox.extensionality
      · rw [mul_point, add_point]
      · simp only [QComplex.one_mul_cert, QComplex.zero_add_cert]
        change QBox.add (QBox.point (CPoly.evalJet tail z).value)
            (QBox.mul (QBox.point z)
              (QBox.point (CPoly.evalJet tail z).derivative)) =
          QBox.point (QComplex.add (CPoly.evalJet tail z).value
            (QComplex.mul z (CPoly.evalJet tail z).derivative))
        rw [mul_point, add_point]

/-- Simultaneous soundness of the polynomial value and derivative boxes. -/
theorem evalPolyJet_contains
    {coefficients : CPoly.Coeffs} {input : QBox} {z : QComplex}
    (hzlo : input.lo <= z) (hzhi : z <= input.hi) :
    FirstJetBox.Contains (evalPolyJet coefficients input)
      (CPoly.evalJet coefficients z) := by
  induction coefficients with
  | nil =>
      exact ⟨QComplex.le_refl _, QComplex.le_refl _,
        QComplex.le_refl _, QComplex.le_refl _⟩
  | cons constant tail ih =>
      have hvalueMul := mul_contains hzlo hzhi ih.1 ih.2.1
      have hvalue := add_contains
        (A := QBox.point constant)
        (C := mul input (evalPolyJet tail input).value)
        (QComplex.le_refl constant) (QComplex.le_refl constant)
        hvalueMul.1 hvalueMul.2
      have hderivativeMul := mul_contains hzlo hzhi ih.2.2.1 ih.2.2.2
      have hderivative := add_contains
        ih.1 ih.2.1 hderivativeMul.1 hderivativeMul.2
      have hjet :
          CPoly.evalJet (constant :: tail) z =
            { value := QComplex.add constant
                (QComplex.mul z (CPoly.evalJet tail z).value)
              derivative := QComplex.add (CPoly.evalJet tail z).value
                (QComplex.mul z (CPoly.evalJet tail z).derivative) } := by
        apply HolomorphicJet.FirstJet.extensionality
        · rfl
        · simp only [CPoly.evalJet, HolomorphicJet.add,
            HolomorphicJet.mul, HolomorphicJet.constant,
            HolomorphicJet.identity, QComplex.one_mul_cert,
            QComplex.zero_add_cert]
      rw [hjet]
      exact ⟨hvalue.1, hvalue.2, hderivative.1, hderivative.2⟩

end QBox

/-- A finite rational-complex polynomial together with its paired box and
first-jet evaluators. -/
structure PolynomialHolomorphicChart where
  coefficients : CPoly.Coeffs
deriving Repr, DecidableEq

namespace PolynomialHolomorphicChart

def evalJet (chart : PolynomialHolomorphicChart) (point : QComplex) :
    HolomorphicJet.FirstJet :=
  CPoly.evalJet chart.coefficients point

def evalBox (chart : PolynomialHolomorphicChart) (input : QBox) :
    QBox.FirstJetBox :=
  QBox.evalPolyJet chart.coefficients input

theorem evalBox_contains (chart : PolynomialHolomorphicChart)
    {input : QBox} {point : QComplex}
    (hlo : input.lo <= point) (hhi : point <= input.hi) :
    QBox.FirstJetBox.Contains (evalBox chart input)
      (evalJet chart point) :=
  QBox.evalPolyJet_contains hlo hhi

end PolynomialHolomorphicChart

end ComputableAnalysis


