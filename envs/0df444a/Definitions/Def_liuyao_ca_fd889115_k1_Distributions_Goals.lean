-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Distributions_Goals
-- name    : liuyao_ca_fd889115_k1_Distributions_Goals
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:57:40.972009+00:00
-- url     : https://prove2.me/theorems/6f43ae1e-6647-4d63-88d5-265eb5650650
-- title:
--   Computable analysis · Goals · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableDistributions/Goals.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RationalBoxes
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ParametrizedLimits
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_BracketDerivative
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealMultiplication
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealComputeQuotient
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealApproximationOrder
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealValueBounds

set_option autoImplicit true

/-!
# Computable distributions: formal target statements

This is a downstream package. It may depend on the computable-analysis
foundation; the foundation does not depend on it. This file defines distributions as continuous linear test actions, constructs
Dirac, and states the Laplace, heat, and wave goals. The PDE statements test the real kernels against complex-valued
test functions, represented by separate real and imaginary channels.
The concrete test-space operations and PDE kernels are separate goals.
-/

open ComputableAnalysis
namespace ComputableDistributions

/-- A multi-index for iterated coordinate partial derivatives. -/
abbrev MultiIndex (dimension : Nat) := Fin dimension → Nat

export ComputableAnalysis (QPoint RationalBox origin sumRat productRat)

def zeroIndex (dimension : Nat) : MultiIndex dimension := fun _ => 0

/-- Increase one coordinate of a multi-index by one. -/
def incrementIndex {dimension : Nat}
    (alpha : MultiIndex dimension) (i : Fin dimension) :
    MultiIndex dimension :=
  fun j => alpha j + if j = i then 1 else 0

theorem incrementIndex_commute {dimension : Nat}
    (alpha : MultiIndex dimension) (i j : Fin dimension) :
    incrementIndex (incrementIndex alpha i) j =
      incrementIndex (incrementIndex alpha j) i := by
  funext k
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp [incrementIndex, hki, hkj, Nat.add_comm, Nat.add_left_comm]

def replaceCoordinate {dimension : Nat} (x : QPoint dimension)
    (i : Fin dimension) (r : Rat) : QPoint dimension :=
  fun j => if j = i then r else x j

/-- A represented compactly supported smooth test function on rational
coordinates. Every mixed partial has a valid raw evaluator; each next
coordinate partial is certified by the foundation's secant-limit derivative
predicate; all partials vanish outside one rational box.

Each derivative also carries a rational Lipschitz bound for joint variation
in the coordinates. Classical smooth compactly supported tests admit such
bounds by bounding the next derivatives.

The represented real extension and effective compact Riemann pairing are
separate constructions and are not assumed by this definition. -/
structure TestFunction (dimension : Nat) where
  derivative : MultiIndex dimension → QPoint dimension → RealCompute
  derivative_valid : ∀ alpha x, (derivative alpha x).Valid
  support : RationalBox dimension
  derivative_vanishes_off_support :
    ∀ alpha x, ¬ support.Contains x →
      (derivative alpha x).Equiv (RealCompute.ofRat 0)
  derivativeLipschitz : MultiIndex dimension → Rat
  derivativeLipschitz_nonneg : ∀ alpha, 0 ≤ derivativeLipschitz alpha
  derivative_control : ∀ alpha x y (δ : Rat), 0 ≤ δ →
    (∀ i, x i ≤ y i + δ ∧ y i ≤ x i + δ) →
    RealApproximationOrder.Small
      (RealApproximationOrder.sub
        (RealApproximationOrder.parameter (derivative alpha x) (derivative_valid alpha x))
        (RealApproximationOrder.parameter (derivative alpha y) (derivative_valid alpha y)))
      (derivativeLipschitz alpha * δ)
  partialDerivative : ∀ alpha i x,
    BracketDerivative.HasDerivativeAt (fun _ => True)
      (fun r => derivative alpha (replaceCoordinate x i r))
      (RealCompute.ofRat (x i)) (derivative (incrementIndex alpha i) x)

namespace TestFunction

/-- Value of a test function at a rational point, represented by its
zeroth-order derivative. -/
def value {dimension : Nat} (phi : TestFunction dimension)
    (x : QPoint dimension) : RealCompute :=
  phi.derivative (zeroIndex dimension) x

theorem value_valid {dimension : Nat} (phi : TestFunction dimension)
    (x : QPoint dimension) : (phi.value x).Valid :=
  phi.derivative_valid (zeroIndex dimension) x

/-- The point-source probe at the origin. -/
def atOrigin {dimension : Nat} (phi : TestFunction dimension) : RealCompute :=
  phi.value (origin dimension)

theorem atOrigin_valid {dimension : Nat} (phi : TestFunction dimension) :
    (phi.atOrigin).Valid :=
  phi.value_valid (origin dimension)

/-- Coordinate partial differentiation preserves the rational support box and
all higher derivative certificates. -/
def coordinatePartial {dimension : Nat} (i : Fin dimension)
    (phi : TestFunction dimension) : TestFunction dimension where
  derivative alpha x := phi.derivative (incrementIndex alpha i) x
  derivative_valid alpha x := phi.derivative_valid
    (incrementIndex alpha i) x
  support := phi.support
  derivative_vanishes_off_support alpha x hx :=
    phi.derivative_vanishes_off_support (incrementIndex alpha i) x hx
  derivativeLipschitz alpha := phi.derivativeLipschitz (incrementIndex alpha i)
  derivativeLipschitz_nonneg alpha := phi.derivativeLipschitz_nonneg (incrementIndex alpha i)
  derivative_control alpha := phi.derivative_control (incrementIndex alpha i)
  partialDerivative alpha j x := by
    simpa [incrementIndex_commute] using
      phi.partialDerivative (incrementIndex alpha i) j x

@[simp] theorem partial_derivative {dimension : Nat}
    (i : Fin dimension) (phi : TestFunction dimension)
    (alpha : MultiIndex dimension) (x : QPoint dimension) :
    (phi.coordinatePartial i).derivative alpha x =
      phi.derivative (incrementIndex alpha i) x := rfl

end TestFunction

/-! The fundamental-solution kernels in this first mission are real-valued,
but test functions are complex-valued from the start. We represent a complex
test by its real and imaginary channels; this avoids importing Mathlib's
complex field and makes the complex test-action identity two exact `RealCompute`
identities. -/

/-- A complex test value represented by its two valid real components. -/
structure ComplexActionValue where
  re : RealCompute
  im : RealCompute
  re_valid : re.Valid
  im_valid : im.Valid

namespace ComplexActionValue

def Equiv (z w : ComplexActionValue) : Prop :=
  z.re.Equiv w.re ∧ z.im.Equiv w.im

theorem equiv_refl (z : ComplexActionValue) : Equiv z z :=
  ⟨RealCompute.equiv_refl z.re z.re_valid,
   RealCompute.equiv_refl z.im z.im_valid⟩

theorem equiv_symm {z w : ComplexActionValue} (h : Equiv z w) : Equiv w z :=
  ⟨RealCompute.equiv_symm h.1, RealCompute.equiv_symm h.2⟩

theorem equiv_trans {z w v : ComplexActionValue}
    (hzw : Equiv z w) (hwv : Equiv w v) : Equiv z v :=
  ⟨RealCompute.equiv_trans z.re_valid w.re_valid v.re_valid hzw.1 hwv.1,
   RealCompute.equiv_trans z.im_valid w.im_valid v.im_valid hzw.2 hwv.2⟩

def zero : ComplexActionValue where
  re := RealCompute.ofRat 0
  im := RealCompute.ofRat 0
  re_valid := RealCompute.ofRat_valid 0
  im_valid := RealCompute.ofRat_valid 0

end ComplexActionValue

/-- A complex-valued compactly supported test, represented as a pair of real
test computations on the same rational coordinate domain. -/
structure ComplexTestFunction (dimension : Nat) where
  re : TestFunction dimension
  im : TestFunction dimension

namespace ComplexTestFunction

def atOrigin {dimension : Nat} (phi : ComplexTestFunction dimension) :
    ComplexActionValue where
  re := phi.re.atOrigin
  im := phi.im.atOrigin
  re_valid := phi.re.atOrigin_valid
  im_valid := phi.im.atOrigin_valid

def coordinatePartial {dimension : Nat} (i : Fin dimension)
    (phi : ComplexTestFunction dimension) : ComplexTestFunction dimension where
  re := phi.re.coordinatePartial i
  im := phi.im.coordinatePartial i

end ComplexTestFunction

/-- Equality of test computations means agreement of every represented mixed
partial on every rational input. -/
def TestFunction.Equivalent {dimension : Nat}
    (φ ψ : TestFunction dimension) : Prop :=
  ∀ alpha x, (φ.derivative alpha x).Equiv (ψ.derivative alpha x)

theorem TestFunction.equivalent_refl {dimension : Nat}
    (φ : TestFunction dimension) : TestFunction.Equivalent φ φ := by
  intro alpha x
  exact RealCompute.equiv_refl _ (φ.derivative_valid alpha x)

theorem TestFunction.equivalent_symm {dimension : Nat}
    {φ ψ : TestFunction dimension} (h : TestFunction.Equivalent φ ψ) :
    TestFunction.Equivalent ψ φ := by
  intro alpha x
  exact RealCompute.equiv_symm (h alpha x)

theorem TestFunction.equivalent_trans {dimension : Nat}
    {φ ψ χ : TestFunction dimension}
    (hφψ : TestFunction.Equivalent φ ψ)
    (hψχ : TestFunction.Equivalent ψ χ) :
    TestFunction.Equivalent φ χ := by
  intro alpha x
  exact RealCompute.equiv_trans (φ.derivative_valid alpha x)
    (ψ.derivative_valid alpha x) (χ.derivative_valid alpha x)
    (hφψ alpha x) (hψχ alpha x)

/-- Algebraic operations on compactly supported test data. Each closure
operation returns a full `TestFunction`, so its support and all iterated
derivative certificates remain available. The laws identify every
derivative with the corresponding pointwise linear combination. The fields
below state the module laws up to `TestFunction.Equivalent`; constructors for
the concrete test space must prove them. -/
structure TestFunctionSpace (dimension : Nat) where
  zero : TestFunction dimension
  add : TestFunction dimension → TestFunction dimension →
    TestFunction dimension
  scale : (r : RealCompute) → r.Valid → TestFunction dimension →
    TestFunction dimension
  zero_derivative : ∀ (alpha : MultiIndex dimension)
      (x : QPoint dimension),
    (zero.derivative alpha x).Equiv (RealCompute.ofRat 0)
  add_derivative : ∀ (φ ψ : TestFunction dimension)
      (alpha : MultiIndex dimension) (x : QPoint dimension),
    ((add φ ψ).derivative alpha x).Equiv
      (RealCompute.add (φ.derivative alpha x) (ψ.derivative alpha x))
  scale_derivative : ∀ (r : RealCompute) (hr : r.Valid)
      (φ : TestFunction dimension) (alpha : MultiIndex dimension)
      (x : QPoint dimension),
    ((scale r hr φ).derivative alpha x).Equiv
      (RealCompute.mul r (φ.derivative alpha x))
  add_zero : ∀ φ, TestFunction.Equivalent (add φ zero) φ
  zero_add : ∀ φ, TestFunction.Equivalent (add zero φ) φ
  add_comm : ∀ φ ψ, TestFunction.Equivalent (add φ ψ) (add ψ φ)
  add_assoc : ∀ φ ψ χ,
    TestFunction.Equivalent (add (add φ ψ) χ) (add φ (add ψ χ))
  scale_one : ∀ φ,
    TestFunction.Equivalent
      (scale (RealCompute.ofRat 1) (RealCompute.ofRat_valid 1) φ) φ
  scale_zero : ∀ φ,
    TestFunction.Equivalent
      (scale (RealCompute.ofRat 0) (RealCompute.ofRat_valid 0) φ) zero
  scale_add_scalar : ∀ r (hr : r.Valid) s (hs : s.Valid) φ,
    TestFunction.Equivalent
      (scale (RealCompute.add r s) (RealCompute.add_valid hr hs) φ)
      (add (scale r hr φ) (scale s hs φ))
  scale_mul_scalar : ∀ r (hr : r.Valid) s (hs : s.Valid) φ,
    TestFunction.Equivalent
      (scale r hr (scale s hs φ))
      (scale (RealCompute.mul r s) (RealCompute.mul_valid hr hs) φ)
  scale_add_test : ∀ r (hr : r.Valid) φ ψ,
    TestFunction.Equivalent
      (scale r hr (add φ ψ))
      (add (scale r hr φ) (scale r hr ψ))
  add_congr : ∀ φ φ' ψ ψ',
    TestFunction.Equivalent φ φ' → TestFunction.Equivalent ψ ψ' →
      TestFunction.Equivalent (add φ ψ) (add φ' ψ')
  scale_test_congr : ∀ r (hr : r.Valid) φ ψ,
    TestFunction.Equivalent φ ψ →
      TestFunction.Equivalent (scale r hr φ) (scale r hr ψ)
  scale_scalar_congr : ∀ r s (hr : r.Valid) (hs : s.Valid) φ,
    r.Equiv s →
      TestFunction.Equivalent (scale r hr φ) (scale s hs φ)

/-- A test action is a real-linear functional on the supplied test-function
space. Scalars are all valid represented reals, not just rational constants. -/
structure IsLinearAction {dimension : Nat}
    (S : TestFunctionSpace dimension)
    (A : TestFunction dimension → RealCompute) : Prop where
  value_valid : ∀ φ, (A φ).Valid
  respects_test_equiv : ∀ φ ψ, TestFunction.Equivalent φ ψ →
    (A φ).Equiv (A ψ)
  map_zero : (A S.zero).Equiv (RealCompute.ofRat 0)
  map_add : ∀ φ ψ,
    (A (S.add φ ψ)).Equiv (RealCompute.add (A φ) (A ψ))
  map_scale : ∀ r (hr : r.Valid) φ,
    (A (S.scale r hr φ)).Equiv (RealCompute.mul r (A φ))

/-- Finite sum of represented real values, recursively indexed by `Fin n`.
This is the finite-dimensional trace used in the Laplace operators. -/
def sumRaw : (dimension : Nat) → (Fin dimension → RealCompute) → RealCompute
  | 0, _ => RealCompute.ofRat 0
  | dimension + 1, f =>
      RealCompute.add (sumRaw dimension (fun i => f i.castSucc))
        (f (Fin.last dimension))

theorem sumRaw_valid :
    ∀ (dimension : Nat) (f : Fin dimension → RealCompute),
      (∀ i, (f i).Valid) → (sumRaw dimension f).Valid
  | 0, _, _ => RealCompute.ofRat_valid 0
  | dimension + 1, f, hf =>
      RealCompute.add_valid
        (sumRaw_valid dimension (fun i => f i.castSucc)
          (fun i => hf i.castSucc))
        (hf (Fin.last dimension))

theorem sumRaw_equiv :
    ∀ (n : Nat) (f g : Fin n → RealCompute),
      (∀ i, (f i).Valid) → (∀ i, (g i).Valid) →
      (∀ i, (f i).Equiv (g i)) → (sumRaw n f).Equiv (sumRaw n g)
  | 0, _, _, _, _, _ => RealCompute.equiv_refl _ (RealCompute.ofRat_valid 0)
  | n + 1, f, g, hf, hg, h => by
      apply RealCompute.add_equiv
      · exact sumRaw_valid n _ (fun i => hf i.castSucc)
      · exact sumRaw_valid n _ (fun i => hg i.castSucc)
      · exact hf (Fin.last n)
      · exact hg (Fin.last n)
      · exact sumRaw_equiv n _ _ (fun i => hf i.castSucc)
          (fun i => hg i.castSucc) (fun i => h i.castSucc)
      · exact h (Fin.last n)

/-- The total order of a mixed partial derivative. -/
def multiIndexOrder : {dimension : Nat} → MultiIndex dimension → Nat
  | 0, _ => 0
  | dimension + 1, alpha =>
    multiIndexOrder (fun i : Fin dimension => alpha i.castSucc) + alpha (Fin.last dimension)

@[simp] theorem multiIndexOrder_zeroIndex (dimension : Nat) :
    multiIndexOrder (zeroIndex dimension) = 0 := by
  induction dimension with
  | zero => rfl
  | succ dimension ih =>
    change multiIndexOrder (zeroIndex dimension) + 0 = 0
    simp [ih]

/-- The represented value vanishes at every rational point outside the box. -/
def TestFunction.SupportedInBox {dimension : Nat}
    (φ : TestFunction dimension) (B : RationalBox dimension) : Prop :=
  ∀ x, ¬ B.Contains x → (φ.value x).Equiv (RealCompute.ofRat 0)

/-- Every partial through order `order` is bounded in absolute value
by the supplied rational bound at every rational point. -/
def TestFunction.DerivativesBoundedBy {dimension : Nat}
    (φ : TestFunction dimension) (order : Nat) (bound : Rat) : Prop :=
  ∀ alpha, multiIndexOrder alpha ≤ order → ∀ x,
    RealApproximationOrder.Small
      (RealApproximationOrder.parameter (φ.derivative alpha x) (φ.derivative_valid alpha x)) bound

/-- On each fixed support box, a continuous test action has an estimate
by a constant times the common bound on finitely many derivative orders.
The box determines the order and the constant. -/
def IsContinuousTestAction {dimension : Nat}
    (A : TestFunction dimension → RealCompute) (valid : ∀ φ, (A φ).Valid) : Prop :=
  ∀ B : RationalBox dimension, ∃ order : Nat, ∃ C : Rat, 0 ≤ C ∧
    ∀ φ, φ.SupportedInBox B → ∀ bound : Rat, 0 ≤ bound →
      φ.DerivativesBoundedBy order bound →
      RealApproximationOrder.Small (RealApproximationOrder.parameter (A φ) (valid φ))
        (C * bound)

/-- A distribution is a continuous linear functional on compactly supported
smooth tests, with values in the represented reals. -/
structure Distribution {dimension : Nat} (tests : TestFunctionSpace dimension) where
  action : TestFunction dimension → RealCompute
  action_linear : IsLinearAction tests action
  action_continuous : IsContinuousTestAction action action_linear.value_valid

namespace Distribution

theorem action_valid {dimension : Nat} {tests : TestFunctionSpace dimension}
    (D : Distribution tests) (φ : TestFunction dimension) : (D.action φ).Valid :=
  D.action_linear.value_valid φ

/-- A sufficiently small common bound on finitely many derivatives makes
the action small, for tests supported in a fixed box. -/
theorem small_action_on_box {dimension : Nat} {tests : TestFunctionSpace dimension}
    (D : Distribution tests) (B : RationalBox dimension) (ε : Rat) (hε : 0 < ε) :
    ∃ order : Nat, ∃ δ : Rat, 0 < δ ∧
      ∀ φ, φ.SupportedInBox B → φ.DerivativesBoundedBy order δ →
        RealApproximationOrder.Small
          (RealApproximationOrder.parameter (D.action φ) (D.action_valid φ)) ε := by
  obtain ⟨order, C, hC, h⟩ := D.action_continuous B
  have hdenom : 0 < 1 + C := by grind only
  let δ := ε / (1 + C)
  have hδ : 0 < δ := Rat.mul_pos hε (Rat.inv_pos.mpr hdenom)
  refine ⟨order, δ, hδ, fun φ hbox hderivative => ?_⟩
  have hmul : δ * (1 + C) = ε := Rat.div_mul_cancel (Rat.ne_of_gt hdenom)
  have hle : δ * C ≤ δ * (1 + C) :=
    Rat.mul_le_mul_of_nonneg_left (by grind only) (Rat.le_of_lt hδ)
  have hbudget : C * δ ≤ ε := by rw [Rat.mul_comm C δ, ← hmul]; exact hle
  exact (h φ hbox δ (Rat.le_of_lt hδ) hderivative).mono hbudget

/-- Two functional implementations agree when their values agree on every test. -/
def Equivalent {dimension : Nat} {tests : TestFunctionSpace dimension}
    (D E : Distribution tests) : Prop :=
  ∀ φ, (D.action φ).Equiv (E.action φ)

theorem equivalent_refl {dimension : Nat} {tests : TestFunctionSpace dimension}
    (D : Distribution tests) : Equivalent D D :=
  fun φ => RealCompute.equiv_refl _ (D.action_valid φ)

theorem equivalent_symm {dimension : Nat} {tests : TestFunctionSpace dimension}
    {D E : Distribution tests} (h : Equivalent D E) : Equivalent E D :=
  fun φ => RealCompute.equiv_symm (h φ)

theorem equivalent_trans {dimension : Nat} {tests : TestFunctionSpace dimension}
    {D E F : Distribution tests} (hDE : Equivalent D E)
    (hEF : Equivalent E F) : Equivalent D F :=
  fun φ => RealCompute.equiv_trans (D.action_valid φ) (E.action_valid φ)
    (F.action_valid φ) (hDE φ) (hEF φ)

def actionSetoid {dimension : Nat} (tests : TestFunctionSpace dimension) :
    Setoid (Distribution tests) where
  r := Equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩

/-- Distribution values with equivalent functional implementations identified. -/
abbrev Class {dimension : Nat} (tests : TestFunctionSpace dimension) :=
  Quotient (actionSetoid tests)

def evaluate {dimension : Nat} {tests : TestFunctionSpace dimension}
    (D : Class tests) (φ : TestFunction dimension) : RealComputeQuotient.Value :=
  Quotient.liftOn D
    (fun P => RealComputeQuotient.ofRaw (P.action φ) (P.action_valid φ))
    (fun _ _ h => RealComputeQuotient.ofRaw_eq_iff.mpr (h φ))

theorem ext_iff {dimension : Nat} {tests : TestFunctionSpace dimension}
    (D E : Class tests) :
    D = E ↔ ∀ φ, evaluate D φ = evaluate E φ := by
  constructor
  · rintro rfl φ
    rfl
  · refine Quotient.inductionOn₂ D E ?_
    intro P Q h
    exact Quotient.sound (fun φ => RealComputeQuotient.ofRaw_eq_iff.mp (h φ))

end Distribution

/-- The point source at the origin acts by evaluation. -/
def diracAction {dimension : Nat} :
    TestFunction dimension → RealCompute := TestFunction.atOrigin

/-- Dirac is continuous of order zero, with constant one on every box. -/
def dirac {dimension : Nat} (tests : TestFunctionSpace dimension) : Distribution tests where
  action := diracAction
  action_linear :=
    { value_valid := TestFunction.atOrigin_valid
      respects_test_equiv := fun _ _ h => h (zeroIndex dimension) (origin dimension)
      map_zero := tests.zero_derivative (zeroIndex dimension) (origin dimension)
      map_add := fun φ ψ => tests.add_derivative φ ψ (zeroIndex dimension) (origin dimension)
      map_scale := fun r hr φ =>
        tests.scale_derivative r hr φ (zeroIndex dimension) (origin dimension) }
  action_continuous := by
    intro _
    refine ⟨0, 1, by decide, ?_⟩
    intro φ _ bound _ hbound
    rw [Rat.one_mul]
    exact hbound (zeroIndex dimension) (by simp) (origin dimension)

@[simp] theorem dirac_apply {dimension : Nat} (tests : TestFunctionSpace dimension)
    (φ : TestFunction dimension) : (dirac tests).action φ = φ.atOrigin := rfl

/-- The point-source action characterizes Dirac among distributions. -/
def IsDiracAction {dimension : Nat} (tests : TestFunctionSpace dimension)
    (D : Distribution tests) : Prop :=
  D.Equivalent (dirac tests)

/-- The test-action of the spatial Laplacian, using its formal transpose
`Delta = sum_i partial_i^2`. -/
def spatialLaplacianAction {dimension : Nat} {tests : TestFunctionSpace dimension}
    (D : Distribution tests)
    (φ : TestFunction dimension) : RealCompute :=
  sumRaw dimension fun i =>
    D.action ((φ.coordinatePartial i).coordinatePartial i)

theorem spatialLaplacianAction_valid {dimension : Nat} {tests : TestFunctionSpace dimension}
    (D : Distribution tests)
    (φ : TestFunction dimension) : (spatialLaplacianAction D φ).Valid :=
  sumRaw_valid dimension
    (fun i => D.action ((φ.coordinatePartial i).coordinatePartial i))
    (fun i => D.action_valid ((φ.coordinatePartial i).coordinatePartial i))

/-- Complex test-action of the real spatial Laplacian kernel. The real kernel
acts separately on the real and imaginary test channels. -/
def spatialLaplacianComplexAction {dimension : Nat} {tests : TestFunctionSpace dimension}
    (D : Distribution tests)
    (φ : ComplexTestFunction dimension) : ComplexActionValue where
  re := spatialLaplacianAction D φ.re
  im := spatialLaplacianAction D φ.im
  re_valid := spatialLaplacianAction_valid D φ.re
  im_valid := spatialLaplacianAction_valid D φ.im

/-- The Laplace source identity for every complex-valued test function. -/
def IsLaplaceFundamentalSolutionComplex {dimension : Nat}
    {tests : TestFunctionSpace dimension}
    (E : Distribution tests) : Prop :=
  ∀ (φ : ComplexTestFunction dimension),
    (spatialLaplacianComplexAction E φ).Equiv φ.atOrigin

/-- Goal shape for the fundamental solution of the spatial Laplacian on
`R^n`, with $\Delta=\sum_i\partial_i^2$. -/
def IsLaplaceFundamentalSolutionReal {dimension : Nat}
    (tests : TestFunctionSpace dimension)
    (E : Distribution tests) : Prop :=
  ∀ (φ : TestFunction dimension),
    (spatialLaplacianAction E φ).Equiv φ.atOrigin

/-- Public Laplace target: the real kernel acts on complex-valued tests by
complex linear extension, encoded as separate real and imaginary actions. -/
def IsLaplaceFundamentalSolution {dimension : Nat}
    {tests : TestFunctionSpace dimension}
    (E : Distribution tests) : Prop :=
  IsLaplaceFundamentalSolutionComplex E

/-- Coordinate zero is time; the remaining coordinates are space. -/
def timeCoordinate (spatialDimension : Nat) : Fin (spatialDimension + 1) :=
  ⟨0, Nat.zero_lt_succ spatialDimension⟩

def spatialCoordinate {spatialDimension : Nat}
    (i : Fin spatialDimension) : Fin (spatialDimension + 1) := i.succ

/-- The squared spatial radius of a rational spacetime point. -/
def spatialRadiusSquared {spatialDimension : Nat}
    (p : QPoint (spatialDimension + 1)) : Rat :=
  sumRat spatialDimension fun i => p (spatialCoordinate i) ^ 2

/-- The closed forward cone for propagation speed one, including its vertex. -/
def InForwardLightCone {spatialDimension : Nat}
    (p : QPoint (spatialDimension + 1)) : Prop :=
  0 ≤ p (timeCoordinate spatialDimension) ∧
    spatialRadiusSquared p ≤ p (timeCoordinate spatialDimension) ^ 2

/-- The null boundary of the forward light cone, including its vertex. -/
def OnForwardLightCone {spatialDimension : Nat}
    (p : QPoint (spatialDimension + 1)) : Prop :=
  0 ≤ p (timeCoordinate spatialDimension) ∧
    spatialRadiusSquared p = p (timeCoordinate spatialDimension) ^ 2

theorem onForwardLightCone_inForwardLightCone {spatialDimension : Nat}
    {p : QPoint (spatialDimension + 1)} (h : OnForwardLightCone p) :
    InForwardLightCone p :=
  ⟨h.1, by rw [h.2]; exact Rat.le_refl⟩

/-- The test is zero on a positive rational neighborhood of the region.
Requiring a neighborhood also covers actions that detect normal derivatives
on a hypersurface. -/
def TestFunction.VanishesNear {dimension : Nat} (φ : TestFunction dimension)
    (region : QPoint dimension → Prop) : Prop :=
  ∃ ε : Rat, 0 < ε ∧ ∀ p, region p → ∀ q,
    (∀ i, q i ≤ p i + ε ∧ p i ≤ q i + ε) →
    (φ.value q).Equiv (RealCompute.ofRat 0)

theorem TestFunction.vanishesNear_congr {dimension : Nat}
    {φ ψ : TestFunction dimension} (h : TestFunction.Equivalent φ ψ)
    {region : QPoint dimension → Prop} (hφ : φ.VanishesNear region) :
    ψ.VanishesNear region := by
  obtain ⟨ε, hε, hzero⟩ := hφ
  refine ⟨ε, hε, fun p hp q hclose => ?_⟩
  exact RealCompute.equiv_trans (ψ.value_valid q) (φ.value_valid q) (RealCompute.ofRat_valid 0)
    (RealCompute.equiv_symm (h (zeroIndex dimension) q)) (hzero p hp q hclose)

/-- Distributional support, tested by vanishing on a neighborhood of the
region. The statement uses the test's values, so the support box stored in a
test is not required to avoid the region. -/
def IsSupportedIn {dimension : Nat} {tests : TestFunctionSpace dimension}
    (D : Distribution tests) (region : QPoint dimension → Prop) : Prop :=
  ∀ φ, φ.VanishesNear region → (D.action φ).Equiv (RealCompute.ofRat 0)

theorem dirac_isSupportedIn_origin {dimension : Nat} (tests : TestFunctionSpace dimension) :
    IsSupportedIn (dirac tests) (fun x => x = origin dimension) := by
  intro φ hφ
  obtain ⟨ε, hε, hzero⟩ := hφ
  exact hzero (origin dimension) rfl (origin dimension) (fun _ => by
    constructor <;> grind only)

theorem isSupportedIn_mono {dimension : Nat} {tests : TestFunctionSpace dimension}
    {D : Distribution tests} {region larger : QPoint dimension → Prop}
    (h : IsSupportedIn D region) (hsubset : ∀ p, region p → larger p) :
    IsSupportedIn D larger := by
  intro φ hφ
  obtain ⟨ε, hε, hzero⟩ := hφ
  exact h φ ⟨ε, hε, fun p hp => hzero p (hsubset p hp)⟩

theorem isSupportedIn_congr {dimension : Nat} {tests : TestFunctionSpace dimension}
    {D E : Distribution tests} (h : Distribution.Equivalent D E)
    {region : QPoint dimension → Prop} (hD : IsSupportedIn D region) :
    IsSupportedIn E region := by
  intro φ hφ
  exact RealCompute.equiv_trans (E.action_linear.value_valid φ) (D.action_linear.value_valid φ)
    (RealCompute.ofRat_valid 0) (RealCompute.equiv_symm (h φ)) (hD φ hφ)

/-- Formal transpose action of the heat operator
`partial_t - Delta_x`, namely `-partial_t - Delta_x` on tests. -/
def heatAdjointAction {spatialDimension : Nat}
    {tests : TestFunctionSpace (spatialDimension + 1)}
    (H : Distribution tests)
    (φ : TestFunction (spatialDimension + 1)) : RealCompute :=
  RealCompute.sub
    (RealCompute.neg (H.action
      (φ.coordinatePartial (timeCoordinate spatialDimension))))
    (sumRaw spatialDimension fun i =>
      H.action ((φ.coordinatePartial (spatialCoordinate i)).coordinatePartial
        (spatialCoordinate i)))

theorem heatAdjointAction_valid {spatialDimension : Nat}
    {tests : TestFunctionSpace (spatialDimension + 1)}
    (H : Distribution tests)
    (φ : TestFunction (spatialDimension + 1)) :
    (heatAdjointAction H φ).Valid := by
  apply RealCompute.sub_valid
  · exact RealCompute.neg_valid
      (H.action_valid (φ.coordinatePartial (timeCoordinate spatialDimension)))
  · apply sumRaw_valid
    intro i
    exact H.action_valid
      ((φ.coordinatePartial (spatialCoordinate i)).coordinatePartial
        (spatialCoordinate i))

/-- Complex test-action of a real heat-kernel presentation. -/
def heatAdjointComplexAction {spatialDimension : Nat}
    {tests : TestFunctionSpace (spatialDimension + 1)}
    (H : Distribution tests)
    (φ : ComplexTestFunction (spatialDimension + 1)) : ComplexActionValue where
  re := heatAdjointAction H φ.re
  im := heatAdjointAction H φ.im
  re_valid := heatAdjointAction_valid H φ.re
  im_valid := heatAdjointAction_valid H φ.im

/-- Formal transpose action of the wave operator
`partial_t^2 - Delta_x`, which has the same expression on tests. -/
def waveAdjointAction {spatialDimension : Nat}
    {tests : TestFunctionSpace (spatialDimension + 1)}
    (W : Distribution tests)
    (φ : TestFunction (spatialDimension + 1)) : RealCompute :=
  RealCompute.sub
    (W.action ((φ.coordinatePartial (timeCoordinate spatialDimension)).coordinatePartial
      (timeCoordinate spatialDimension)))
    (sumRaw spatialDimension fun i =>
      W.action ((φ.coordinatePartial (spatialCoordinate i)).coordinatePartial
        (spatialCoordinate i)))

theorem waveAdjointAction_valid {spatialDimension : Nat}
    {tests : TestFunctionSpace (spatialDimension + 1)}
    (W : Distribution tests)
    (φ : TestFunction (spatialDimension + 1)) :
    (waveAdjointAction W φ).Valid := by
  apply RealCompute.sub_valid
  · exact W.action_valid
      ((φ.coordinatePartial (timeCoordinate spatialDimension)).coordinatePartial
        (timeCoordinate spatialDimension))
  · apply sumRaw_valid
    intro i
    exact W.action_valid
      ((φ.coordinatePartial (spatialCoordinate i)).coordinatePartial
        (spatialCoordinate i))

/-- Complex test-action of a real wave-kernel presentation. -/
def waveAdjointComplexAction {spatialDimension : Nat}
    {tests : TestFunctionSpace (spatialDimension + 1)}
    (W : Distribution tests)
    (φ : ComplexTestFunction (spatialDimension + 1)) : ComplexActionValue where
  re := waveAdjointAction W φ.re
  im := waveAdjointAction W φ.im
  re_valid := waveAdjointAction_valid W φ.re
  im_valid := waveAdjointAction_valid W φ.im

/-- Goal shape for the retarded fundamental solution of
`partial_t - Delta_x` on space-time. Its formal transpose is evaluated as
`-partial_t - Delta_x` on each test. -/
def IsHeatFundamentalSolutionReal {spatialDimension : Nat}
    (tests : TestFunctionSpace (spatialDimension + 1))
    (H : Distribution tests) : Prop :=
  ∀ (φ : TestFunction (spatialDimension + 1)),
    (heatAdjointAction H φ).Equiv φ.atOrigin

/-- Goal shape for the retarded fundamental solution of
`partial_t^2 - Delta_x` on space-time. Its formal transpose has the same
expression on tests. -/
def IsWaveFundamentalSolutionReal {spatialDimension : Nat}
    (tests : TestFunctionSpace (spatialDimension + 1))
    (W : Distribution tests) : Prop :=
  ∀ (φ : TestFunction (spatialDimension + 1)),
    (waveAdjointAction W φ).Equiv φ.atOrigin

/-- A spacetime action is retarded when it vanishes on tests whose certified
support box lies strictly before time zero. Coordinate zero is time. -/
def IsRetardedReal {spatialDimension : Nat}
    {tests : TestFunctionSpace (spatialDimension + 1)}
    (T : Distribution tests) : Prop :=
  ∀ φ, φ.support.upper 0 < 0 →
    (T.action φ).Equiv (RealCompute.ofRat 0)

/-- The heat and wave targets include causality, not only the source identity. -/
def IsHeatFundamentalSolution {spatialDimension : Nat}
    {tests : TestFunctionSpace (spatialDimension + 1)}
    (H : Distribution tests) : Prop :=
  ∀ (φ : ComplexTestFunction (spatialDimension + 1)),
    (heatAdjointComplexAction H φ).Equiv φ.atOrigin

def IsWaveFundamentalSolution {spatialDimension : Nat}
    {tests : TestFunctionSpace (spatialDimension + 1)}
    (W : Distribution tests) : Prop :=
  ∀ (φ : ComplexTestFunction (spatialDimension + 1)),
    (waveAdjointComplexAction W φ).Equiv φ.atOrigin

theorem isWaveFundamentalSolution_iff_real {spatialDimension : Nat}
    {tests : TestFunctionSpace (spatialDimension + 1)}
    {W : Distribution tests} :
    IsWaveFundamentalSolution W ↔ IsWaveFundamentalSolutionReal tests W := by
  constructor
  · intro h φ
    exact (h ⟨φ, φ⟩).1
  · intro h φ
    exact ⟨h φ.re, h φ.im⟩

/-- Retarded support is checked on both channels of a complex test. -/
def IsRetarded {spatialDimension : Nat}
    {tests : TestFunctionSpace (spatialDimension + 1)}
    (T : Distribution tests) : Prop :=
  ∀ φ : ComplexTestFunction (spatialDimension + 1),
    φ.re.support.upper 0 < 0 → φ.im.support.upper 0 < 0 →
      (T.action φ.re).Equiv (RealCompute.ofRat 0) ∧
      (T.action φ.im).Equiv (RealCompute.ofRat 0)

def IsRetardedHeatFundamentalSolution {spatialDimension : Nat}
    {tests : TestFunctionSpace (spatialDimension + 1)}
    (H : Distribution tests) : Prop :=
  IsHeatFundamentalSolution H ∧ IsRetarded H

def IsRetardedWaveFundamentalSolution {spatialDimension : Nat}
    {tests : TestFunctionSpace (spatialDimension + 1)}
    (W : Distribution tests) : Prop :=
  IsWaveFundamentalSolution W ∧ IsSupportedIn W InForwardLightCone

theorem waveConeSupport_isRetarded {spatialDimension : Nat}
    {tests : TestFunctionSpace (spatialDimension + 1)}
    {W : Distribution tests} (h : IsSupportedIn W InForwardLightCone) :
    IsRetarded W := by
  have before (φ : TestFunction (spatialDimension + 1))
      (hφ : φ.support.upper 0 < 0) : φ.VanishesNear InForwardLightCone := by
    let ε : Rat := -(φ.support.upper 0) / 2
    have hε : 0 < ε := by
      change 0 < -(φ.support.upper 0) * (2 : Rat)⁻¹
      exact Rat.mul_pos (by grind only) (Rat.inv_pos.mpr (by decide +kernel))
    refine ⟨ε, hε, fun p hp q hclose => ?_⟩
    apply φ.derivative_vanishes_off_support (zeroIndex _) q
    intro hq
    have hp₀ : 0 ≤ p 0 := hp.1
    have hq₀ : q 0 ≤ φ.support.upper 0 := (hq 0).2
    have hc : p 0 ≤ q 0 + ε := (hclose 0).2
    dsimp [ε] at hc
    grind only
  intro φ hre him
  exact ⟨h φ.re (before φ.re hre), h φ.im (before φ.im him)⟩

/-- Strong Huygens support, as opposed to support anywhere inside the cone. -/
def HasWavefrontSupport {spatialDimension : Nat}
    {tests : TestFunctionSpace (spatialDimension + 1)}
    (W : Distribution tests) : Prop :=
  IsSupportedIn W OnForwardLightCone

/-- A nonzero test can probe the source inside any prescribed rational cube
around the vertex. -/
def HasLocalizedOriginTests (dimension : Nat) : Prop :=
  ∀ r : Rat, 0 < r → ∃ φ : TestFunction dimension,
    (∀ i, -r ≤ φ.support.lower i ∧ φ.support.upper i ≤ r) ∧
      φ.atOrigin.Equiv (RealCompute.ofRat 1)

/-- All-dimensions Laplace target, stated independently of any chosen
approximation sequence. -/
def LaplaceAllDimensionsTarget
    (tests : ∀ dimension, 0 < dimension → TestFunctionSpace dimension)
    (kernels : ∀ dimension (h : 0 < dimension),
      Distribution (tests dimension h)) : Prop :=
  ∀ dimension (h : 0 < dimension),
    IsLaplaceFundamentalSolution (kernels dimension h)

/-- All-dimensions heat target, stated independently of any chosen
approximation sequence. -/
def HeatAllDimensionsTarget
    (tests : ∀ spatialDimension, 0 < spatialDimension →
      TestFunctionSpace (spatialDimension + 1))
    (kernels : ∀ spatialDimension (h : 0 < spatialDimension),
      Distribution (tests spatialDimension h)) : Prop :=
  ∀ spatialDimension (h : 0 < spatialDimension),
    IsRetardedHeatFundamentalSolution (kernels spatialDimension h)

/-- All-dimensions wave target, stated independently of any chosen
approximation sequence. -/
def WaveAllDimensionsTarget
    (tests : ∀ spatialDimension, 0 < spatialDimension →
      TestFunctionSpace (spatialDimension + 1))
    (kernels : ∀ spatialDimension (h : 0 < spatialDimension),
      Distribution (tests spatialDimension h)) : Prop :=
  ∀ spatialDimension (h : 0 < spatialDimension),
    IsRetardedWaveFundamentalSolution (kernels spatialDimension h) ∧
    (3 ≤ spatialDimension → spatialDimension % 2 = 1 →
      HasWavefrontSupport (kernels spatialDimension h))

/-! The following propositions isolate the exact source and support
identities. The stronger formula and construction targets are in
`MissionTargets.lean`. -/

/-- Construct a continuous linear Laplace fundamental solution in every
positive dimension, with the exact identity on complex-valued tests. -/
def LaplaceFundamentalSolutionsExist : Prop :=
  ∃ (tests : ∀ dimension, 0 < dimension → TestFunctionSpace dimension),
    ∃ (kernels : ∀ dimension (h : 0 < dimension),
      Distribution (tests dimension h)),
      LaplaceAllDimensionsTarget tests kernels

/-- Mission root: construct the retarded heat fundamental solution in every
positive spatial dimension. Tests include the initial-time boundary. -/
def RetardedHeatFundamentalSolutionsExist : Prop :=
  ∃ (tests : ∀ spatialDimension, 0 < spatialDimension →
      TestFunctionSpace (spatialDimension + 1)),
    ∃ (kernels : ∀ spatialDimension (h : 0 < spatialDimension),
      Distribution (tests spatialDimension h)),
      HeatAllDimensionsTarget tests kernels

/-- Construct retarded wave fundamental solutions in every positive spatial
dimension, with strong Huygens support in odd dimensions at least three. -/
def RetardedWaveFundamentalSolutionsExist : Prop :=
  ∃ (tests : ∀ spatialDimension, 0 < spatialDimension →
      TestFunctionSpace (spatialDimension + 1)),
    ∃ (kernels : ∀ spatialDimension (h : 0 < spatialDimension),
      Distribution (tests spatialDimension h)),
      (∀ spatialDimension, 0 < spatialDimension →
        HasLocalizedOriginTests (spatialDimension + 1)) ∧
      WaveAllDimensionsTarget tests kernels

/-- Combined long-range mission goal. The three conjuncts remain separate so
each fundamental solution can be developed and reviewed independently. -/
def AllThreeFundamentalSolutionsExist : Prop :=
  LaplaceFundamentalSolutionsExist ∧
  RetardedHeatFundamentalSolutionsExist ∧
  RetardedWaveFundamentalSolutionsExist

/-- A continuous linear kernel and its Laplace source identity in every
positive spatial dimension. -/
structure LaplaceAllDimensionsGoal where
  testSpaces : ∀ dimension, 0 < dimension → TestFunctionSpace dimension
  kernels : ∀ dimension (h : 0 < dimension),
    Distribution (testSpaces dimension h)
  satisfies : LaplaceAllDimensionsTarget testSpaces kernels

/-- Constructive deliverable for the retarded heat operator in every positive
spatial dimension. -/
structure HeatAllDimensionsGoal where
  testSpaces : ∀ spatialDimension, 0 < spatialDimension →
    TestFunctionSpace (spatialDimension + 1)
  kernels : ∀ spatialDimension (h : 0 < spatialDimension),
    Distribution (testSpaces spatialDimension h)
  satisfies : HeatAllDimensionsTarget testSpaces kernels

/-- Constructive deliverable for the retarded wave operator in every positive
spatial dimension. -/
structure WaveAllDimensionsGoal where
  testSpaces : ∀ spatialDimension, 0 < spatialDimension →
    TestFunctionSpace (spatialDimension + 1)
  kernels : ∀ spatialDimension (h : 0 < spatialDimension),
    Distribution (testSpaces spatialDimension h)
  originTests : ∀ spatialDimension, 0 < spatialDimension →
    HasLocalizedOriginTests (spatialDimension + 1)
  satisfies : WaveAllDimensionsTarget testSpaces kernels

end ComputableDistributions


