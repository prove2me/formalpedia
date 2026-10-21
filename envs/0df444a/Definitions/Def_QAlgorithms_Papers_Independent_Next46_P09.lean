-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P09
-- name    : QAlgorithms_Papers_Independent_Next46_P09
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T13:59:13.116103+00:00
-- url     : https://prove2.me/theorems/5bc8f3f7-f08c-4d02-88fa-487be4367804
-- title:
--   Definitions for Unbounded generators of dynamical semigroups
-- statement:
--   The objects the formalized statements of *Unbounded generators of dynamical semigroups* (arXiv:1707.02266) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsTraceLinear`: PDF pp.1–2: complex linearity on the full nuclear trace-class subtype. The sum/scalar identities are expressed on the underlying bounded operators; closure of nuclear operators under these operations is not a new assumption.
--   - `IsPositiveBlock`: PDF pp.1–2: positivity of a finite matrix of actual trace-class operators. Complex reality is tested as well as the sign of the quadratic form.
--   - `IsTraceCP`: PDF pp.1–2: complete positivity at all finite matrix levels.
--   - `TraceDynamicalSemigroup`: PDF pp.1–2: the full Schroedinger-picture dynamical semigroup. The arbitrary Hilbert basis only writes the basis-independent nuclear trace. Continuity is exactly the trace-pairing continuity at zero in Problem I.1.
--   - `IsNoEvent`: PDF p.3, Definition II.1: every normalized pure input is sent to a nonnegative multiple of a normalized pure state; the multiplier may be zero.
--   - `InTraceGeneratorGraph`: PDF pp.2,7: the actual full trace-norm right-derivative graph. No arbitrary closed extension of a formal expression is substituted. Every argument of traceNormValue here is a difference of trace-class operators.
--   - `TraceGeneratorDomain`: PDF p.7, (13): the full actual generator domain.
--   - `IsLaplaceResolvent`: PDF p.7, (11): the actual Laplace resolvent characterized by all bounded trace-pairing tests. Integrability is explicit, so the Bochner integral cannot silently take its nonintegrable default value. Only lambda > 0 is used.
--   - `ClassicalSpace`: PDF p.3: the classical state space is full l1(X), including signed inputs.
--   - `pointMass`: PDF p.3: the normalized point mass at x.
--   - `ClassicalNoEventSemigroup`: PDF p.3: a classical no-event semigroup on a countable discrete set. No fixed-point conclusion is built into the definition: the output atom y may initially differ from the input atom x. Positivity and contraction express nonincrease of total mass on positive inputs.
--   - `IsHilbertGenerator`: PDF p.5: K is precisely the full Hilbert-norm right-derivative generator of C, on D. This is a hypothesis on the given generator, not on an exit space.
--   - `MinimalExitSpace`: PDF p.5, (6): an exact minimal exit space. Dense range describes the separated completion of D in the loss form, including its null-space quotient.
--   - `DomainPerturbation`: PDF p.8, Proposition II.4: a linear CP perturbation on the actual domain. Its ambient function is merely a totalization: all linearity, positivity and trace conditions below test only inputs in the full generator domain.
--   - `TraceCPDominates`: PDF p.8: CP order compares every matrix level, not only positive inputs.
--   - `ResolventFixedPoint`: PDF p.8, (15): the fixed-point equation on the full complex trace class.
--   - `IsMinimalPerturbation`: PDF pp.8–9, (16): the minimal perturbation construction, characterized by its actual Laplace resolvents, strong series, and smallest CP solution. The partial sum converges on each trace-class input in trace norm.
--   - `PerturbationRange`: PDF p.9: finite rank means finite-dimensional range of the perturbation map on its domain; it does not mean that individual output operators have finite rank as operators on H. Values of the totalization outside the actual domain do not enter this span.
-- source:
--   Unbounded generators of dynamical semigroups, arXiv:1707.02266v1, https://arxiv.org/abs/1707.02266v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P50

/-!
Unbounded generators of dynamical semigroups, arXiv:1707.02266v1.
Only the six nodes explicitly listed in items.json are stated here.
Other nodes and missing analytic interfaces are recorded in HARD.md/GAPS.json.
Compilation is pending the authorized batch handoff.

The nuclear trace-class subtype is the entire complex trace class, not just
states. Algebraic relations below are tested on underlying bounded operators;
no operator-norm topology is imposed on the trace-class subtype. Trace-norm
limits use the accepted nuclear norm on trace-class differences explicitly.
-/

noncomputable section

open Filter MeasureTheory
open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P09

universe u v

open QAlgorithms.Papers.Independent.Dependency50.P13
  (TraceClass IsTraceClass traceNormValue operatorTrace IsPositive)
open QAlgorithms.Papers.Independent.Claimed50.P50 (ContractionSemigroup)

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]

/-- PDF pp.1–2: complex linearity on the full nuclear trace-class subtype.
The sum/scalar identities are expressed on the underlying bounded operators;
closure of nuclear operators under these operations is not a new assumption. -/
def IsTraceLinear (F : TraceClass H → TraceClass H) : Prop :=
  (∀ rho sigma tau : TraceClass H, tau.val = rho.val + sigma.val →
    (F tau).val = (F rho).val + (F sigma).val) ∧
  (∀ (c : ℂ) (rho tau : TraceClass H), tau.val = c • rho.val →
    (F tau).val = c • (F rho).val)

/-- PDF pp.1–2: positivity of a finite matrix of actual trace-class operators.
Complex reality is tested as well as the sign of the quadratic form. -/
def IsPositiveBlock {n : ℕ} (a : Fin n → Fin n → TraceClass H) : Prop :=
  ∀ z : Fin n → H,
    (∑ i, ∑ j, inner ℂ (z i) ((a i j).val (z j))).im = 0 ∧
    0 ≤ (∑ i, ∑ j, inner ℂ (z i) ((a i j).val (z j))).re

/-- PDF pp.1–2: complete positivity at all finite matrix levels. -/
def IsTraceCP (F : TraceClass H → TraceClass H) : Prop :=
  ∀ (n : ℕ) (a : Fin n → Fin n → TraceClass H),
    IsPositiveBlock a → IsPositiveBlock (fun i j => F (a i j))

/-- PDF pp.1–2: the full Schroedinger-picture dynamical semigroup.
The arbitrary Hilbert basis only writes the basis-independent nuclear trace.
Continuity is exactly the trace-pairing continuity at zero in Problem I.1. -/
structure TraceDynamicalSemigroup {I : Type v} (b : HilbertBasis I ℂ H) where
  maps : NNReal → TraceClass H → TraceClass H
  linear : ∀ t, IsTraceLinear (maps t)
  completelyPositive : ∀ t, IsTraceCP (maps t)
  initial : ∀ rho, maps 0 rho = rho
  semigroup : ∀ s t rho, maps (s + t) rho = maps s (maps t rho)
  traceNonIncreasing : ∀ t rho, IsPositive rho.val →
    (operatorTrace b (maps t rho).val).re ≤ (operatorTrace b rho.val).re
  pairingContinuous : ∀ (rho : TraceClass H) (A : H →L[ℂ] H),
    ContinuousAt (fun t : NNReal => operatorTrace b ((maps t rho).val.comp A)) 0

/-- PDF p.3, Definition II.1: every normalized pure input is sent to a
nonnegative multiple of a normalized pure state; the multiplier may be zero. -/
def IsNoEvent {I : Type v} {b : HilbertBasis I ℂ H}
    (T : TraceDynamicalSemigroup b) : Prop :=
  ∀ (t : NNReal) (psi : H), ‖psi‖ = 1 →
    ∀ rho : TraceClass H, rho.val = InnerProductSpace.rankOne ℂ psi psi →
      ∃ (a : NNReal) (phi : H), ‖phi‖ = 1 ∧
        (T.maps t rho).val = (a : ℂ) • InnerProductSpace.rankOne ℂ phi phi

/-- PDF pp.2,7: the actual full trace-norm right-derivative graph.
No arbitrary closed extension of a formal expression is substituted. Every
argument of traceNormValue here is a difference of trace-class operators. -/
def InTraceGeneratorGraph {I : Type v} {b : HilbertBasis I ℂ H}
    (T : TraceDynamicalSemigroup b) (rho eta : TraceClass H) : Prop :=
  Tendsto
    (fun t : ℝ => traceNormValue
      (((t : ℂ)⁻¹) • ((T.maps t.toNNReal rho).val - rho.val) - eta.val))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

/-- PDF p.7, (13): the full actual generator domain. -/
def TraceGeneratorDomain {I : Type v} {b : HilbertBasis I ℂ H}
    (T : TraceDynamicalSemigroup b) : Set (TraceClass H) :=
  {rho | ∃ eta, InTraceGeneratorGraph T rho eta}

/-- PDF p.7, (11): the actual Laplace resolvent characterized by all bounded
trace-pairing tests. Integrability is explicit, so the Bochner integral cannot
silently take its nonintegrable default value. Only lambda > 0 is used. -/
def IsLaplaceResolvent {I : Type v} {b : HilbertBasis I ℂ H}
    (T : TraceDynamicalSemigroup b) (lambda : ℝ)
    (R : TraceClass H → TraceClass H) : Prop :=
  ∀ (rho : TraceClass H) (A : H →L[ℂ] H),
    IntegrableOn
      (fun t : ℝ => (Real.exp (-lambda * t) : ℂ) *
        operatorTrace b ((T.maps t.toNNReal rho).val.comp A)) (Set.Ioi 0) ∧
    operatorTrace b ((R rho).val.comp A) =
      ∫ t in Set.Ioi (0 : ℝ), (Real.exp (-lambda * t) : ℂ) *
        operatorTrace b ((T.maps t.toNNReal rho).val.comp A)

/-- PDF p.3: the classical state space is full l1(X), including signed inputs. -/
abbrev ClassicalSpace (X : Type u) := lp (fun _ : X => ℝ) 1

/-- PDF p.3: the normalized point mass at x. -/
def pointMass {X : Type u} (x : X) : ClassicalSpace X := by
  classical
  exact lp.single 1 x 1

/-- PDF p.3: a classical no-event semigroup on a countable discrete set.
No fixed-point conclusion is built into the definition: the output atom y may
initially differ from the input atom x. Positivity and contraction express
nonincrease of total mass on positive inputs. -/
structure ClassicalNoEventSemigroup (X : Type u) where
  maps : NNReal → ClassicalSpace X →L[ℝ] ClassicalSpace X
  initial : maps 0 = ContinuousLinearMap.id ℝ (ClassicalSpace X)
  semigroup : ∀ s t, maps (s + t) = (maps s).comp (maps t)
  positive : ∀ t rho, (∀ x, 0 ≤ rho x) → ∀ x, 0 ≤ maps t rho x
  contraction : ∀ t rho, ‖maps t rho‖ ≤ ‖rho‖
  continuous : ∀ rho, Continuous (fun t : NNReal => maps t rho)
  pure : ∀ t x, ∃ (a : NNReal) (y : X), maps t (pointMass x) = (a : ℝ) • pointMass y

/-- PDF p.5: K is precisely the full Hilbert-norm right-derivative generator
of C, on D. This is a hypothesis on the given generator, not on an exit space. -/
def IsHilbertGenerator (C : ContractionSemigroup H)
    (D : Submodule ℂ H) (K : D →ₗ[ℂ] H) : Prop :=
  ∀ x y : H,
    (∃ z : D, (z : H) = x ∧ K z = y) ↔
      Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) • (C.maps t.toNNReal x - x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds y)

/-- PDF p.5, (6): an exact minimal exit space. Dense range describes the
separated completion of D in the loss form, including its null-space quotient. -/
structure MinimalExitSpace (D : Submodule ℂ H) (K : D →ₗ[ℂ] H) where
  carrier : Type u
  [normed : NormedAddCommGroup carrier]
  [innerProduct : InnerProductSpace ℂ carrier]
  [complete : CompleteSpace carrier]
  j : D →ₗ[ℂ] carrier
  lossForm : ∀ psi phi : D,
    inner ℂ (j psi) (j phi) =
      -(inner ℂ (K psi) (phi : H) + inner ℂ (psi : H) (K phi))
  dense : DenseRange j

attribute [instance] MinimalExitSpace.normed MinimalExitSpace.innerProduct
  MinimalExitSpace.complete

/-- PDF p.8, Proposition II.4: a linear CP perturbation on the actual domain.
Its ambient function is merely a totalization: all linearity, positivity and
trace conditions below test only inputs in the full generator domain. -/
structure DomainPerturbation {I : Type v} {b : HilbertBasis I ℂ H}
    (T : TraceDynamicalSemigroup b) where
  maps : TraceClass H → TraceClass H
  add : ∀ rho sigma tau : TraceClass H,
    rho ∈ TraceGeneratorDomain T → sigma ∈ TraceGeneratorDomain T →
    tau ∈ TraceGeneratorDomain T → tau.val = rho.val + sigma.val →
      (maps tau).val = (maps rho).val + (maps sigma).val
  smul : ∀ (c : ℂ) (rho tau : TraceClass H),
    rho ∈ TraceGeneratorDomain T → tau ∈ TraceGeneratorDomain T →
    tau.val = c • rho.val → (maps tau).val = c • (maps rho).val
  completelyPositive : ∀ (n : ℕ) (a : Fin n → Fin n → TraceClass H),
    (∀ i j, a i j ∈ TraceGeneratorDomain T) →
    IsPositiveBlock a → IsPositiveBlock (fun i j => maps (a i j))
  traceBound : ∀ rho eta : TraceClass H, InTraceGeneratorGraph T rho eta →
    IsPositive rho.val →
      (operatorTrace b (maps rho).val).re ≤ -(operatorTrace b eta.val).re

/-- PDF p.8: CP order compares every matrix level, not only positive inputs. -/
def TraceCPDominates (X Y : TraceClass H → TraceClass H) : Prop :=
  ∀ (n : ℕ) (a : Fin n → Fin n → TraceClass H), IsPositiveBlock a →
    ∀ z : Fin n → H,
      (∑ i, ∑ j, inner ℂ (z i) (((X (a i j)).val - (Y (a i j)).val) (z j))).im = 0 ∧
      0 ≤ (∑ i, ∑ j,
        inner ℂ (z i) (((X (a i j)).val - (Y (a i j)).val) (z j))).re

/-- PDF p.8, (15): the fixed-point equation on the full complex trace class. -/
def ResolventFixedPoint (Rzero B X : TraceClass H → TraceClass H) : Prop :=
  ∀ rho, (X rho).val = (Rzero rho).val + (X (B rho)).val

/-- PDF pp.8–9, (16): the minimal perturbation construction, characterized
by its actual Laplace resolvents, strong series, and smallest CP solution.
The partial sum converges on each trace-class input in trace norm. -/
def IsMinimalPerturbation {I : Type v} {b : HilbertBasis I ℂ H}
    (Tzero : TraceDynamicalSemigroup b) (P : DomainPerturbation Tzero)
    (T : TraceDynamicalSemigroup b) : Prop :=
  ∀ lambda : ℝ, 0 < lambda →
    ∃ Rzero R : TraceClass H → TraceClass H,
      IsTraceLinear Rzero ∧ IsTraceCP Rzero ∧
      IsLaplaceResolvent Tzero lambda Rzero ∧
      IsTraceLinear R ∧ IsTraceCP R ∧ IsLaplaceResolvent T lambda R ∧
      (∀ rho, Rzero rho ∈ TraceGeneratorDomain Tzero) ∧
      IsTraceLinear (P.maps ∘ Rzero) ∧ IsTraceCP (P.maps ∘ Rzero) ∧
      (∀ rho : TraceClass H,
        Tendsto (fun m : ℕ => traceNormValue
          ((∑ n ∈ Finset.range (m + 1),
            (Rzero (((P.maps ∘ Rzero)^[n]) rho)).val) - (R rho).val))
          atTop (nhds 0)) ∧
      ResolventFixedPoint Rzero (P.maps ∘ Rzero) R ∧
      (∀ X : TraceClass H → TraceClass H, IsTraceLinear X → IsTraceCP X →
        ResolventFixedPoint Rzero (P.maps ∘ Rzero) X → TraceCPDominates X R)

/-- PDF p.9: finite rank means finite-dimensional range of the perturbation
map on its domain; it does not mean that individual output operators have
finite rank as operators on H. Values of the totalization outside the actual
domain do not enter this span. -/
def PerturbationRange {I : Type v} {b : HilbertBasis I ℂ H}
    {Tzero : TraceDynamicalSemigroup b} (P : DomainPerturbation Tzero) :
    Submodule ℂ (H →L[ℂ] H) :=
  Submodule.span ℂ {sigma | ∃ rho : TraceClass H,
    rho ∈ TraceGeneratorDomain Tzero ∧ sigma = (P.maps rho).val}

/-- The perturbation equation tests every complex input, including nonstates. -/
example (Rzero B X : TraceClass H → TraceClass H) :
    ResolventFixedPoint Rzero B X =
      (∀ rho, (X rho).val = (Rzero rho).val + (X (B rho)).val) := rfl

/-- The actual generator excludes t=0 in its difference quotient. -/
example {I : Type v} {b : HilbertBasis I ℂ H}
    (T : TraceDynamicalSemigroup b) (rho eta : TraceClass H) :
    InTraceGeneratorGraph T rho eta =
      Tendsto (fun t : ℝ => traceNormValue
        (((t : ℂ)⁻¹) • ((T.maps t.toNNReal rho).val - rho.val) - eta.val))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := rfl

/-- Rank-one operators use the source's conjugate-linear-first convention. -/
example (u v x : H) : InnerProductSpace.rankOne ℂ u v x = inner ℂ v x • u := rfl

/-- Empty CP matrix tests impose no spurious condition. -/
example (a : Fin 0 → Fin 0 → TraceClass H) : IsPositiveBlock a := by
  intro z
  simp

/-- Point masses are normalized at their own site. -/
example {X : Type u} (x : X) : pointMass x x = 1 := by
  classical
  exact lp.single_apply_self 1 x 1

/-- Zero rates give the identity multiplier, including t=0. -/
example (t : NNReal) : Real.exp (-(t : ℝ) * (0 : ℝ)) = 1 := by simp

/-- The no-event semigroup is the actual identity at time zero. -/
example {I : Type v} {b : HilbertBasis I ℂ H}
    (T : TraceDynamicalSemigroup b) (rho : TraceClass H) : T.maps 0 rho = rho :=
  T.initial rho

end QAlgorithms.Papers.Independent.Next46.P09


