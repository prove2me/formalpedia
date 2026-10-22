-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P24
-- name    : QAlgorithms_Papers_Independent_Gap48_P24
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T22:25:56.123608+00:00
-- url     : https://prove2.me/theorems/05c7cdb8-0eac-494b-8e82-7c5b8ee3beb8
-- title:
--   Definitions for A Continuity Theorem for Stinespring's Dilation
-- statement:
--   The objects the formalized statements of *A Continuity Theorem for Stinespring's Dilation* (arXiv:0710.2495) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `CompleteComplexHilbert`: PDF pp.1–4: arbitrary complete complex Hilbert spaces, with no separability bound.
--   - `IsCStarCompletelyPositive`: Complete positivity of a bounded complex-linear map. In a C*-algebra the positive cone is exactly {x* x}; requiring every finite amplification to preserve this cone is the usual definition, without choosing an auxiliary order instance.
--   - `cstarCompletelyBoundedNorm`: PDF pp.2–3: stabilized operator norm. For CP maps and their differences this set contains zero and is bounded above; no finiteness hypothesis is assumed.
--   - `RepresentationData`: PDF p.2: the carrier and action of a potential representation. Validity is checked by `IsRepresentation`, and is required in every dilation fiber. Keeping that predicate separate permits the literal direct-sum construction below.
--   - `IsRepresentation`: PDF pp.2–3: a nondegenerate *-representation. Nondegeneracy is the closed span of pi(A)K being all of K; on unital A it forces pi(1)=I.
--   - `dilationFiber`: PDF pp.2,4: V is bounded, with no isometry or normalization requirement.
--   - `piDistance`: PDF p.4, (4): the real pi-distance, retaining the printed empty-fiber default.
--   - `dilationBures`: PDF p.4, (5), correction C1: infimum over actual common dilation pairs. This is the flattened infimum over representations with both fibers nonempty. Stinespring's theorem gives nonemptiness on CP inputs; all costs are nonnegative.
--   - `IsMinimalStinespring`: PDF p.2: minimality means dense linear span, not density of the raw set.
--   - `hilbertSum`: PDF pp.4,9: the Hilbert direct sum, equipped with its L2 norm.
--   - `sumOperator`: PDF p.9, (22)–(23): block-diagonal operator on the actual Hilbert direct sum.
--   - `sumRepresentation`: PDF pp.4,9: the representation pi1 direct-sum pi2, constructed from its actions.
--   - `overlapSet`: PDF p.7, (15): overlaps from the two fibers in one common representation.
--   - `intertwinerSet`: PDF p.8, (18): all contraction intertwiners, intertwining every a in A.
--   - `commonOverlaps`: PDF p.8, (19): union over admissible common representations, as in C1.
--   - `IsExtension`: PDF p.5, (8)–(9): the intrinsic two-by-two CP extensions. This construction uses the actual C*-matrix algebra, including its operator norm.
--   - `extensionCost`: PDF p.5, (8): cost of an intrinsic extension, evaluated at 1_A.
--   - `intrinsicBures`: PDF p.5, Definition 2: intrinsic Bures distance. For CP inputs the extension set is nonempty (the diagonal extension) and all its costs are nonnegative.
--   - `IsInjective`: PDF pp.5,13: injectivity via its equivalent conditional-expectation characterization: every faithful concrete realization has a contractive CP retraction. P lands in B rather than sigma(B), using the inverse faithful map. This is an algebra property, independent of T1 and T2.
--   - `traceVariational`: PDF p.7, (16): trace-class variational quantity. The accepted nuclear trace-class space and basis trace work on arbitrary Hilbert spaces. For H=0 there is no unit-trace operator, and the variational value is explicitly zero.
--   - `IsPositiveFunctional`: PDF pp.15–16: bounded positive functionals, without unit-trace normalization. Positivity on all a* a is positivity on the full C*-positive cone.
--   - `scalarFiber`: PDF pp.4,15–16: scalar GNS fiber, using nondegenerate nonunital representations.
--   - `scalarBures`: PDF pp.4,15–16: scalar dilation Bures distance, with the same C1 restriction. GNS direct sums give common fibers for all bounded positive functionals. For scalar output the operator V : ℂ → K is identified with V(1).
-- source:
--   A Continuity Theorem for Stinespring's Dilation, arXiv:0710.2495v1, https://arxiv.org/abs/0710.2495v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13

/-!
Kretschmann, Schlingemann and Werner, arXiv:0710.2495v1.
All citations are PDF page numbers. Main-section algebras are unital; Appendix B
allows nonunital algebras. Hilbert spaces are arbitrary, including the zero space.
Generic C*-algebras carry PartialOrder and StarOrderedRing instances, expressing
the canonical positive cone (every C*-algebra admits this order). These instances
are needed by Mathlib CStarMatrix and impose no additional mathematical restriction.
C1 (PDF p.4): the global infimum uses common representations only, rather than
including the artificial empty-fiber value 2. The latter would cap every distance
at 2 and contradict the unrestricted CP-map bounds. The local pi-distance retains
that printed default. C2 (PDF p.7): Lemma 4 is restricted to common representations,
as required by its proof; its zero-Hilbert-space value is explicitly zero.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

open scoped ComplexOrder

namespace QAlgorithms.Papers.Independent.Gap48.P24

universe u v

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- PDF pp.1–4: arbitrary complete complex Hilbert spaces, with no separability bound. -/
structure CompleteComplexHilbert where
  carrier : Type u
  [normed : NormedAddCommGroup carrier]
  [innerProduct : InnerProductSpace ℂ carrier]
  [complete : CompleteSpace carrier]

attribute [instance] CompleteComplexHilbert.normed CompleteComplexHilbert.innerProduct CompleteComplexHilbert.complete

/-- The carrier of a bundled Hilbert space. -/
instance completeComplexHilbertCoeSort : CoeSort CompleteComplexHilbert.{u} (Type u) := ⟨CompleteComplexHilbert.carrier⟩

/-- Complete positivity of a bounded complex-linear map. In a C*-algebra the
positive cone is exactly {x* x}; requiring every finite amplification to preserve
this cone is the usual definition, without choosing an auxiliary order instance. -/
def IsCStarCompletelyPositive {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] (T : A →L[ℂ] B) : Prop :=
  ∀ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A),
    ∃ Y : CStarMatrix (Fin n) (Fin n) B, (star X * X).map T = star Y * Y

/-- PDF pp.2–3: stabilized operator norm. For CP maps and their differences this
set contains zero and is bounded above; no finiteness hypothesis is assumed. -/
def cstarCompletelyBoundedNorm {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] (T : A → B) : ℝ :=
  sSup {r : ℝ | ∃ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A),
    ‖X‖ ≤ 1 ∧ r = ‖X.map T‖}

/-- PDF p.2: the carrier and action of a potential representation. Validity is
checked by `IsRepresentation`, and is required in every dilation fiber. Keeping
that predicate separate permits the literal direct-sum construction below. -/
structure RepresentationData (A : Type u) where
  K : CompleteComplexHilbert.{u}
  act : A → (K →L[ℂ] K)

/-- PDF pp.2–3: a nondegenerate *-representation. Nondegeneracy is the closed
span of pi(A)K being all of K; on unital A it forces pi(1)=I. -/
def IsRepresentation {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (R : RepresentationData A) : Prop :=
  (∃ pi : A →⋆ₙₐ[ℂ] (R.K →L[ℂ] R.K), ∀ a, R.act a = pi a) ∧
  (Submodule.span ℂ {z : R.K | ∃ a : A, ∃ x : R.K, z = R.act a x}).topologicalClosure = ⊤

/-- PDF pp.2,4: V is bounded, with no isometry or normalization requirement. -/
def dilationFiber {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (H : CompleteComplexHilbert.{u})
    (T : A → (H →L[ℂ] H)) (R : RepresentationData A) : Set (H →L[ℂ] R.K) :=
  {V | IsRepresentation R ∧ ∀ a, T a = V.adjoint.comp ((R.act a).comp V)}

/-- PDF p.4, (4): the real pi-distance, retaining the printed empty-fiber default. -/
def piDistance {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (H : CompleteComplexHilbert.{u})
    (T1 T2 : A → (H →L[ℂ] H)) (R : RepresentationData A) : ℝ :=
  if (dilationFiber H T1 R).Nonempty ∧ (dilationFiber H T2 R).Nonempty then
    sInf {r : ℝ | ∃ V1 ∈ dilationFiber H T1 R, ∃ V2 ∈ dilationFiber H T2 R,
      r = ‖V1 - V2‖}
  else 2

/-- PDF p.4, (5), correction C1: infimum over actual common dilation pairs.
This is the flattened infimum over representations with both fibers nonempty.
Stinespring's theorem gives nonemptiness on CP inputs; all costs are nonnegative. -/
def dilationBures {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (H : CompleteComplexHilbert.{u})
    (T1 T2 : A → (H →L[ℂ] H)) : ℝ :=
  sInf {r : ℝ | ∃ R : RepresentationData A,
    ∃ V1 ∈ dilationFiber H T1 R, ∃ V2 ∈ dilationFiber H T2 R, r = ‖V1 - V2‖}

/-- PDF p.2: minimality means dense linear span, not density of the raw set. -/
def IsMinimalStinespring {A : Type u} (H : CompleteComplexHilbert.{u}) (R : RepresentationData A)
    (V : H →L[ℂ] R.K) : Prop :=
  (Submodule.span ℂ {z : R.K | ∃ a : A, ∃ x : H, z = R.act a (V x)}).topologicalClosure = ⊤

/-- PDF pp.4,9: the Hilbert direct sum, equipped with its L2 norm. -/
def hilbertSum (K1 K2 : CompleteComplexHilbert.{u}) : CompleteComplexHilbert.{u} where
  carrier := WithLp 2 (K1 × K2)

/-- PDF p.9, (22)–(23): block-diagonal operator on the actual Hilbert direct sum. -/
def sumOperator {K1 K2 : CompleteComplexHilbert.{u}} (B1 : (K1 →L[ℂ] K1)) (B2 : (K2 →L[ℂ] K2)) :
    ((hilbertSum K1 K2) →L[ℂ] (hilbertSum K1 K2)) :=
  let E := WithLp.prodContinuousLinearEquiv 2 ℂ K1 K2
  E.symm.toContinuousLinearMap.comp ((B1.prodMap B2).comp E.toContinuousLinearMap)

/-- PDF pp.4,9: the representation pi1 direct-sum pi2, constructed from its actions. -/
def sumRepresentation {A : Type u} (R1 R2 : RepresentationData A) : RepresentationData A where
  K := hilbertSum R1.K R2.K
  act a := sumOperator (R1.act a) (R2.act a)

/-- PDF p.7, (15): overlaps from the two fibers in one common representation. -/
def overlapSet {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (H : CompleteComplexHilbert.{u})
    (T1 T2 : A → (H →L[ℂ] H)) (R : RepresentationData A) : Set ((H →L[ℂ] H)) :=
  {N | ∃ V1 ∈ dilationFiber H T1 R, ∃ V2 ∈ dilationFiber H T2 R,
    N = V1.adjoint.comp V2}

/-- PDF p.8, (18): all contraction intertwiners, intertwining every a in A. -/
def intertwinerSet {A : Type u} (H : CompleteComplexHilbert.{u}) (R1 R2 : RepresentationData A)
    (V1 : H →L[ℂ] R1.K) (V2 : H →L[ℂ] R2.K) : Set ((H →L[ℂ] H)) :=
  {M | ∃ W : R2.K →L[ℂ] R1.K, ‖W‖ ≤ 1 ∧
    (∀ a, W.comp (R2.act a) = (R1.act a).comp W) ∧
    M = V1.adjoint.comp (W.comp V2)}

/-- PDF p.8, (19): union over admissible common representations, as in C1. -/
def commonOverlaps {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (H : CompleteComplexHilbert.{u})
    (T1 T2 : A → (H →L[ℂ] H)) : Set ((H →L[ℂ] H)) :=
  {N | ∃ R : RepresentationData A,
    (dilationFiber H T1 R).Nonempty ∧ (dilationFiber H T2 R).Nonempty ∧
    N ∈ overlapSet H T1 T2 R}

/-- PDF p.5, (8)–(9): the intrinsic two-by-two CP extensions. This construction
uses the actual C*-matrix algebra, including its operator norm. -/
def IsExtension {A : Type u} {B : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (T1 T2 : A → B) (E : A →L[ℂ] CStarMatrix (Fin 2) (Fin 2) B) : Prop :=
  IsCStarCompletelyPositive E ∧ ∀ a, E a 0 0 = T1 a ∧ E a 1 1 = T2 a

/-- PDF p.5, (8): cost of an intrinsic extension, evaluated at 1_A. -/
def extensionCost {A : Type u} {B : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (E : A →L[ℂ] CStarMatrix (Fin 2) (Fin 2) B) : ℝ :=
  Real.sqrt ‖E 1 0 0 + E 1 1 1 - E 1 0 1 - E 1 1 0‖

/-- PDF p.5, Definition 2: intrinsic Bures distance. For CP inputs the extension
set is nonempty (the diagonal extension) and all its costs are nonnegative. -/
def intrinsicBures {A : Type u} {B : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (T1 T2 : A → B) : ℝ :=
  sInf {r : ℝ | ∃ E : A →L[ℂ] CStarMatrix (Fin 2) (Fin 2) B,
    IsExtension T1 T2 E ∧ r = extensionCost E}

/-- PDF pp.5,13: injectivity via its equivalent conditional-expectation
characterization: every faithful concrete realization has a contractive CP
retraction. P lands in B rather than sigma(B), using the inverse faithful map.
This is an algebra property, independent of T1 and T2. -/
def IsInjective (B : Type u) [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] : Prop :=
  ∀ (H : CompleteComplexHilbert.{u}) (sigma : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)), Function.Injective sigma →
    ∃ P : (H →L[ℂ] H) →L[ℂ] B, IsCStarCompletelyPositive P ∧ ‖P‖ ≤ 1 ∧ ∀ b, P (sigma b) = b

/-- PDF p.7, (16): trace-class variational quantity. The accepted nuclear
trace-class space and basis trace work on arbitrary Hilbert spaces. For H=0
there is no unit-trace operator, and the variational value is explicitly zero. -/
def traceVariational {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (H : CompleteComplexHilbert.{u})
    {I : Type u} (b : HilbertBasis I ℂ H) (T1 T2 : A → (H →L[ℂ] H))
    (R : RepresentationData A) : ℝ :=
  if Subsingleton H then 0 else
    sInf {r : ℝ | ∃ N ∈ overlapSet H T1 T2 R,
      r = sSup {q : ℝ | ∃ rho : QAlgorithms.Papers.Independent.Dependency50.P13.State b,
        q = (QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace b
          (rho.val.val.comp (T1 1))).re +
          (QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace b
          (rho.val.val.comp (T2 1))).re -
          2 * (QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace b
          (rho.val.val.comp N)).re}}

/-- PDF pp.15–16: bounded positive functionals, without unit-trace normalization.
Positivity on all a* a is positivity on the full C*-positive cone. -/
def IsPositiveFunctional {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (omega : A →L[ℂ] ℂ) : Prop :=
  ∀ a, (omega (star a * a)).im = 0 ∧ 0 ≤ (omega (star a * a)).re

/-- PDF pp.4,15–16: scalar GNS fiber, using nondegenerate nonunital representations. -/
def scalarFiber {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (omega : A → ℂ) (R : RepresentationData A) : Set R.K :=
  {psi | IsRepresentation R ∧ ∀ a, omega a = inner ℂ psi (R.act a psi)}

/-- PDF pp.4,15–16: scalar dilation Bures distance, with the same C1 restriction.
GNS direct sums give common fibers for all bounded positive functionals.
For scalar output the operator V : ℂ → K is identified with V(1). -/
def scalarBures {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (omega0 omega1 : A → ℂ) : ℝ :=
  sInf {r : ℝ | ∃ R : RepresentationData A,
    ∃ psi0 ∈ scalarFiber omega0 R, ∃ psi1 ∈ scalarFiber omega1 R, r = ‖psi0 - psi1‖}

/-- Sanity: amplification applies the map to the actual selected matrix entry. -/
example {A : Type u} {B : Type v} (T : A → B) (n : ℕ)
    (X : CStarMatrix (Fin n) (Fin n) A) (i j : Fin n) :
    X.map T i j = T (X i j) := rfl

/-- Sanity: the zero bounded map is completely positive, including n=0. -/
example {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] :
    IsCStarCompletelyPositive (0 : A →L[ℂ] B) := by
  intro n X
  refine ⟨0, ?_⟩
  rw [star_zero, mul_zero]
  ext i j
  rfl

/-- Sanity: complete positivity does not exclude the identity map. -/
example {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] : IsCStarCompletelyPositive (ContinuousLinearMap.id ℂ A) := by
  intro n X
  refine ⟨X, ?_⟩
  ext i j
  rfl

/-- Sanity: direct-sum action has the source's block order. -/
example {K1 K2 : CompleteComplexHilbert.{u}} (B1 : (K1 →L[ℂ] K1)) (B2 : (K2 →L[ℂ] K2)) (x : K1) (y : K2) :
    sumOperator B1 B2 (WithLp.toLp 2 (x, y)) = WithLp.toLp 2 (B1 x, B2 y) := rfl

/-- Sanity: the extension cost is zero on the zero extension. -/
example {A : Type u} {B : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] :
    extensionCost (0 : A →L[ℂ] CStarMatrix (Fin 2) (Fin 2) B) = 0 := by
  simp [extensionCost, CStarMatrix.zero_apply]

/-- Sanity: a zero vector realizes the zero functional in every valid representation. -/
example {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (R : RepresentationData A)
    (hR : IsRepresentation R) : (0 : R.K) ∈ scalarFiber (fun _ => 0) R := by
  refine ⟨hR, ?_⟩
  intro a
  simp

/-- Sanity: an inadmissible representation retains the printed local default 2. -/
example {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (H : CompleteComplexHilbert.{u}) (T1 T2 : A → (H →L[ℂ] H)) (R : RepresentationData A)
    (h : ¬ ((dilationFiber H T1 R).Nonempty ∧ (dilationFiber H T2 R).Nonempty)) :
    piDistance H T1 T2 R = 2 := by
  simp [piDistance, h]

/-- Sanity: the trace variational expression has its declared zero-space value. -/
example {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (H : CompleteComplexHilbert.{u}) [Subsingleton H] {I : Type u} (b : HilbertBasis I ℂ H)
    (T1 T2 : A → (H →L[ℂ] H)) (R : RepresentationData A) :
    traceVariational H b T1 T2 R = 0 := by
  simp [traceVariational, (inferInstance : Subsingleton H)]

end QAlgorithms.Papers.Independent.Gap48.P24


