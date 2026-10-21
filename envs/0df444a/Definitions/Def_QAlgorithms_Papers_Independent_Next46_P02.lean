-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02
-- name    : QAlgorithms_Papers_Independent_Next46_P02
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T12:21:49.567818+00:00
-- url     : https://prove2.me/theorems/2a00e5d0-5f0e-4436-a351-222462d20d6b
-- title:
--   Definitions for Trace-Class and Nuclear Operators
-- statement:
--   The objects the formalized statements of *Trace-Class and Nuclear Operators* (arXiv:2204.06954) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `NormOn`: PDF pp.3,7,10–11: the full norm axioms on a specified linear class. These axioms are conclusions of the results, never hypotheses on the classes.
--   - `CompleteIn`: PDF pp.15,17: completeness in the specified norm, expressed by its Cauchy criterion. Membership of sequence terms and of the limit is explicit.
--   - `banachTensorEval`: PDF p.3: evaluation of a simple tensor of continuous dual functionals.
--   - `dualTensorPairing`: PDF p.3: the canonical algebraic dual-tensor pairing, before completion.
--   - `injectiveNorm`: PDF p.3: injective norm, supremum of scalar absolute values over dual balls. The set is nonempty and bounded for every algebraic tensor.
--   - `algebraicProjectiveNorm`: PDF p.3: projective norm as infimum over all finite representations, including the empty representation of zero. The cost set is nonempty and bounded below by zero. No minimizing representation is stipulated.
--   - `ReasonableCrossnorm`: PDF p.3: a reasonable crossnorm. The pointwise dual estimate is exactly continuity of each f tensor g and its dual norm bound.
--   - `restrictedDualNorm`: PDF p.3: restriction of the alpha-dual norm to the ALGEBRAIC tensor of continuous duals. Under ReasonableCrossnorm the defining supremum is bounded.
--   - `BanachNuclearRepresentation`: PDF pp.7–8: an actual nuclear representation, with absolute norm-product summability and convergent vector sums, as opposed to unguarded tsum equations.
--   - `IsNuclear`: PDF p.8: nuclearity, using the source's explicit series redefinition.
--   - `banachNuclearNorm`: PDF pp.7–8: nuclear norm. This real infimum is used only on IsNuclear, where the cost set is nonempty and bounded below. Off that class its empty-set value is zero and is never interpreted as a finite norm.
--   - `hilbertPositiveSqrt`: PDF p.9: the nonnegative square root. It is selected by its mathematical characterization, not by an extra hypothesis supplied to a theorem. On positive operators existence and uniqueness are the Hilbert-space positive-root theorem; the fallback concerns nonpositive inputs only. The zero branch pins the zero space. This avoids imposing Mathlib's complex-only functional-calculus instance on F.
--   - `hilbertOperatorModulus`: PDF p.9: |T| is the positive square root of T* T, never of T squared.
--   - `basisIndex`: PDF p.9: choose one complete orthonormal basis, indexed by a subset of H. No countability or nonemptiness requirement is made.
--   - `referenceBasis`: PDF p.9: the chosen complete orthonormal basis; invariance is a theorem.
--   - `basisDiagonal`: PDF pp.9,16: Lean inner is conjugate linear FIRST, so this is <T e;e> in source notation. The function is defined on all bounded operators but summed as a trace only when convergence is supplied.
--   - `IsModulusTraceClass`: PDF p.9: the independent modulus/basis definition of trace class. One basis suffices by basis_independence; this definition does not mention nuclearity.
--   - `modulusTraceNorm`: PDF p.9: the trace norm, on its finite domain IsModulusTraceClass. Outside that class a nonconvergent real tsum is zero and is never used as a norm.
--   - `IsHilbertSchmidt`: PDF pp.9–10: Hilbert–Schmidt membership by square summability on a complete basis; this definition is independent of trace class and nuclearity.
--   - `hilbertSchmidtNorm`: PDF p.10: Hilbert–Schmidt norm on IsHilbertSchmidt only.
--   - `IsFiniteRank`: PDF p.2: finite rank refers to the entire bounded operator's range.
--   - `basisOperatorTrace`: PDF p.16: the actual basis-sum trace, used only with trace-class guards.
--   - `hilbertSchmidtInner`: PDF pp.16–17: Hilbert–Schmidt inner product in Lean's convention. It is tr(S* T) with Lean arguments S,T.
--   - `FiniteRankDenseIn`: PDF pp.15,17: finite-rank density measured in the specified norm.
--   - `InnerProductOn`: PDF p.16: all inner-product axioms, with the given norm, on the given class. The reversed arguments encode the source's first-linear convention faithfully.
--   - `UnitNuclearRepresentation`: PDF p.18 with p.4's finite-or-countable convention: unit-vector expansion. A subset of N indexes the family, so the empty expansion of zero is allowed, even on the zero Hilbert space. Every displayed sum is an actual convergent sum.
--   - `unitExpansionCosts`: PDF p.18: all unit-expansion costs, with no artificial upper bound.
-- source:
--   Trace-Class and Nuclear Operators, arXiv:2204.06954v2, https://arxiv.org/abs/2204.06954v2

import Mathlib

/-!
Statements from Kubrusly, Trace-Class and Nuclear Operators, arXiv:2204.06954v2.
The real and complex fields are both covered. All operators act on the full
space; no separability or nontriviality assumption is imposed. Local definitions
keep the modulus/basis definition of trace class independent of nuclearity.
Completed-projective constructions not installed here are explicitly deferred.
Names distinguish these general Banach/Hilbert definitions from the frozen
matrix-only or complex-only namesakes; ASSESSMENT.json records each comparison.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P02

open Filter
open scoped TensorProduct Topology

attribute [local instance] Classical.propDecidable

variable {F : Type*} [RCLike F]

/-- PDF pp.3,7,10–11: the full norm axioms on a specified linear class.
These axioms are conclusions of the results, never hypotheses on the classes. -/
def NormOn {E : Type*} [AddCommGroup E] [Module F E]
    (P : E → Prop) (n : E → ℝ) : Prop :=
  P 0 ∧ n 0 = 0 ∧
  (∀ x, P x → 0 ≤ n x ∧ (n x = 0 ↔ x = 0)) ∧
  (∀ x y, P x → P y → P (x + y) ∧ n (x + y) ≤ n x + n y) ∧
  (∀ (a : F) x, P x → P (a • x) ∧ n (a • x) = ‖a‖ * n x)

/-- PDF pp.15,17: completeness in the specified norm, expressed by its Cauchy
criterion. Membership of sequence terms and of the limit is explicit. -/
def CompleteIn {E : Type*} [AddCommGroup E] (P : E → Prop) (n : E → ℝ) : Prop :=
  ∀ u : ℕ → E, (∀ k, P (u k)) →
    (∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ j k : ℕ,
      N ≤ j → N ≤ k → n (u j - u k) < eps) →
    ∃ x : E, P x ∧ ∀ eps : ℝ, 0 < eps → ∃ N : ℕ,
      ∀ k : ℕ, N ≤ k → n (u k - x) < eps

section Banach

variable {X Y V W : Type*}
variable [NormedAddCommGroup X] [NormedSpace F X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace F Y] [CompleteSpace Y]
variable [NormedAddCommGroup V] [NormedSpace F V] [CompleteSpace V]
variable [NormedAddCommGroup W] [NormedSpace F W] [CompleteSpace W]

/-- PDF p.3: evaluation of a simple tensor of continuous dual functionals. -/
def banachTensorEval (f : X →L[F] F) (g : Y →L[F] F) : TensorProduct F X Y →ₗ[F] F :=
  TensorProduct.lift (f.toLinearMap.smulRight g.toLinearMap)

/-- PDF p.3: the canonical algebraic dual-tensor pairing, before completion. -/
def dualTensorPairing :
    TensorProduct F (X →L[F] F) (Y →L[F] F) →ₗ[F]
      (TensorProduct F X Y →ₗ[F] F) :=
  TensorProduct.lift (LinearMap.mk₂ F banachTensorEval
    (by intro f h g; ext x y; simp [banachTensorEval, add_mul])
    (by intro a f g; ext x y; simp [banachTensorEval, mul_assoc])
    (by intro f g h; ext x y; simp [banachTensorEval, mul_add])
    (by intro a f g; ext x y; simp [banachTensorEval, mul_left_comm, mul_assoc]))

/-- PDF p.3: injective norm, supremum of scalar absolute values over dual balls.
The set is nonempty and bounded for every algebraic tensor. -/
def injectiveNorm (u : TensorProduct F X Y) : ℝ :=
  sSup {r : ℝ | ∃ (f : X →L[F] F) (g : Y →L[F] F),
    ‖f‖ ≤ 1 ∧ ‖g‖ ≤ 1 ∧ r = ‖banachTensorEval f g u‖}

/-- PDF p.3: projective norm as infimum over all finite representations,
including the empty representation of zero. The cost set is nonempty and
bounded below by zero. No minimizing representation is stipulated. -/
def algebraicProjectiveNorm (u : TensorProduct F X Y) : ℝ :=
  sInf {r : ℝ | ∃ (n : ℕ) (x : Fin n → X) (y : Fin n → Y),
    u = ∑ k, (x k) ⊗ₜ[F] (y k) ∧ r = ∑ k, ‖x k‖ * ‖y k‖}

/-- PDF p.3: a reasonable crossnorm. The pointwise dual estimate is exactly
continuity of each f tensor g and its dual norm bound. -/
def ReasonableCrossnorm (a : TensorProduct F X Y → ℝ) : Prop :=
  NormOn (F := F) (fun _ => True) a ∧
  (∀ (x : X) (y : Y), a (x ⊗ₜ[F] y) ≤ ‖x‖ * ‖y‖) ∧
  (∀ (f : X →L[F] F) (g : Y →L[F] F) u,
    ‖banachTensorEval f g u‖ ≤ ‖f‖ * ‖g‖ * a u)

/-- PDF p.3: restriction of the alpha-dual norm to the ALGEBRAIC tensor of
continuous duals. Under ReasonableCrossnorm the defining supremum is bounded. -/
def restrictedDualNorm (a : TensorProduct F X Y → ℝ)
    (v : TensorProduct F (X →L[F] F) (Y →L[F] F)) : ℝ :=
  sSup {r : ℝ | ∃ u : TensorProduct F X Y,
    a u ≤ 1 ∧ r = ‖dualTensorPairing v u‖}

example (f : X →L[F] F) (g : Y →L[F] F) (x : X) (y : Y) :
    banachTensorEval f g (x ⊗ₜ[F] y) = f x * g y := by
  simp [banachTensorEval]

/-- PDF pp.7–8: an actual nuclear representation, with absolute norm-product
summability and convergent vector sums, as opposed to unguarded tsum equations. -/
def BanachNuclearRepresentation (T : X →L[F] Y) (f : ℕ → (X →L[F] F))
    (y : ℕ → Y) : Prop :=
  Summable (fun k => ‖f k‖ * ‖y k‖) ∧
    ∀ x : X, HasSum (fun k => (f k x) • y k) (T x)

/-- PDF p.8: nuclearity, using the source's explicit series redefinition. -/
def IsNuclear (T : X →L[F] Y) : Prop :=
  ∃ (f : ℕ → (X →L[F] F)) (y : ℕ → Y), BanachNuclearRepresentation T f y

/-- PDF pp.7–8: nuclear norm. This real infimum is used only on IsNuclear,
where the cost set is nonempty and bounded below. Off that class its empty-set
value is zero and is never interpreted as a finite norm. -/
def banachNuclearNorm (T : X →L[F] Y) : ℝ :=
  sInf {r : ℝ | ∃ (f : ℕ → (X →L[F] F)) (y : ℕ → Y),
    BanachNuclearRepresentation T f y ∧ r = ∑' k, ‖f k‖ * ‖y k‖}

example : BanachNuclearRepresentation (0 : X →L[F] Y) (fun _ => 0) (fun _ => 0) := by
  constructor
  · simp
  · intro x
    simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : Y)) 0)

end Banach

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace F H] [CompleteSpace H]

/-- PDF p.9: the nonnegative square root. It is selected by its mathematical
characterization, not by an extra hypothesis supplied to a theorem. On positive
operators existence and uniqueness are the Hilbert-space positive-root theorem;
the fallback concerns nonpositive inputs only. The zero branch pins the zero space.
This avoids imposing Mathlib's complex-only functional-calculus instance on F. -/
def hilbertPositiveSqrt (A : H →L[F] H) : H →L[F] H :=
  if A = 0 then 0 else
    if h : ∃ B : H →L[F] H, B.IsPositive ∧ B.comp B = A then
      Classical.choose h else 0

/-- PDF p.9: |T| is the positive square root of T* T, never of T squared. -/
def hilbertOperatorModulus (T : H →L[F] H) : H →L[F] H :=
  hilbertPositiveSqrt ((ContinuousLinearMap.adjoint T).comp T)

/-- PDF p.9: choose one complete orthonormal basis, indexed by a subset of H.
No countability or nonemptiness requirement is made. -/
def basisIndex (F : Type*) [RCLike F] (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace F H] [CompleteSpace H] : Set H :=
  Classical.choose (exists_hilbertBasis F H)

/-- PDF p.9: the chosen complete orthonormal basis; invariance is a theorem. -/
def referenceBasis : HilbertBasis (basisIndex F H) F H :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis F H))

/-- PDF pp.9,16: Lean inner is conjugate linear FIRST, so this is <T e;e> in
source notation. The function is defined on all bounded operators but summed
as a trace only when convergence is supplied. -/
def basisDiagonal {I : Type*} (b : HilbertBasis I F H) (T : H →L[F] H) (i : I) : F :=
  inner F (b i) (T (b i))

/-- PDF p.9: the independent modulus/basis definition of trace class.
One basis suffices by basis_independence; this definition does not mention nuclearity. -/
def IsModulusTraceClass (T : H →L[F] H) : Prop :=
  Summable (fun i : basisIndex F H => RCLike.re (basisDiagonal referenceBasis (hilbertOperatorModulus T) i))

/-- PDF p.9: the trace norm, on its finite domain IsModulusTraceClass. Outside that
class a nonconvergent real tsum is zero and is never used as a norm. -/
def modulusTraceNorm (T : H →L[F] H) : ℝ :=
  ∑' i : basisIndex F H, RCLike.re (basisDiagonal referenceBasis (hilbertOperatorModulus T) i)

/-- PDF pp.9–10: Hilbert–Schmidt membership by square summability on a complete
basis; this definition is independent of trace class and nuclearity. -/
def IsHilbertSchmidt (T : H →L[F] H) : Prop :=
  Summable (fun i : basisIndex F H => ‖T (referenceBasis i)‖ ^ 2)

/-- PDF p.10: Hilbert–Schmidt norm on IsHilbertSchmidt only. -/
def hilbertSchmidtNorm (T : H →L[F] H) : ℝ :=
  Real.sqrt (∑' i : basisIndex F H, ‖T (referenceBasis i)‖ ^ 2)

/-- PDF p.2: finite rank refers to the entire bounded operator's range. -/
def IsFiniteRank (T : H →L[F] H) : Prop :=
  FiniteDimensional F (LinearMap.range T.toLinearMap)

/-- PDF p.16: the actual basis-sum trace, used only with trace-class guards. -/
def basisOperatorTrace (T : H →L[F] H) : F :=
  ∑' i : basisIndex F H, basisDiagonal referenceBasis T i

/-- PDF pp.16–17: Hilbert–Schmidt inner product in Lean's convention.
It is tr(S* T) with Lean arguments S,T. -/
def hilbertSchmidtInner (S T : H →L[F] H) : F :=
  basisOperatorTrace ((ContinuousLinearMap.adjoint S).comp T)

/-- PDF pp.15,17: finite-rank density measured in the specified norm. -/
def FiniteRankDenseIn (P : (H →L[F] H) → Prop) (n : (H →L[F] H) → ℝ) : Prop :=
  ∀ T, P T → ∀ eps : ℝ, 0 < eps →
    ∃ S : H →L[F] H, IsFiniteRank S ∧ P S ∧ P (T - S) ∧ n (T - S) < eps

/-- PDF p.16: all inner-product axioms, with the given norm, on the given class.
The reversed arguments encode the source's first-linear convention faithfully. -/
def InnerProductOn (P : (H →L[F] H) → Prop) (n : (H →L[F] H) → ℝ)
    (ip : (H →L[F] H) → (H →L[F] H) → F) : Prop :=
  NormOn (F := F) P n ∧
  (∀ S T, P S → P T → star (ip S T) = ip T S) ∧
  (∀ S T U, P S → P T → P U → ip S (T + U) = ip S T + ip S U) ∧
  (∀ (a : F) S T, P S → P T → ip S (a • T) = a * ip S T) ∧
  (∀ T, P T → RCLike.re (ip T T) = n T ^ 2)

example : hilbertPositiveSqrt (0 : H →L[F] H) = 0 := by
  simp [hilbertPositiveSqrt]

example : hilbertOperatorModulus (0 : H →L[F] H) = 0 := by
  simp [hilbertOperatorModulus, hilbertPositiveSqrt]

example : IsModulusTraceClass (0 : H →L[F] H) := by
  simp [IsModulusTraceClass, basisDiagonal, hilbertOperatorModulus, hilbertPositiveSqrt]

example : IsHilbertSchmidt (0 : H →L[F] H) := by
  simp [IsHilbertSchmidt]

example : modulusTraceNorm (0 : H →L[F] H) = 0 := by
  simp [modulusTraceNorm, basisDiagonal, hilbertOperatorModulus, hilbertPositiveSqrt]

example : hilbertSchmidtNorm (0 : H →L[F] H) = 0 := by
  simp [hilbertSchmidtNorm]

example : basisOperatorTrace (0 : H →L[F] H) = 0 := by
  simp [basisOperatorTrace, basisDiagonal]

/-- PDF p.18 with p.4's finite-or-countable convention: unit-vector expansion.
A subset of N indexes the family, so the empty expansion of zero is allowed,
even on the zero Hilbert space. Every displayed sum is an actual convergent sum. -/
def UnitNuclearRepresentation (T : H →L[F] H) (s : Set ℕ)
    (z y : s → H) (a : s → F) : Prop :=
  (∀ k, ‖z k‖ = 1 ∧ ‖y k‖ = 1) ∧ Summable (fun k => ‖a k‖) ∧
    ∀ x : H, HasSum (fun k => (a k * inner F (z k) x) • y k) (T x)

/-- PDF p.18: all unit-expansion costs, with no artificial upper bound. -/
def unitExpansionCosts (T : H →L[F] H) : Set ℝ :=
  {r | ∃ (s : Set ℕ) (z y : s → H) (a : s → F),
    UnitNuclearRepresentation T s z y a ∧ r = ∑' k, ‖a k‖}

example : UnitNuclearRepresentation (0 : H →L[F] H) (∅ : Set ℕ)
    (fun _ => 0) (fun _ => 0) (fun _ => 0) := by
  constructor
  · intro k
    exact (Set.notMem_empty k.val k.property).elim
  constructor
  · simp
  · intro x
    simpa using (hasSum_zero : HasSum (fun _ : (∅ : Set ℕ) => (0 : H)) 0)

end Hilbert

end QAlgorithms.Papers.Independent.Next46.P02


