-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P18
-- name    : QAlgorithms_Papers_Independent_Frontier18_P18
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T09:06:36.559983+00:00
-- url     : https://prove2.me/theorems/cd79764a-cac8-4422-89e1-953d326f2ad8
-- title:
--   Definitions for Monotonicity of the Holevo quantity: a necessary condition for equality in terms of a channel and its applications
-- statement:
--   The objects the formalized statements of *Monotonicity of the Holevo quantity: a necessary condition for equality in terms of a channel and its applications* (arXiv:1106.3297) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `operatorCoeff`: Bounded-operator coefficients in the canonical orthonormal coordinates, §2, PDF pp.3–4. The ket indexed by j is lp.single 2 j 1.
--   - `boundedOperator`: The bounded realization of a trace-class coefficient array, §2, PDF p.3. A nuclear expansion gives existence and uniqueness on the trace-class domain. For an array with no bounded realization this total extension is explicitly zero; all source results use it only on trace-class arrays.
--   - `conjugateCoeff`: The coefficients of W X W*, §2, PDF p.4, on the whole trace class. Composition uses actual bounded operators, rather than a formal matrix product with an unspecified convergence convention.
--   - `ReversibleOn`: One recovery channel works for every member of S: Definition 3, PDF p.6. No countability, totality or nonemptiness is imposed on S.
--   - `IsometricallyEquivalent`: Isometric equivalence (3), PDF pp.3–4: one partial isometry satisfies both intertwining equations on every trace-class input. The output spaces may differ.
--   - `IsParsevalFrame`: Parseval overcompleteness, PDF pp.5,9: the sum of the rank-one projections converges strongly to the identity. The vectors need not be unit or orthogonal.
--   - `IsKrausRepresentation`: Countable Kraus representation (7), PDF p.4. The normalization sum is strong; the operator-series output converges in trace norm on every trace-class input. Finite Kraus families are included by choosing a finite index type.
--   - `frameKrausTransform`: The computed frame transformation in Lemma 2, PDF p.9. The theorem below asserts operator-norm summability; it is not assumed in this definition.
--   - `stateSquareRoot`: Positive square root of a density operator, PDF pp.19,21–22. The complex continuous functional calculus applies z ↦ sqrt(Re z) to the bounded realization. A state's spectrum is nonnegative real, so this is exactly its positive square root, including at zero; no inverse or spectral gap is required.
--   - `hilbertSchmidtSizeSq`: Squared Hilbert–Schmidt size, PDF pp.21–22. Infinite size is represented by infinity, not by the default value of an unsummable real tsum. Tending to zero in this squared size is equivalent to convergence in Hilbert–Schmidt norm.
--   - `WeakOperatorConverges`: Weak operator convergence, Lemma 3, PDF p.21. Both test vectors are arbitrary; this imposes no self-adjointness or positivity on the operators.
-- source:
--   Monotonicity of the Holevo quantity: a necessary condition for equality in terms of a channel and its applications, arXiv:1106.3297v6, https://arxiv.org/abs/1106.3297v6

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

/-!
# Shirokov: monotonicity of the Holevo quantity

Source: arXiv:1106.3297v6. This draft covers Lemmas 1, 2 and 3.
Other nodes and missing analytic interfaces are recorded in HARD.md and GAPS.json.
The explicitly pinned accepted P33 interfaces supply trace-class states and channels;
no other paper's definitions are modified or consolidated into this paper.
-/

noncomputable section

open Filter
open scoped BigOperators ENNReal

attribute [local instance] Classical.propDecidable

-- Use the complex unital C-star calculus directly on bounded operators.
attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Frontier18.P18

open QAlgorithms.RealRegisters (Hilbert)

/-- Bounded-operator coefficients in the canonical orthonormal coordinates,
§2, PDF pp.3–4. The ket indexed by j is lp.single 2 j 1. -/
def operatorCoeff {I J : Type} (A : Hilbert I →L[ℂ] Hilbert J) : Matrix J I ℂ := by
  classical
  exact fun i j => (A (lp.single 2 j 1)) i

/-- The bounded realization of a trace-class coefficient array, §2, PDF p.3.
A nuclear expansion gives existence and uniqueness on the trace-class domain.
For an array with no bounded realization this total extension is explicitly zero;
all source results use it only on trace-class arrays. -/
def boundedOperator {I : Type} (X : Matrix I I ℂ) : Hilbert I →L[ℂ] Hilbert I := by
  classical
  exact if h : ∃ A : Hilbert I →L[ℂ] Hilbert I, operatorCoeff A = X then h.choose else 0

/-- The coefficients of W X W*, §2, PDF p.4, on the whole trace class.
Composition uses actual bounded operators, rather than a formal matrix product
with an unspecified convergence convention. -/
def conjugateCoeff {I J : Type} (W : Hilbert I →L[ℂ] Hilbert J)
    (X : Matrix I I ℂ) : Matrix J J ℂ :=
  operatorCoeff (W.comp ((boundedOperator X).comp (ContinuousLinearMap.adjoint W)))

/-- One recovery channel works for every member of S: Definition 3, PDF p.6.
No countability, totality or nonemptiness is imposed on S. -/
def ReversibleOn {I J : Type}
    (Phi : Matrix I I ℂ → Matrix J J ℂ) (S : Set (QAlgorithms.Papers.Independent.Dependency50.P33.State I)) : Prop :=
  ∃ Psi : Matrix J J ℂ → Matrix I I ℂ,
    QAlgorithms.Papers.Independent.Dependency50.P33.IsTraceClassChannel Psi ∧
    ∀ rho ∈ S, Psi (Phi rho.coefficients) = rho.coefficients

/-- Isometric equivalence (3), PDF pp.3–4: one partial isometry satisfies both
intertwining equations on every trace-class input. The output spaces may differ. -/
def IsometricallyEquivalent {I J K : Type}
    (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (PhiPrime : Matrix I I ℂ → Matrix K K ℂ) : Prop :=
  ∃ W : Hilbert J →L[ℂ] Hilbert K,
    W.comp ((ContinuousLinearMap.adjoint W).comp W) = W ∧
    ∀ X, QAlgorithms.Papers.Independent.Dependency50.P33.IsTraceClass X →
      PhiPrime X = conjugateCoeff W (Phi X) ∧
      Phi X = conjugateCoeff (ContinuousLinearMap.adjoint W) (PhiPrime X)

/-- Parseval overcompleteness, PDF pp.5,9: the sum of the rank-one projections
converges strongly to the identity. The vectors need not be unit or orthogonal. -/
def IsParsevalFrame {I L : Type} (psi : L → Hilbert I) : Prop :=
  ∀ x : Hilbert I, HasSum (fun i => (inner ℂ (psi i) x) • psi i) x

/-- Countable Kraus representation (7), PDF p.4. The normalization sum is strong;
the operator-series output converges in trace norm on every trace-class input.
Finite Kraus families are included by choosing a finite index type. -/
def IsKrausRepresentation {I J K : Type}
    (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (V : K → (Hilbert I →L[ℂ] Hilbert J)) : Prop :=
  (∀ x : Hilbert I,
    HasSum (fun k => ((ContinuousLinearMap.adjoint (V k)).comp (V k)) x) x) ∧
  ∀ X, QAlgorithms.Papers.Independent.Dependency50.P33.IsTraceClass X →
    Tendsto (fun F : Finset K =>
      QAlgorithms.Papers.Independent.Dependency50.P33.traceSize (Phi X - ∑ k ∈ F, conjugateCoeff (V k) X)) atTop (nhds 0)

/-- The computed frame transformation in Lemma 2, PDF p.9. The theorem below
asserts operator-norm summability; it is not assumed in this definition. -/
def frameKrausTransform {I J K L : Type}
    (V : K → (Hilbert I →L[ℂ] Hilbert J)) (psi : L → Hilbert K)
    (i : L) : Hilbert I →L[ℂ] Hilbert J := by
  classical
  exact ∑' k, (inner ℂ (psi i) (lp.single 2 k 1)) • V k

/-- Positive square root of a density operator, PDF pp.19,21–22.
The complex continuous functional calculus applies z ↦ sqrt(Re z) to the bounded
realization. A state's spectrum is nonnegative real, so this is exactly its
positive square root, including at zero; no inverse or spectral gap is required. -/
def stateSquareRoot {I : Type} (rho : QAlgorithms.Papers.Independent.Dependency50.P33.State I) : Hilbert I →L[ℂ] Hilbert I :=
  cfc (fun z : ℂ => (Real.sqrt z.re : ℂ)) (boundedOperator rho.coefficients)

/-- Squared Hilbert–Schmidt size, PDF pp.21–22. Infinite size is represented by
infinity, not by the default value of an unsummable real tsum. Tending to zero
in this squared size is equivalent to convergence in Hilbert–Schmidt norm. -/
def hilbertSchmidtSizeSq {I J : Type} (A : Hilbert I →L[ℂ] Hilbert J) : ℝ≥0∞ :=
  ∑' i, ∑' j, ENNReal.ofReal (‖operatorCoeff A i j‖ ^ 2)

/-- Weak operator convergence, Lemma 3, PDF p.21. Both test vectors are arbitrary;
this imposes no self-adjointness or positivity on the operators. -/
def WeakOperatorConverges {I : Type}
    (A : ℕ → (Hilbert I →L[ℂ] Hilbert I))
    (A0 : Hilbert I →L[ℂ] Hilbert I) : Prop :=
  ∀ x y : Hilbert I,
    Tendsto (fun n => inner ℂ x (A n y)) atTop (nhds (inner ℂ x (A0 y)))

/-! Small sanity checks for the paper-local interfaces. -/

example {I J : Type} (i : J) (j : I) :
    operatorCoeff (0 : Hilbert I →L[ℂ] Hilbert J) i j = 0 := rfl

example {I : Type} (X : Matrix I I ℂ)
    (h : ¬ ∃ A : Hilbert I →L[ℂ] Hilbert I, operatorCoeff A = X) :
    boundedOperator X = 0 := by
  simp [boundedOperator, h]

example {I J : Type} (X : Matrix I I ℂ) :
    conjugateCoeff (0 : Hilbert I →L[ℂ] Hilbert J) X = 0 := by
  ext i j
  simp [conjugateCoeff, operatorCoeff]

example {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ) :
    ReversibleOn Phi ∅ ↔
      ∃ Psi : Matrix J J ℂ → Matrix I I ℂ, QAlgorithms.Papers.Independent.Dependency50.P33.IsTraceClassChannel Psi := by
  simp [ReversibleOn]

example {I L : Type} (psi : L → Hilbert I) (h : IsParsevalFrame psi)
    (x : Hilbert I) : HasSum (fun i => (inner ℂ (psi i) x) • psi i) x := h x

example {I J K : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (V : K → (Hilbert I →L[ℂ] Hilbert J)) (h : IsKrausRepresentation Phi V)
    (x : Hilbert I) :
    HasSum (fun k => ((ContinuousLinearMap.adjoint (V k)).comp (V k)) x) x := h.1 x

example {I J K L : Type} (psi : L → Hilbert K) (i : L) :
    frameKrausTransform (fun _ : K => (0 : Hilbert I →L[ℂ] Hilbert J)) psi i = 0 := by
  simp [frameKrausTransform]

example {I : Type} (rho : QAlgorithms.Papers.Independent.Dependency50.P33.State I) :
    stateSquareRoot rho = cfc (fun z : ℂ => (Real.sqrt z.re : ℂ)) (boundedOperator rho.coefficients) := rfl

example {I J : Type} :
    hilbertSchmidtSizeSq (0 : Hilbert I →L[ℂ] Hilbert J) = 0 := by
  simp [hilbertSchmidtSizeSq, operatorCoeff]

example {I : Type} (A : Hilbert I →L[ℂ] Hilbert I) :
    WeakOperatorConverges (fun _ => A) A := by
  intro x y
  exact tendsto_const_nhds

end QAlgorithms.Papers.Independent.Frontier18.P18


