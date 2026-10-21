-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P23
-- name    : QAlgorithms_Papers_Independent_Claimed50_P23
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T10:09:03.700584+00:00
-- url     : https://prove2.me/theorems/734f97a3-cc44-46b5-8d64-fa5715c8a081
-- title:
--   Definitions for Integrating representations of Banach--Lie algebras
-- statement:
--   The objects the formalized statements of *Integrating representations of Banach--Lie algebras* (arXiv:1003.0999) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `BanachLieBracket`: PDF pp.1--2: a continuous real bilinear Lie bracket. The ambient real normed space is required to be complete wherever this structure is used.
--   - `onDomain`: PDF pp.2--3: the unbounded operator with exactly the specified domain D. Neither boundedness nor completeness of D is imposed.
--   - `EssentiallySkewAdjoint`: PDF p.2: essential skew-adjointness uses graph closure and equality of the FULL adjoint graph, including its domain. Closability prevents the default closure of a nonclosable partial map from being used.
--   - `UnitaryFlow`: PDF p.2: a strongly continuous unitary one-parameter group on the same H.
--   - `identityFlow`: The trivial one-parameter group; only a fallback outside the Stone domain.
--   - `HasFullGenerator`: PDF p.2: the full infinitesimal generator is determined by existence of the Hilbert-space derivative at zero, on its entire domain.
--   - `stoneFlow`: PDF p.2: Stone's group of the graph closure. Choose the group with exactly that full generator when it exists, and the identity group otherwise. All source statements using this definition assume essential skew-adjointness, or analytic vectors on a dense invariant domain, which imply existence and uniqueness. No bounded-operator exponential is used for an unbounded operator.
--   - `operatorExp`: PDF pp.2--6: e^{tA}, acting on all of H.
--   - `domainValue`: A subtype lift, equal to the supplied vector whenever it belongs to D. The zero fallback is never used in a domain-guarded source formula.
--   - `operatorOrbit`: PDF pp.3--6: the orbit viewed in D, always accompanied by invariance in source statements. The topology on D is the topology induced by H.
--   - `InvariantDomain`: PDF pp.2--3: invariance of the original operator domain for every real time.
--   - `IsAnalyticVector`: PDF pp.3--5: an analytic vector for an operator preserving D. The positive radius is allowed to depend on both the operator and the vector.
--   - `IsStrongRepresentation`: PDF pp.1--2: a strongly continuous skew-symmetric representation on an invariant complex linear domain. Real linearity is in g, complex linearity in D. Density is a separate hypothesis, so larger domains inherit it from containment.
--   - `adjointExp`: PDF p.4: the bounded adjoint exponential on the Banach Lie algebra. Unlike the Hilbert-space operator exponential, this is a bounded-operator exponential.
-- source:
--   Integrating representations of Banach--Lie algebras, arXiv:1003.0999v3, https://arxiv.org/abs/1003.0999v3

import Mathlib

/-!
Statements from S. Merigon, Integrating representations of Banach--Lie algebras,
arXiv:1003.0999v3. All new definitions are local to this paper.
The integration and actual BCH-chart interfaces are explicitly deferred in HARD.md.
-/

noncomputable section

open MeasureTheory
open scoped Interval Classical

namespace QAlgorithms.Papers.Independent.Claimed50.P23

/-- PDF pp.1--2: a continuous real bilinear Lie bracket. The ambient real
normed space is required to be complete wherever this structure is used. -/
structure BanachLieBracket (g : Type*) [NormedAddCommGroup g] [NormedSpace ℝ g] where
  bracket : g →L[ℝ] g →L[ℝ] g
  skew : ∀ x y, bracket x y = -bracket y x
  jacobi : ∀ x y z,
    bracket x (bracket y z) + bracket y (bracket z x) + bracket z (bracket x y) = 0

/-- The abelian bracket is admitted on every real Banach space, including zero. -/
example (g : Type*) [NormedAddCommGroup g] [NormedSpace ℝ g] :
    Nonempty (BanachLieBracket g) := by
  exact ⟨⟨0, by simp, by simp⟩⟩

section Operators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF pp.2--3: the unbounded operator with exactly the specified domain D.
Neither boundedness nor completeness of D is imposed. -/
def onDomain (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) : H →ₗ.[ℂ] H where
  domain := D
  toFun := A

/-- The unbounded operator retains its exact, possibly nonclosed, domain. -/
example (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) : (onDomain D A).domain = D := rfl

/-- PDF p.2: essential skew-adjointness uses graph closure and equality of the
FULL adjoint graph, including its domain. Closability prevents the default closure
of a nonclosable partial map from being used. -/
def EssentiallySkewAdjoint (A : H →ₗ.[ℂ] H) : Prop :=
  A.IsClosable ∧ ∀ v w : H,
    (v, w) ∈ A.closure.graph ↔ (v, -w) ∈ A.closure.adjoint.graph

/-- PDF p.2: a strongly continuous unitary one-parameter group on the same H. -/
structure UnitaryFlow (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  action : ℝ → H ≃ₗᵢ[ℂ] H
  at_zero : ∀ v, action 0 v = v
  add_time : ∀ s t v, action (s + t) v = action s (action t v)
  strong_continuous : ∀ v, Continuous (fun t => action t v)

/-- The trivial one-parameter group; only a fallback outside the Stone domain. -/
def identityFlow : UnitaryFlow H where
  action := fun _ => LinearIsometryEquiv.refl ℂ H
  at_zero := fun _ => rfl
  add_time := fun _ _ _ => rfl
  strong_continuous := fun _ => continuous_const

/-- PDF p.2: the full infinitesimal generator is determined by existence of the
Hilbert-space derivative at zero, on its entire domain. -/
def HasFullGenerator (U : UnitaryFlow H) (A : H →ₗ.[ℂ] H) : Prop :=
  ∀ v w : H, HasDerivAt (fun t : ℝ => U.action t v) w 0 ↔ (v, w) ∈ A.graph

/-- PDF p.2: Stone's group of the graph closure. Choose the group with exactly
that full generator when it exists, and the identity group otherwise. All source
statements using this definition assume essential skew-adjointness, or analytic
vectors on a dense invariant domain, which imply existence and uniqueness. No
bounded-operator exponential is used for an unbounded operator. -/
def stoneFlow (A : H →ₗ.[ℂ] H) : UnitaryFlow H :=
  if h : ∃ U : UnitaryFlow H, HasFullGenerator U A.closure then h.choose
  else identityFlow

/-- The choice is tied to the full generator whenever such a group exists. -/
example (A : H →ₗ.[ℂ] H)
    (h : ∃ U : UnitaryFlow H, HasFullGenerator U A.closure) :
    HasFullGenerator (stoneFlow A) A.closure := by
  simpa only [stoneFlow, dif_pos h] using h.choose_spec

/-- PDF pp.2--6: e^{tA}, acting on all of H. -/
def operatorExp (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) (t : ℝ) (v : H) : H :=
  (stoneFlow (onDomain D A)).action t v

/-- A subtype lift, equal to the supplied vector whenever it belongs to D.
The zero fallback is never used in a domain-guarded source formula. -/
def domainValue (D : Submodule ℂ H) (v : H) : D :=
  if h : v ∈ D then ⟨v, h⟩ else 0

/-- Subtype lifting does not alter a vector already in D. -/
example (D : Submodule ℂ H) (v : D) : domainValue D (v : H) = v := by
  simp [domainValue, v.property]

/-- PDF pp.3--6: the orbit viewed in D, always accompanied by invariance in
source statements. The topology on D is the topology induced by H. -/
def operatorOrbit (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) (t : ℝ) (v : D) : D :=
  domainValue D (operatorExp D A t (v : H))

/-- PDF pp.2--3: invariance of the original operator domain for every real time. -/
def InvariantDomain (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) : Prop :=
  ∀ (t : ℝ) (v : D), operatorExp D A t (v : H) ∈ D

/-- Invariance makes the subtype orbit exactly the original Hilbert-space orbit. -/
example (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) (hInvariant : InvariantDomain D A)
    (t : ℝ) (v : D) :
    (operatorOrbit D A t v : H) = operatorExp D A t (v : H) := by
  simp only [operatorOrbit, domainValue, dif_pos (hInvariant t v)]

/-- PDF pp.3--5: an analytic vector for an operator preserving D. The positive
radius is allowed to depend on both the operator and the vector. -/
def IsAnalyticVector (D : Submodule ℂ H) (A : D →ₗ[ℂ] D) (v : D) : Prop :=
  ∃ r : ℝ, 0 < r ∧
    Summable (fun n : ℕ => (r ^ n / (n.factorial : ℝ)) * ‖((A ^ n) v : H)‖)

/-- Zero belongs to the domain of the original operator, without a nonzero-vector
assumption anywhere in the paper. -/
example (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) :
    (onDomain D A) ⟨0, D.zero_mem⟩ = 0 := by
  exact A.map_zero

end Operators

section HilbertStatements

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {g : Type*} [NormedAddCommGroup g] [NormedSpace ℝ g] [CompleteSpace g]

/-- PDF pp.1--2: a strongly continuous skew-symmetric representation on an
invariant complex linear domain. Real linearity is in g, complex linearity in D.
Density is a separate hypothesis, so larger domains inherit it from containment. -/
structure IsStrongRepresentation (L : BanachLieBracket g) (D : Submodule ℂ H)
    (alpha : g → D →ₗ[ℂ] D) : Prop where
  add_lie : ∀ x y v, alpha (x + y) v = alpha x v + alpha y v
  smul_lie : ∀ (r : ℝ) x v, alpha (r • x) v = r • alpha x v
  bracket_lie : ∀ x y v,
    alpha (L.bracket x y) v = alpha x (alpha y v) - alpha y (alpha x v)
  skew : ∀ x (v w : D),
    inner ℂ (alpha x v : H) (w : H) = -inner ℂ (v : H) (alpha x w : H)
  strong_continuous : ∀ v : D, Continuous (fun x : g => (alpha x v : H))

/-- The zero representation is admitted, including on the zero Hilbert space. -/
example (L : BanachLieBracket g) (D : Submodule ℂ H) :
    IsStrongRepresentation L D (fun _ => 0) := by
  constructor
  · intros; simp
  · intros; simp
  · intros; simp
  · intros; simp
  · intro v
    change Continuous (fun _ : g => (0 : H))
    exact continuous_const

/-- PDF p.4: the bounded adjoint exponential on the Banach Lie algebra. Unlike
the Hilbert-space operator exponential, this is a bounded-operator exponential. -/
def adjointExp (L : BanachLieBracket g) (t : ℝ) (x y : g) : g :=
  (NormedSpace.exp (t • L.bracket x)) y

/-- The adjoint exponential at time zero has positive identity normalization. -/
example (L : BanachLieBracket g) (x y : g) : adjointExp L 0 x y = y := by
  simp [adjointExp]

end HilbertStatements

end QAlgorithms.Papers.Independent.Claimed50.P23


