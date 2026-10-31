-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P60
-- name    : QAlgorithms_Papers_Independent_Intake100_P60
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T14:06:44.225372+00:00
-- url     : https://prove2.me/theorems/ffc3ffe7-c3e7-43fa-a988-df3d49e97107
-- title:
--   Definitions for Trace class groups
-- statement:
--   The objects the formalized statements of *Trace class groups* (arXiv:1501.02375) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ContinuousUnitaryRepresentation`: Introduction and Definition 1.3, PDF pp.2,4: a strongly continuous unitary representation on a complete complex Hilbert space. Strong continuity is tested on each vector, with no operator-norm continuity or separability requirement.
--   - `IsUnitaryInvariantSubspace`: Introduction, PDF p.2: invariance of an actual complex linear subspace.
--   - `IsTopologicallyIrreducible`: PDF pp.2,5 and Definition 3.1, p.12: nonzero unitary representation with no proper nonzero closed invariant subspace. Algebraically invariant subspaces need not be closed, so the closedness condition is explicit.
--   - `trivialRepresentation`: The trivial unitary action, allowed among the representations of PDF pp.2,5.
--   - `discreteIntegrated`: Example 1.5, PDF p.5: with counting Haar measure the Bruhat test functions of a discrete group are precisely finitely supported complex functions, and the integrated operator is the indicated finite sum of bounded operators. This construction has no totalized infinite integral and works for uncountable groups.
--   - `DiscreteTraceClass`: Definition 1.3 and Example 1.5, PDF pp.4--5, specialized to discrete groups: every actual test-function operator is trace class. Counting Haar measure is fixed.
-- source:
--   Trace class groups, arXiv:1501.02375v5, https://arxiv.org/abs/1501.02375v5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13

/-!
Faithful statement draft for Deitmar--van Dijk, arXiv:1501.02375v5.
Only the discrete representation example and the three finite representation type
examples are stated here. Every other planned node is explicitly deferred in
HARD.md and GAPS.json; none is replaced by a weaker claim.

The accepted nuclear operator predicate in Dependency50.P13 is reused on arbitrary
complete complex Hilbert spaces, including nonseparable ones. Local definitions
below implement only this paper's representation and discrete integration notions.
Counting Haar measure is fixed for the discrete example; positive rescaling does
not change trace-class membership. No irreducibility is imposed in that example.
Compilation is pending the separate mechanical handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P60

universe u v

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass)

/-- Introduction and Definition 1.3, PDF pp.2,4: a strongly continuous unitary
representation on a complete complex Hilbert space. Strong continuity is tested
on each vector, with no operator-norm continuity or separability requirement. -/
structure ContinuousUnitaryRepresentation
    (G : Type u) [Group G] [TopologicalSpace G]
    (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  hom : G →* (H ≃ₗᵢ[ℂ] H)
  continuous_orbit : ∀ v : H, Continuous (fun g : G => hom g v)

section RepresentationDefinitions

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Introduction, PDF p.2: invariance of an actual complex linear subspace. -/
def IsUnitaryInvariantSubspace (pi : ContinuousUnitaryRepresentation G H) (V : Submodule ℂ H) : Prop :=
  ∀ (g : G) (v : H), v ∈ V → pi.hom g v ∈ V

/-- PDF pp.2,5 and Definition 3.1, p.12: nonzero unitary representation with no
proper nonzero closed invariant subspace. Algebraically invariant subspaces need
not be closed, so the closedness condition is explicit. -/
def IsTopologicallyIrreducible (pi : ContinuousUnitaryRepresentation G H) : Prop :=
  Nontrivial H ∧ ∀ V : Submodule ℂ H,
    IsClosed (V : Set H) → IsUnitaryInvariantSubspace pi V → V = ⊥ ∨ V = ⊤

/-- The trivial unitary action, allowed among the representations of PDF pp.2,5. -/
def trivialRepresentation : ContinuousUnitaryRepresentation G H where
  hom := 1
  continuous_orbit := fun _ => continuous_const

/-- Sanity: every vector is fixed in the trivial representation. -/
example (g : G) (v : H) :
    (trivialRepresentation : ContinuousUnitaryRepresentation G H).hom g v = v := by
  rfl

/-- Sanity: the whole Hilbert space is invariant for every representation. -/
example (pi : ContinuousUnitaryRepresentation G H) : IsUnitaryInvariantSubspace pi ⊤ := by
  simp [IsUnitaryInvariantSubspace]

/-- Example 1.5, PDF p.5: with counting Haar measure the Bruhat test functions
of a discrete group are precisely finitely supported complex functions, and the
integrated operator is the indicated finite sum of bounded operators. This
construction has no totalized infinite integral and works for uncountable groups. -/
def discreteIntegrated (pi : ContinuousUnitaryRepresentation G H) (f : G →₀ ℂ) :
    H →L[ℂ] H :=
  f.sum (fun g c => c • (pi.hom g).toContinuousLinearEquiv.toContinuousLinearMap)

/-- Definition 1.3 and Example 1.5, PDF pp.4--5, specialized to discrete groups:
every actual test-function operator is trace class. Counting Haar measure is fixed. -/
def DiscreteTraceClass (pi : ContinuousUnitaryRepresentation G H) : Prop :=
  ∀ f : G →₀ ℂ, IsTraceClass (discreteIntegrated pi f)

/-- Sanity: the zero test function gives the zero operator. -/
example (pi : ContinuousUnitaryRepresentation G H) :
    discreteIntegrated pi (0 : G →₀ ℂ) = 0 := by
  simp [discreteIntegrated]

/-- Sanity: the identity atom in the source proof gives the identity operator. -/
example (pi : ContinuousUnitaryRepresentation G H) :
    discreteIntegrated pi (Finsupp.single (1 : G) (1 : ℂ)) =
      ContinuousLinearMap.id ℂ H := by
  classical
  simp [discreteIntegrated, ContinuousLinearMap.one_def]

end RepresentationDefinitions

end QAlgorithms.Papers.Independent.Intake100.P60


