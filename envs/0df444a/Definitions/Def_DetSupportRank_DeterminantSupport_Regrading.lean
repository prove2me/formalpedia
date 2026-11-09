-- Prove2me | Definitions.Def_DetSupportRank_DeterminantSupport_Regrading
-- name    : DetSupportRank_DeterminantSupport_Regrading
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:22:23.818824+00:00
-- url     : https://prove2.me/theorems/d60f568c-7514-4e85-b5b3-c8520ab7250a
-- title:
--   Regrading, exact sequences, and arbitrary free resolutions
-- statement:
--   The combined degree of a pair $(u,w)$ under integers $a,b$ is $au+bw$. Regrading takes the sum of all old pieces with the same new degree:
--   $$M'_v=\sum_{au+bw=v}M_{u,w}.$$
--   Finite exact sequences carry actual terms, maps, exactness, degree preservation and zero endpoints. Arbitrary free resolutions may have infinitely many nonzero terms and free modules of arbitrary rank. Exact specialization asserts image-kernel equalities for the actual induced maps and the zero specialized terminal module.
--
--   These constructions encode the hypotheses and conclusions of the source's homological statements without assuming that a generally nonflat evaluation functor is exact.
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Observation 5.12, p.19; Fact 5.7, p.18; Lemma 5.26, p.25, p. 19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_Specialization

noncomputable section
open scoped BigOperators
universe uDSRegrade

namespace DetSupportRank.DeterminantSupport

/-- Linear combination of a pair of integer multidegrees. -/
def combineDegrees {D : Type} (a b : ℤ) (u : (D ⊕ D) → ℤ) : D → ℤ :=
  fun i => a * u (Sum.inl i) + b * u (Sum.inr i)

/-- Regrading groups homogeneous pieces by the specified degree map. -/
def regradedModuleData {K : Type uDSRegrade} [Field K] {V D E : Type}
    (L : (D → ℤ) → E → ℤ) (M : GradedModuleData K V D) : GradedModuleData K V E where
  Carrier := M.Carrier
  piece v := Submodule.span K {x | ∃ u, L u = v ∧ x ∈ M.piece u}

/-- A finite exact sequence with endpoints zero, extended by zero beyond its length.
All the modules, maps and exactness conditions are explicit. -/
structure FiniteExactSequence {K : Type uDSRegrade} [Field K] {V D : Type}
    (p : V → D → ℤ) where
  length : ℕ
  term : ℕ → GradedModuleData K V D
  beyond : ∀ i, length < i → Subsingleton (term i).Carrier
  finite : ∀ i, Module.Finite (MvPolynomial V K) (term i).Carrier
  graded : ∀ i, IsGraded p (term i)
  differential : ∀ i, (term i).Carrier →ₗ[MvPolynomial V K] (term (i + 1)).Carrier
  preserves : ∀ i, PreservesDegrees (term i) (term (i + 1)) (differential i)
  first_injective : Function.Injective (differential 0)
  exact : ∀ i, LinearMap.range (differential i) = LinearMap.ker (differential (i + 1))

/-- An arbitrary free resolution, with no finiteness, termination or grading restriction.
Candidate piece data on its terms do not impose a grading; Lemma 5.26 ignores them. -/
structure FreeResolutionData {K : Type uDSRegrade} [Field K] {V D : Type}
    (B : GradedModuleData K V D) where
  term : ℕ → GradedModuleData K V D
  free : ∀ i, Module.Free (MvPolynomial V K) (term i).Carrier
  differential : ∀ i, (term (i + 1)).Carrier →ₗ[MvPolynomial V K] (term i).Carrier
  augmentation : (term 0).Carrier →ₗ[MvPolynomial V K] B.Carrier
  surjective : Function.Surjective augmentation
  exact_aug : LinearMap.range (differential 0) = LinearMap.ker augmentation
  exact : ∀ i, LinearMap.range (differential (i + 1)) = LinearMap.ker (differential i)

/-- Every specialized map is the induced evaluation map, and B(c) is zero at the points
in Lemma 5.26. The remaining equalities express exactness at every free term. -/
def ExactSpecialization {K : Type uDSRegrade} [Field K] {V D : Type}
    {B : GradedModuleData K V D} (R : FreeResolutionData B) (c : V → K) : Prop :=
  Subsingleton (specializedSpace B c) ∧
  LinearMap.range (specializeLinearMap (R.term 1) (R.term 0) c (R.differential 0)) =
    LinearMap.ker (specializeLinearMap (R.term 0) B c R.augmentation) ∧
  Function.Surjective (specializeLinearMap (R.term 0) B c R.augmentation) ∧
  ∀ i, LinearMap.range (specializeLinearMap (R.term (i + 2)) (R.term (i + 1)) c
      (R.differential (i + 1))) =
    LinearMap.ker (specializeLinearMap (R.term (i + 1)) (R.term i) c (R.differential i))

end DetSupportRank.DeterminantSupport


