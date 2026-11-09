-- Prove2me | Definitions.Def_DetSupportRank_DeterminantSupport_FreeResolutions
-- name    : DetSupportRank_DeterminantSupport_FreeResolutions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:46.862278+00:00
-- url     : https://prove2.me/theorems/1dc62a58-0afe-46a4-a583-642fb862fb5f
-- title:
--   Finite graded free resolutions
-- statement:
--   A finite graded free resolution is actual data
--   $$0\longrightarrow F_\ell\longrightarrow\cdots\longrightarrow F_0\longrightarrow M\longrightarrow0,$$
--   with finite free terms, integer basis shifts, degree-preserving linear maps, surjective augmentation, and image equal to kernel at every place. Terms beyond $\ell$ have rank zero, which includes exactness at the left endpoint.
--
--   This defines what it means to be a resolution. It does not assume that a module possesses one: existence with $\ell\le m$ is Theorem 5.9.
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Theorem 5.9 and §5.3, pp.18–19, p. 18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_GradedModules

noncomputable section
open scoped BigOperators
universe uDSFreeResolutions

namespace DetSupportRank.DeterminantSupport

/-- An actual finite graded free resolution. Exactness belongs to the definition of a resolution,
not to admissibility of the module. Ranks beyond `length` are zero, so exactness includes the left endpoint. -/
structure FiniteGradedResolution {K : Type uDSFreeResolutions} [Field K] {V D : Type}
    (p : V → D → ℤ) (M : GradedModuleData K V D) where
  length : ℕ
  rank : ℕ → ℕ
  vanishes : ∀ i, length < i → rank i = 0
  shift : (i : ℕ) → Fin (rank i) → D → ℤ
  differential : (i : ℕ) →
    (Fin (rank (i + 1)) → MvPolynomial V K) →ₗ[MvPolynomial V K]
      (Fin (rank i) → MvPolynomial V K)
  augmentation : (Fin (rank 0) → MvPolynomial V K) →ₗ[MvPolynomial V K] M.Carrier
  aug_surjective : Function.Surjective augmentation
  exact_aug : LinearMap.range (differential 0) = LinearMap.ker augmentation
  exact_differential : ∀ i, LinearMap.range (differential (i + 1)) =
    LinearMap.ker (differential i)
  differential_graded : ∀ i, PreservesDegrees
    (freeModuleData p (shift (i + 1))) (freeModuleData p (shift i)) (differential i)
  augmentation_graded : PreservesDegrees (freeModuleData p (shift 0)) M augmentation

end DetSupportRank.DeterminantSupport


