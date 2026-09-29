-- Prove2me | Definitions.Def_WassersteinDRO_Shrinkage_affineEstimator
-- name    : WassersteinDRO_Shrinkage_affineEstimator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:48:45.259971+00:00
-- url     : https://prove2.me/theorems/e8ec9a55-2a1f-45f8-adf6-14e5968a176d
-- title:
--   Affine estimator built from a block matrix
-- statement:
--   Given a block $S_{xy}, S_{yy}$ and nominal means $\hat\mu_x,\hat\mu_y$, the affine estimator
--   is $\psi(y) = S_{xy}(S_{yy})^{-1}(y-\hat\mu_y)+\hat\mu_x$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, p. 29, formula following Theorem 25's SDP (36)

import Mathlib

namespace WassersteinDRO.Shrinkage

/-- The affine estimator `ψ⋆(y) = S_xy(S_yy)⁻¹(y-µ̂_y) + µ̂_x`, Kuhn et al. 2019, p. 29,
built from a block `S = [[S_xx,S_xy],[S_yx,S_yy]]` and the nominal mean's blocks `µ̂_x,µ̂_y`. -/
noncomputable def affineEstimator {mx my : ℕ}
    (Sxy : Matrix (Fin mx) (Fin my) ℝ) (Syy : Matrix (Fin my) (Fin my) ℝ)
    (muHatX : EuclideanSpace ℝ (Fin mx)) (muHatY : EuclideanSpace ℝ (Fin my)) :
    EuclideanSpace ℝ (Fin my) → EuclideanSpace ℝ (Fin mx) :=
  fun y => (EuclideanSpace.equiv (Fin mx) ℝ).symm
    (Sxy.mulVec (Syy⁻¹.mulVec (EuclideanSpace.equiv (Fin my) ℝ (y - muHatY)))) + muHatX

end WassersteinDRO.Shrinkage


