-- Prove2me | Definitions.Def_threeStarCyclicProduct
-- name    : threeStarCyclicProduct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-25T04:32:05.889328+00:00
-- url     : https://prove2.me/theorems/64fe489e-e678-4f52-835c-1a80c41bce4f
-- title:
--   The heterogeneous cyclic product of three tensors
-- statement:
--   For three order-three tensors $X,Y,Z$, their heterogeneous cyclic product is
--
--   $$
--   X\otimes\pi(Y)\otimes\pi^2(Z),
--   $$
--
--   where $\pi$ cyclically permutes the three tensor modes.  When $X=Y=Z$, this is the usual cyclic symmetrization.  Allowing three distinct inputs is necessary when a modewise direct sum is cyclically symmetrized: its outer blocks are indexed by all ordered triples of summands, not only the diagonal triples.
-- source:
--   The cyclic symmetrization used in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal p. 264; heterogeneous triples arise from distributing it over the disjoint C-tensors on journal p. 271; https://doi.org/10.1016/S0747-7171(08)80013-2.

import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_permutation

universe u

namespace MME

noncomputable def threeStarCyclicProduct
    {K : Type u} [Field K]
    (X Y Z : TensorObj K 3) : TensorObj K 3 :=
  TensorObj.kron X
    (TensorObj.kron
      (TensorObj.permObj cyclicPerm Y)
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) Z))

end MME


