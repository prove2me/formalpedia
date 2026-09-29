-- Prove2me | Definitions.Def_mme_perm_kronPow_mode_equiv
-- name    : mme_perm_kronPow_mode_equiv
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-27T12:41:47.320256+00:00
-- url     : https://prove2.me/theorems/523f5c25-76d7-4982-a43b-c9a5e23db637
-- title:
--   Mode equivalence for powers of a permuted tensor
-- statement:
--   For an order-three tensor $T$, a permutation $e$ of its modes, and an exponent $n$, each mode of $(eT)^{\otimes n}$ is canonically linearly equivalent to the $e^{-1}$-indexed mode of $T^{\otimes n}$. The equivalence is obtained recursively from the identity in degree zero and tensor products of the factorwise identity maps.
--
--   This is the mode-space interface needed to transport tensor maps, product bases, and projector restrictions through cyclic permutations without replacing exact maps by an opaque tensor isomorphism.
-- source:
--   Standard functoriality of tensor powers under mode reindexing; formalization infrastructure for the q=6 Coppersmith-Winograd 121/211 rows.

import Definitions.Def_mme_permutation

open MME

universe u

set_option autoImplicit false

namespace MME.TensorObj

noncomputable def permKronPowModeEquiv
    {K : Type u} [Field K] (e : Equiv.Perm (Fin 3))
    (T : TensorObj K 3) (i : Fin 3) :
    (n : ℕ) → ((TensorObj.permObj e T).kronPow n).V i ≃ₗ[K]
      (T.kronPow n).V (e.symm i)
  | 0 => LinearEquiv.refl K K
  | n + 1 => TensorProduct.congr
      (LinearEquiv.refl K (T.V (e.symm i)))
      (permKronPowModeEquiv e T i n)

end MME.TensorObj


