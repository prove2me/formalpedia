-- Prove2me | Definitions.Def_mme_CW_2376_address_block
-- name    : mme_CW_2376_address_block
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-24T17:31:32.177589+00:00
-- url     : https://prove2.me/theorems/0a6c15a2-b243-4379-b9fb-1de48fb850e0
-- title:
--   Tensor block attached to an exact CW profile address
-- statement:
--   For a finite family of tensor objects, `kronFin` is their ordered Kronecker product, with the empty product equal to the tensor unit.
--
--   Given the five-grade certificate for $T_6\otimes T_6$ and an exact-profile address $a$, its address block is the ordered product of the graded constituent selected at every coordinate:
--
--   $$
--   B(a)=\bigotimes_{j<3{,}000{,}000m}(T_6\otimes T_6)_{(a_0(j),a_1(j),a_2(j))}.
--   $$
--
--   Retaining the coordinate order makes this object directly compatible with variable zeroing in the source power. A later exact-multiplicity theorem may reorder its factors up to tensor isomorphism and identify it with the common CW profile core.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), tensor-square constituents (11) and exact type sequences (12)--(13), journal pp. 265--269; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_2376_profile_address
import Definitions.Def_mme_block_subtensor

namespace MME

universe u

namespace TensorObj

noncomputable def kronFin {K : Type u} [Field K] {d : ℕ} :
    (n : ℕ) → (Fin n → TensorObj K d) → TensorObj K d
  | 0, _ => TensorObj.oneObj
  | n + 1, f =>
      TensorObj.kron (f 0)
        (kronFin n (fun i => f i.succ))

end TensorObj

noncomputable def cw2376ExactAddressBlock
    {K : Type u} [Field K]
    (cert : CWSquareFiveGradeCertificate K 6)
    {m : ℕ} (a : CW2376ExactProfileAddress m) : TensorObj K 3 :=
  TensorObj.kronFin (cw2376ProfileLength m)
    (fun j => cert.grading.blockSubtensor
      (cw2376AddressType a.1 j))

end MME


