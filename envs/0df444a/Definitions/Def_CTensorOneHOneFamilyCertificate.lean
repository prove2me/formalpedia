-- Prove2me | Definitions.Def_CTensorOneHOneFamilyCertificate
-- name    : CTensorOneHOneFamilyCertificate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-25T04:29:09.660548+00:00
-- url     : https://prove2.me/theorems/28383bd7-15fa-4ccd-a1ae-5d820bdd39a0
-- title:
--   A modewise-disjoint outer family of finite C-tensors
-- statement:
--   A `CTensorOneHOneFamilyCertificate` records that a source tensor restricts to a modewise direct sum of $A$ finite C-tensors.  Every outer summand is a C-tensor over $\langle1,H,1\rangle$, and every component matrix product in every summand has the same volume $v$.
--
--   Distinct outer summands need not be isomorphic, and the component identifications inside one summand may depend on the component.  The definition therefore retains exactly the information supplied by the first Coppersmith--Winograd hash: outer fibers are genuinely disjoint, while each fiber keeps its shared third-mode coordinates and only a common matrix-product volume is asserted.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal p. 271: the disjoint family of C-tensors over <1,H,1> and the common component volume; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_CTensorOneHOneCertificate

universe u

namespace MME

structure CTensorOneHOneFamilyCertificate
    {K : Type u} [Field K]
    (source : TensorObj K 3) (A H volume : ℕ) where
  star : Fin A → TensorObj K 3
  restrict : TensorObj.Restrict (TensorObj.bigAdd star) source
  certificate : ∀ a : Fin A,
    CTensorOneHOneCertificate (star a) H volume

end MME


