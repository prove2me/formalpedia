-- Prove2me | Definitions.Def_CTensorThreeCyclicBalancedGradingCertificate
-- name    : CTensorThreeCyclicBalancedGradingCertificate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-25T04:41:29.704343+00:00
-- url     : https://prove2.me/theorems/1ff7c3ee-e8e2-40da-baa1-00ddd3e8f66f
-- title:
--   Balanced grading certificate for three heterogeneous C-tensor stars
-- statement:
--   Let $X$, $Y$, and $Z$ be three possibly different C-tensors over $\langle 1,H,1\rangle$ whose matrix-product components all have common volume $v$. This certificate packages the balanced-word grading of the heterogeneous cyclic product $X\otimes\pi(Y)\otimes\pi^2(Z)$ at tensor-power length $R=Hm$. It records the word-pair addresses in the three modes, the induced-support collision rule, a matrix-multiplication isomorphism for every complete address block, and the common block volume $v^{3R}$.
--
--   The interface separates the finite tensor-coordinate construction from the Salem--Spencer counting argument and does not require a fixed component shape or common fine-coordinate trivialization.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), C-tensor argument on journal pp. 271--272.

import Definitions.Def_CTensorOneHOneCertificate
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_threeStarCyclicProduct

open MME

universe u

namespace MME

structure CTensorThreeCyclicBalancedGradingCertificate
    {K : Type u} [Field K]
    (X Y Z : TensorObj K 3) (H volume m W : ℕ) where
  t : ℕ
  grading : (threeStarCyclicProduct X Y Z).TypeGrading t
  address :
    (Fin W × Fin W × Fin W) → Fin 3 → Fin (H * m) → Fin t
  a : (Fin W × Fin W × Fin W) → ℕ
  b : (Fin W × Fin W × Fin W) → ℕ
  c : (Fin W × Fin W × Fin W) → ℕ
  mixed_support :
    ∀ es : Fin 3 → (Fin W × Fin W × Fin W),
      (∀ r : Fin (H * m),
        grading.blockTensor (fun i ↦ address (es i) i r) ≠ 0) →
      (es 1).2.1 = (es 2).2.1 ∧
      (es 2).2.2 = (es 0).2.2 ∧
      (es 0).1 = (es 1).1
  component : ∀ e,
    TensorObj.Isomorphic
      (MMObj K (a e) (b e) (c e))
      (gradedAddressBlock grading (address e))
  common_volume : ∀ e,
    a e * b e * c e = volume ^ (3 * (H * m))

end MME


