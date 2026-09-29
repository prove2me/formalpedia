-- Prove2me | Definitions.Def_mme_induced_word_zeroing
-- name    : mme_induced_word_zeroing
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-24T18:38:10.230513+00:00
-- url     : https://prove2.me/theorems/307dc65d-a05d-4684-8c90-4b0867294f3d
-- title:
--   Graded word blocks and coordinate-zeroing maps
-- statement:
--   Let $T$ be an order-three tensor with a finite type grading. An address of length $N$ assigns one grading class to every tensor mode at every coordinate. This definition package constructs: (1) the ordered Kronecker product of the corresponding coordinate blocks, (2) the modewise projection from $T^{\otimes N}$ onto that address block, and (3) the canonical inclusion of one tensor into a finite direct sum.
--
--   These are the tensor-algebra maps used to formalize the laser method's induced-matching zeroing step. They contain no numerical CW parameters and can be reused for later tensor powers and refined laser constructions.
--
--   **Formalization Note** The ordered product uses `TensorObj.kronFin`; the address projection recursively tensors the original grading projections.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), type decomposition and variable zeroing on journal pp. 265 and 267--269; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_tensor_quotient

/-!
# Generic word blocks and zeroing maps for graded tensor powers

These definitions package the tensor-algebra objects used by the induced
matching step of the laser method.  They are independent of the CW numerical
profile.
-/

namespace MME

universe u

variable {K : Type u} [Field K]

/-- The ordered tensor block attached to a word of grading triples. -/
noncomputable def gradedAddressBlock
    {T : TensorObj K 3} {t N : ℕ}
    (G : T.TypeGrading t) (a : Fin 3 → Fin N → Fin t) : TensorObj K 3 :=
  TensorObj.kronFin N
    (fun j => G.blockSubtensor (fun i => a i j))

/-- Project every tensor-power coordinate to the grading class prescribed by
one address. -/
noncomputable def gradedAddressProj
    {T : TensorObj K 3} {t : ℕ} (G : T.TypeGrading t) :
    (N : ℕ) → (a : Fin 3 → Fin N → Fin t) →
      (i : Fin 3) →
      (T.kronPow N).V i →ₗ[K] (gradedAddressBlock G a).V i
  | 0, _, _ => LinearMap.id
  | N + 1, a, i =>
      TensorProduct.map
        (G.blockProj i (a i 0))
        (gradedAddressProj G N (fun i j => a i j.succ) i)

/-- Inclusion of one summand into the recursively represented `bigAdd`. -/
noncomputable def gradedBigAddSlot :
    (k : ℕ) → (B : Fin k → TensorObj K 3) → (j : Fin k) →
      (i : Fin 3) → (B j).V i →ₗ[K] (TensorObj.bigAdd B).V i
  | 0, _, j, _ => j.elim0
  | 1, B, j, i =>
      Fin.cases
        (motive := fun j => (B j).V i →ₗ[K] (B 0).V i)
        LinearMap.id
        (fun j' => j'.elim0)
        j
  | n + 2, B, j, i =>
      Fin.cases
        (motive := fun j => (B j).V i →ₗ[K]
          (TensorObj.add (B 0)
            (TensorObj.bigAdd (fun k => B k.succ))).V i)
        (LinearMap.inl K ((B 0).V i)
          ((TensorObj.bigAdd (fun k => B k.succ)).V i))
        (fun j' =>
          (LinearMap.inr K ((B 0).V i)
            ((TensorObj.bigAdd (fun k => B k.succ)).V i)).comp
              (gradedBigAddSlot (n + 1) (fun k => B k.succ) j' i))
        j

end MME


