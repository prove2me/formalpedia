-- Prove2me | Definitions.Def_mme_induced_mode_choice_certificate
-- name    : mme_induced_mode_choice_certificate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-24T18:47:59.442078+00:00
-- url     : https://prove2.me/theorems/30fe0dfd-fa63-474b-afcd-997533d0a360
-- title:
--   Finite mode-choice certificates for induced tensor zeroing
-- statement:
--   Let $S$ and $T$ be order-three tensors. A finite mode-choice certificate records, separately in each tensor mode, a finite family of linear maps from $S$ to $T$. It also records a finite set $E$ of retained triples of map choices. Every choice outside $E$ must send the source tensor to zero, and the sum of the images indexed by $E$ must equal the target tensor.
--
--   This packages exactly the finite data needed in an induced-variable-zeroing argument. It does not contain a tensor-restriction witness, a common-factor assertion, or any asymptotic assumption. The certificate is intended as reusable infrastructure for laser-method block extraction and other finite support-zeroing arguments.
-- source:
--   Elementary multilinearity of tensor products; the induced variable-zeroing application follows the block-zeroing step in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal p. 271, https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_tensor

open PiTensorProduct BigOperators

universe u

namespace MME

structure InducedModeChoiceCertificate
    {K : Type u} [Field K]
    (source target : TensorObj K 3) where
  slotCount : Fin 3 → ℕ
  modeMap : ∀ i : Fin 3,
    Fin (slotCount i) → source.V i →ₗ[K] target.V i
  kept : Finset (∀ i : Fin 3, Fin (slotCount i))
  offSupport : ∀ choice : ∀ i : Fin 3, Fin (slotCount i),
    choice ∉ kept →
      PiTensorProduct.map (fun i => modeMap i (choice i)) source.t = 0
  targetTensor :
    target.t =
      ∑ choice : {choice : (∀ i : Fin 3, Fin (slotCount i)) //
          choice ∈ kept},
        PiTensorProduct.map
          (fun i => modeMap i (choice.1 i)) source.t

end MME


