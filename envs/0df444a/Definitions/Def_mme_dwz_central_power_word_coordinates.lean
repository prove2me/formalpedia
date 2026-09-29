-- Prove2me | Definitions.Def_mme_dwz_central_power_word_coordinates
-- name    : mme_dwz_central_power_word_coordinates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T05:35:52.083554+00:00
-- url     : https://prove2.me/theorems/43ac29a5-4dd4-47bc-8586-204d64be968e
-- title:
--   Literal coordinates of central CW-square channel words after power flattening
-- statement:
--   A length-\(m\) word in the central 022 or 202 channel alphabet has one coordinate in \([q^2+2]\) at each position. This interface defines its literal full coordinate by the little-endian base expansion\n\n$$\n\sum_{i=0}^{m-1} c_i(q^2+2)^i.\n$$\n\nIt also names the corresponding standard basis vectors in all three modes of the flattened 022 and 202 matrix-multiplication tensors. The one-dimensional modes retain their explicit unique power coordinates, so later restriction maps can track prescribed source words without replacing them by arbitrary coordinates of the same cardinality.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.3 and Appendix A, https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_little_endian_MM_power_flatten
import Definitions.Def_mme_dwz_cw_square_restricted_central_power_words

namespace MME.DWZFineChannel

universe u

set_option autoImplicit false

/-- The base-`P` coordinate of a word, with position zero least significant. -/
noncomputable def littleEndianWordIndex (P r : ℕ) :
    (Fin r → Fin P) ≃ Fin (P ^ r) :=
  finFunctionFinEquiv

/-- The exact collapsed MM coordinate of a fine central-channel word. -/
noncomputable def fineChannelWordIndex (q m : ℕ) :
    (Fin m → Fine022Channel q) ≃ Fin ((q ^ 2 + 2) ^ m) :=
  (Equiv.piCongrRight (fun _ : Fin m ↦ fine022ChannelEquiv q)).trans
    finFunctionFinEquiv

/-- The unique little-endian coordinate in a power of a one-point mode. -/
noncomputable def unitWordIndex (m : ℕ) : Fin (1 ^ m) :=
  littleEndianWordIndex 1 m (fun _ ↦ 0)

/-- The flat 022 basis triple at a named word coordinate. -/
noncomputable def central022FlatMMVec
    (K : Type u) [Field K] (q m : ℕ)
    (k : Fin ((q ^ 2 + 2) ^ m)) :
    ∀ s : Fin 3,
      (MMObj K (1 ^ m) (1 ^ m) ((q ^ 2 + 2) ^ m)).V s
  | ⟨0, _⟩ =>
      (Pi.single (unitWordIndex m, unitWordIndex m) 1 :
        Fin (1 ^ m) × Fin (1 ^ m) → K)
  | ⟨1, _⟩ =>
      (Pi.single (unitWordIndex m, k) 1 :
        Fin (1 ^ m) × Fin ((q ^ 2 + 2) ^ m) → K)
  | ⟨2, _⟩ =>
      (Pi.single (k, unitWordIndex m) 1 :
        Fin ((q ^ 2 + 2) ^ m) × Fin (1 ^ m) → K)

/-- The flat 202 basis triple at the same named word coordinate. -/
noncomputable def central202FlatMMVec
    (K : Type u) [Field K] (q m : ℕ)
    (k : Fin ((q ^ 2 + 2) ^ m)) :
    ∀ s : Fin 3,
      (MMObj K ((q ^ 2 + 2) ^ m) (1 ^ m) (1 ^ m)).V s
  | ⟨0, _⟩ =>
      (Pi.single (k, unitWordIndex m) 1 :
        Fin ((q ^ 2 + 2) ^ m) × Fin (1 ^ m) → K)
  | ⟨1, _⟩ =>
      (Pi.single (unitWordIndex m, unitWordIndex m) 1 :
        Fin (1 ^ m) × Fin (1 ^ m) → K)
  | ⟨2, _⟩ =>
      (Pi.single (unitWordIndex m, k) 1 :
        Fin (1 ^ m) × Fin ((q ^ 2 + 2) ^ m) → K)

end MME.DWZFineChannel


