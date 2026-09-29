-- Prove2me | Definitions.Def_TarchaBraids_TarchaMoveCertificate_v1
-- name    : TarchaBraids_TarchaMoveCertificate_v1
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-24T09:42:22.021908+00:00
-- url     : https://prove2.me/theorems/024ce2ca-243d-45ca-8f17-5f0494140257
-- title:
--   Finite certificates for Tarcha elementary moves
-- statement:
--   A finite certificate for Tarcha's elementary-move analysis. It records the empty word, a generic contextual Artin-relator insertion, the far-commutator move, and the adjacent-braid move. The certificate is only an interface for a finite sequence of moves; it does not assert that every null geometric half-twist word has such a certificate.
-- source:
--   Tarcha, Um Estudo Introdutório da Teoria de Tranças, Theorem 3.15, pp. 59--62, Figures 3.18--3.27; Birman, Braids, Links and Mapping Class Groups, Chapter 1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

namespace TarchaBraids

open BraidsLinksMCG

inductive TarchaMoveCertificate (n : ℕ) :
    FreeGroup (Fin (n - 1)) → Prop where
  | nil : TarchaMoveCertificate n 1
  | step {w u r} :
      TarchaMoveCertificate n w →
      r ∈ braidRels n →
      TarchaMoveCertificate n (u * r * u⁻¹ * w)
  | far {i j : Fin (n - 1)}
      (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) :
      TarchaMoveCertificate n
        (FreeGroup.of i * FreeGroup.of j * (FreeGroup.of i)⁻¹ *
          (FreeGroup.of j)⁻¹)
  | adjacent {i j : Fin (n - 1)}
      (hji : (j : ℕ) = (i : ℕ) + 1) :
      TarchaMoveCertificate n
        (FreeGroup.of i * FreeGroup.of j * FreeGroup.of i *
          (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹)

end TarchaBraids


