-- Prove2me | Definitions.Def_TarchaBraids_TarchaFreeMoveCertificate_v1
-- name    : TarchaBraids_TarchaFreeMoveCertificate_v1
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-24T10:32:11.377121+00:00
-- url     : https://prove2.me/theorems/e6f503bc-920a-466c-8e48-b084fee87ee8
-- title:
--   Finite certificates for Tarcha moves including free cancellation
-- statement:
--   This finite certificate records the elementary moves used in Tarcha's Theorem 3.15. It includes the free-group equality cases, contextual insertions of Artin relators, explicit composition of successive move words, the far commuting move, and the adjacent braid move. It is an algebraic interface only; it does not assert that every null geometric half-twist word has such a certificate.
-- source:
--   Tarcha, Um Estudo Introdutório da Teoria de Tranças, Theorem 3.15, pp. 59--62, Figures 3.18--3.27; Birman, Braids, Links and Mapping Class Groups, Chapter 1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

namespace TarchaBraids

open BraidsLinksMCG

inductive TarchaFreeMoveCertificate (n : ℕ) :
    FreeGroup (Fin (n - 1)) → Prop where
  | nil : TarchaFreeMoveCertificate n 1
  | freeEq {x y} (h : x = y) :
      TarchaFreeMoveCertificate n x → TarchaFreeMoveCertificate n y
  | contextual {w u r} :
      TarchaFreeMoveCertificate n w →
      r ∈ braidRels n →
      TarchaFreeMoveCertificate n (u * r * u⁻¹ * w)
  | mul {x y} :
      TarchaFreeMoveCertificate n x →
      TarchaFreeMoveCertificate n y →
      TarchaFreeMoveCertificate n (x * y)
  | far {i j : Fin (n - 1)}
      (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) :
      TarchaFreeMoveCertificate n
        (FreeGroup.of i * FreeGroup.of j * (FreeGroup.of i)⁻¹ *
          (FreeGroup.of j)⁻¹)
  | adjacent {i j : Fin (n - 1)}
      (hji : (j : ℕ) = (i : ℕ) + 1) :
      TarchaFreeMoveCertificate n
        (FreeGroup.of i * FreeGroup.of j * FreeGroup.of i *
          (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹)

end TarchaBraids


