-- Prove2me | Definitions.Def_TarchaBraids_GeomRelatorTrace_v1
-- name    : TarchaBraids_GeomRelatorTrace_v1
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-24T07:29:34.760964+00:00
-- url     : https://prove2.me/theorems/04cbf8b4-e995-48dd-bef4-cfab0f181afb
-- title:
--   Finite contextual Artin-relator traces
-- statement:
--   A finite contextual Artin-relator trace records a word as the empty word or as a finite sequence of insertions of a commuting or adjacent braid relator in an arbitrary free-group context, followed by the inverse context. The definition is the algebraic trace interface used to formalize the finite elementary-move analysis in Tarcha's Theorem 3.15; it makes no claim by itself that a geometric null word has such a trace.
-- source:
--   Tarcha, Um Estudo Introdutório da Teoria de Tranças, Theorem 3.15, pp. 59--62, Figures 3.18--3.27; Birman, Braids, Links and Mapping Class Groups, Chapter 1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

namespace TarchaBraids

open BraidsLinksMCG

inductive GeomRelatorTrace (n : ℕ) :
    FreeGroup (Fin (n - 1)) → Prop where
  | nil : GeomRelatorTrace n 1
  | step {w u r : FreeGroup (Fin (n - 1))} :
      GeomRelatorTrace n w →
      r ∈ braidRels n →
      GeomRelatorTrace n (u * r * u⁻¹ * w)

end TarchaBraids


