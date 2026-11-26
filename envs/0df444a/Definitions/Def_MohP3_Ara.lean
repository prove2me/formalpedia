-- Prove2me | Definitions.Def_MohP3_Ara
-- name    : MohP3_Ara
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T21:57:35.294282+00:00
-- url     : https://prove2.me/theorems/a8f00c6f-13e3-5a6a-a30d-245aa530f825
-- title:
--   Ara
-- statement:
--   Definitions and structural lemmas for Ara, from GrgAakash (GrgAakash/moh-p3-set-theoretic-complete-intersection; see pinned Apache-2.0 LICENSE and README.md)'s pinned Moh P3 curve is a global and formal-local set-theoretic complete intersection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Ara.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace MohP3
variable {A : Type*} [CommRing A]
noncomputable def arithRank (I : Ideal A) : ℕ∞ :=
  ⨅ s ∈ {s : Finset A | (Ideal.span (s : Set A)).radical = I.radical}, (s.card : ℕ∞)
end MohP3


