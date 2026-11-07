-- Prove2me | Definitions.Def_AaronsonAmbainis_Bridge_Fourier
-- name    : AaronsonAmbainis_Bridge_Fourier
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:56:01.249045+00:00
-- url     : https://prove2.me/theorems/eb07d543-6505-4094-af35-b35c276b80f8
-- title:
--   Fourier
-- statement:
--   Definitions and structural lemmas for Fourier, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
set_option autoImplicit true
namespace AaronsonAmbainis.Bridge
open Finset
noncomputable def sg (b : Bool) : ℝ := if b then -1 else 1
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def fourier (f : Cube ι → ℝ) (S : Finset ι) : ℝ :=
  (∑ y, f y * chi S y) / 2 ^ Fintype.card ι
end AaronsonAmbainis.Bridge


