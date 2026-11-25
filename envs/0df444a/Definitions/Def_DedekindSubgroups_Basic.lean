-- Prove2me | Definitions.Def_DedekindSubgroups_Basic
-- name    : DedekindSubgroups_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:01:01.012438+00:00
-- url     : https://prove2.me/theorems/97ccccf1-0815-5bfa-9c2c-b3400e3e0957
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from J. S. Farland (jkfarland-bot/DedekindSubgroups-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned DedekindSubgroups: a congruence modulo 16 for sums of Dedekind sums over subgroups of odd order development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Basic.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace DedekindSubgroups
noncomputable def sawtooth (x : ℚ) : ℚ := if Int.fract x = 0 then 0 else Int.fract x - 1 / 2
noncomputable def dedekindSum (h k : ℕ) : ℚ :=
  ∑ r ∈ range k, sawtooth ((r : ℚ) / k) * sawtooth ((h * r : ℚ) / k)
end DedekindSubgroups


