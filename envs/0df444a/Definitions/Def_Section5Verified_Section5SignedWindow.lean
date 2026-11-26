-- Prove2me | Definitions.Def_Section5Verified_Section5SignedWindow
-- name    : Section5Verified_Section5SignedWindow
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:37:57.923284+00:00
-- url     : https://prove2.me/theorems/b2f34e75-3778-436e-9145-3d51b6e42813
-- title:
--   Section5SignedWindow — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5SignedWindow; mechanically extracted with exact Lean declaration spans.

import Mathlib
section
set_option autoImplicit false

/-! Signed middle-bit windows. The discarded low bits cause a bounded rounding error;
the omitted high bits are irrelevant inside the represented interval. -/

def section5_signed_residue (H z : ℤ) : ℤ :=
  if z % (2*H) < H then z % (2*H) else z % (2*H)-2*H



def section5_window_truncate (P H z : ℤ) : ℤ := P*section5_signed_residue H (z/P)









end


