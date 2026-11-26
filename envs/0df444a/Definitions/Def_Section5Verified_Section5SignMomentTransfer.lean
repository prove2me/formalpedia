-- Prove2me | Definitions.Def_Section5Verified_Section5SignMomentTransfer
-- name    : Section5Verified_Section5SignMomentTransfer
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:37:38.207289+00:00
-- url     : https://prove2.me/theorems/dead8ce0-0bb2-401f-aef3-7ccb23154d60
-- title:
--   Section5SignMomentTransfer — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5SignMomentTransfer; mechanically extracted with exact Lean declaration spans.

import Mathlib
section
set_option autoImplicit false

/-! Bounded squarefree sign moments determine the expectation of every
polynomial of bounded total degree. This is a finite-sum identity. -/

namespace Section5SignMoments

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

noncomputable def mean (f : Ω → ℝ) : ℝ := (Fintype.card Ω : ℝ)⁻¹ * ∑ x, f x









def oddSupport (d : ι →₀ ℕ) : Finset ι := d.support.filter (fun i => d i % 2=1)









end Section5SignMoments

end


