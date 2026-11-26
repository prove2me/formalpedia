-- Prove2me | Definitions.Def_Section5Verified_Section5CodedFrameCovariance
-- name    : Section5Verified_Section5CodedFrameCovariance
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:40:22.173626+00:00
-- url     : https://prove2.me/theorems/9ea5c69e-d083-4a80-9b84-11c515b09442
-- title:
--   Section5CodedFrameCovariance — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5CodedFrameCovariance; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_Section5Verified_Section5PowerCodeCharacters
import Mathlib
section
set_option autoImplicit false

namespace Section5PowerCode

variable {F ι : Type*} [Field F] [Fintype F] [CharP F 2]
  [Fintype ι] [DecidableEq ι]

noncomputable def frameWeight {k : ℕ} (χ : AddChar F ℝ) (v : ι → F)
    (w : ι → ℝ) (t : Fin k → F) : ℝ :=
  (Fintype.card (Fin k → F) : ℝ)⁻¹*(∑ i, w i*codeSign χ v t i)^2









end Section5PowerCode

end


