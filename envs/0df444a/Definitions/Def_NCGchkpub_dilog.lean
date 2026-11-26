-- Prove2me | Definitions.Def_NCGchkpub_dilog
-- name    : NCGchkpub_dilog
-- status  : Definition
-- author  : @LG
-- created : 2026-11-26T12:22:45.684203+00:00
-- url     : https://prove2.me/theorems/648ea89d-1581-4b6f-b64a-f642fffefc95
-- title:
--   Dilogarithm (public check)
-- statement:
--   Li₂(z)=Σ z^n/n².

import Mathlib

namespace NCGchkpub
noncomputable def dilog (z : ℂ) : ℂ := ∑' k : ℕ, z ^ (k + 1) / (k + 1 : ℂ) ^ 2
end NCGchkpub


