-- Prove2me | Definitions.Def_d9ClippedSeats
-- name    : d9ClippedSeats
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T08:07:32.865392+00:00
-- url     : https://prove2.me/theorems/e2dce4f6-a9e3-444b-ab0b-00a2178e7c8b
-- title:
--   d9ClippedSeats
-- statement:
--   Automatically extracted helper definition d9ClippedSeats from oversized parent candidate 029f41399a9b5b2cc3817d3867fba60227809162ca9c89b493c85daffb84e989.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:029f41399a9b5b2cc3817d3867fba60227809162ca9c89b493c85daffb84e989

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open NestedSeatAlloc.IntPolicy

/- Core signed-fare and derivative development for the d9 bridge. -/
def d9ClippedSeats (p x s : ℝ) : ℝ := min x (max 0 (s - p))


