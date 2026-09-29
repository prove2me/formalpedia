-- Prove2me | Definitions.Def_ProximityPrize_SubmissionUpper_HalfRadiusCollision_dot
-- name    : ProximityPrize_SubmissionUpper_HalfRadiusCollision_dot
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-27T04:28:40.493083+00:00
-- url     : https://prove2.me/theorems/ae3728c5-7227-4de7-9328-5d80e60d9828
-- title:
--   ProximityPrize.SubmissionUpper.HalfRadiusCollision.dot
-- statement:
--   Finite-field dot product used by the Proximity Prize upper-bound proof.
--
--   Original Proximity Prize source by GitHub contributor gpsanant; preserved in the verified upper submission by erdkocak (224323f053d0d1dfa78d7b9625194fe0133f04bc). Ported from Lean 4.32.2 to 4.33.1 with independently checked statements, full source and target kernel replay, quotient checks and transitive axiom checks. This provider publication is not a new competition submission.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/a36cdb6a0c9be507b70276a92129bb15d4ed2a27/ProximityPrize/SubmissionUpper/HalfRadiusCollision.lean
--
--   yukon-proof-operation:bootstrap-d70ab56cdc82b3871892d825a530fa13902cf33c730aca3835336a5abbfdb92a
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246Ym9vdHN0cmFwLWQ3MGFiNTZjZGM4MmIzODcxODkyZDgyNWE1MzBmYTEzOTAyY2YzM2M3MzBhY2EzODM1MzM2YTVhYmJmZGI5MmEiLCJoYXNoIjoiNzI3NjQ3MmRkOWRiMGYxMjY0NDNiNTg1ODZjOTgyYmUwMmMyZDAyNmNlZTllMWM3YTZiMTFlMzYyNDIzYzE2MCIsImtpbmQiOiJkZWZpbml0aW9uIiwidGFyZ2V0IjoiUHJveGltaXR5UHJpemVfU3VibWlzc2lvblVwcGVyX0hhbGZSYWRpdXNDb2xsaXNpb25fZG90IiwiZW52aXJvbm1lbnQiOnsidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIiwibWF0aGxpYlJldiI6IjBkZjQ0NGEzNjBlYWE2MGFiOGMxMWRjYTUxYTg2YWY2OTI5NTU0NzQifSwidGFnIjoicHJveGltaXR5LXByaXplIn0]

import Mathlib
import Init
namespace ProximityPrize.SubmissionUpper.HalfRadiusCollision

open scoped BigOperators

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

def dot {k : ℕ} (x v : Fin k → F) : F := ∑ i, x i * v i
end HalfRadiusCollision
end SubmissionUpper
end ProximityPrize


