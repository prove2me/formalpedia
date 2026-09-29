-- Prove2me | Definitions.Def_Erdos9796Mission_PinnedMultiplicity
-- name    : Erdos9796Mission_PinnedMultiplicity
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-11T16:22:18.214457+00:00
-- url     : https://prove2.me/theorems/4cf28fd0-0836-435b-8d01-9958a5133875
-- title:
--   Pinned distance multiplicity
-- statement:
--   For a finite planar point set A and a center p, define the realized positive radii from p and the maximum number of points of A lying at one such radius. This maximum is the pinned distance multiplicity at p.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/3d0e9306396f0aa6639f4453174693990fe9c242/lean/Erdos9796Proof/P97/PinnedMultiplicity.lean#L154-L166

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Erdos9796Mission

open scoped EuclideanGeometry

namespace Erdos9796Mission

/-- The positive distances from `p` that are realized inside `A`. -/
noncomputable def pinnedRadii (A : Finset Plane) (p : Plane) : Finset ℝ :=
  (A.image (fun q => dist p q)).filter (fun r => 0 < r)

/-- The largest number of points of `A` on one positive-radius circle centered
at `p`. The value is zero when no positive distance is realized. -/
noncomputable def pinnedMultiplicity (A : Finset Plane) (p : Plane) : ℕ :=
  (pinnedRadii A p).sup (fun r => (A.filter (fun q => dist p q = r)).card)

end Erdos9796Mission


