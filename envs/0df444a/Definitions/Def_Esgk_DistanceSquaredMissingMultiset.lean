-- Prove2me | Definitions.Def_Esgk_DistanceSquaredMissingMultiset
-- name    : Esgk_DistanceSquaredMissingMultiset
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:49:34.723045+00:00
-- url     : https://prove2.me/theorems/259127c6-92af-4ced-b564-b104258db734
-- title:
--   Multiset of missing squared distances
-- statement:
--   For a configuration point, this forms the multiset containing each ordered distance value's squared value with its missing-neighbor multiplicity.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_DistanceDeficiencyNewton
import Definitions.Def_Esgk_Energy
import Definitions.Def_Esgk_Foundation
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open scoped BigOperators

variable {n : ℕ}

 
noncomputable def distanceSquaredMissingMultiset
    (p : Config n) (i : Fin n) : Multiset ℝ :=
  (OrderedDistanceValues p).val.bind fun r ↦
    Multiset.replicate (DistanceMissingMultiplicity p i r) (r ^ 2)


end Esgk


