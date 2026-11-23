-- Prove2me | Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
-- name    : GroupTheoreticShannonCapacity_MainProofs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:27:08.847318+00:00
-- url     : https://prove2.me/theorems/864c411e-43dd-4dbc-a619-6da8d758fa30
-- title:
--   Main Proofs
-- statement:
--   Definitions and structural lemmas for Main Proofs, from jzuiddam/GroupTheoreticShannonCapacity contributors (see pinned LICENSE and source headers)'s pinned Shannon capacity limits from lattice packings development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MainProofs.lean

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
set_option autoImplicit true
namespace GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice
noncomputable def Delta (n k b r s : ℝ) : ℝ :=
  let a := k * b^n + s * b + r
  a / b - ((r/k * s^n + a^n) / (r/k + b^n))^(1/n)
end GroupTheoreticShannonCapacity.MainProofs


