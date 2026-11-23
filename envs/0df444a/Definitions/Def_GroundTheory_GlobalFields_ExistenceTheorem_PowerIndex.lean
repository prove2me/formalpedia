-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ExistenceTheorem_PowerIndex
-- name    : GroundTheory_GlobalFields_ExistenceTheorem_PowerIndex
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:17.926988+00:00
-- url     : https://prove2.me/theorems/08b654cc-200f-4566-90a5-183e7563db62
-- title:
--   Power Index
-- statement:
--   Definitions and structural lemmas for Power Index, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ExistenceTheorem/PowerIndex.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open NumberField IsDedekindDomain Module
noncomputable section
section PowerIndex
variable {G : Type*} [CommGroup G]
instance finite_additive_quotient_torsion [Group.FG G] :
    Module.Finite ℤ (Additive (G ⧸ CommGroup.torsion G)) := by
  rw [Module.Finite.iff_addGroup_fg, AddGroup.fg_iff_addMonoid_fg, ← Monoid.fg_iff_add_fg,
    ← Group.fg_iff_monoid_fg]
  infer_instance
end PowerIndex
section SUnit
variable {K : Type*} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
namespace SUnit
end SUnit
end SUnit
end
end GroundTheory.Global


