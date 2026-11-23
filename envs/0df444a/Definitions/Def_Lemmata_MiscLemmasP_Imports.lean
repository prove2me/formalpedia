-- Prove2me | Definitions.Def_Lemmata_MiscLemmasP_Imports
-- name    : Lemmata_MiscLemmasP_Imports
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:28:33.405596+00:00
-- url     : https://prove2.me/theorems/0756f8b9-9da6-418a-ad61-aedc38c190f9
-- title:
--   Imports
-- statement:
--   Definitions and structural lemmas for Imports, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/MiscLemmasP/Imports.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
namespace Bl.ThirdBlockLemmaA
noncomputable def goal1 :
  {n : Nat} →   {M : Type u_1} →     [inst : AddCommGroup M] →       [inst_1 : _root_.Module Complex M] →         (Fin n → Fin n → Module.End Complex M) → Nat → Fin n → Fin n → Module.End Complex M := fun A k i j => ((Matrix.of A) ^ k) i j
end Bl.ThirdBlockLemmaA


