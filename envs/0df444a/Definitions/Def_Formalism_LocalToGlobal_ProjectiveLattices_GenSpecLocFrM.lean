-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSpecLocFrM
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_GenSpecLocFrM
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:46.616795+00:00
-- url     : https://prove2.me/theorems/498edf78-ea16-48cd-8906-3f42d0672c6a
-- title:
--   Gen Spec Loc Fr M
-- statement:
--   Definitions and structural lemmas for Gen Spec Loc Fr M, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSpecLocFrM.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj.LocFrM
open TensorProduct
variable {O : Type*} [CommRing O] [IsLocalRing O] {V : Type*} [AddCommGroup V] [Module O V]
  [Module.Free O V] [Module.Finite O V]
section Split
variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
end Split
end Formalism.L2.Pj.LocFrM


