-- Prove2me | Definitions.Def_Formalism_WachLatticeTwists_StatementDual
-- name    : Formalism_WachLatticeTwists_StatementDual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:16.832274+00:00
-- url     : https://prove2.me/theorems/48b3e2fe-f22b-4df6-bc67-90af784bb043
-- title:
--   Statement Dual
-- statement:
--   Definitions and structural lemmas for Statement Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/StatementDual.lean

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.RepresentationBoundsCohomology
def annKO (O : Type*) [CommRing O] [IsDomain O] {H : Type*} [AddCommGroup H] [Module O H]
    (S : Submodule O H) : Submodule O (H →ₗ[O] Formalism.NG.KO O) where
  carrier := {φ | ∀ x ∈ S, φ x = 0}
  add_mem' := by intro a b ha hb x hx; simp [ha x hx, hb x hx]
  zero_mem' := by intro x _; rfl
  smul_mem' := by intro c a ha x hx; simp [ha x hx]
def StatDualColength : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (H : Type*) [AddCommGroup H] [Module O H] [Module.Finite O H] (I M : Submodule O H), I ≤ M →
    Module.length O (annKO O I ⧸ (annKO O M).comap (annKO O I).subtype) =
      Module.length O (M ⧸ I.comap M.subtype)
end Formalism.RepresentationBoundsCohomology


