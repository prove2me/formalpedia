-- Prove2me | Definitions.Def_Formalism_SubspaceCounting_StatementD
-- name    : Formalism_SubspaceCounting_StatementD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:13:16.050795+00:00
-- url     : https://prove2.me/theorems/ed721c68-86b0-401f-957d-466ad25b5009
-- title:
--   Statement D
-- statement:
--   Definitions and structural lemmas for Statement D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/StatementD.lean

import Definitions.Def_Formalism_SubspaceCounting_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.G0
def AllButLESmith : Prop := by
  classical
  exact
  ∀ {O M ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M] [Module O M] [Fintype ι] (π : O), Irreducible π →
    ∀ (P : Submodule O M) (n : ℕ) (snf : Module.Basis.SmithNormalForm P ι n) (g E : ℕ),
    AllButLE π ⊤ P g E ↔
      ((Finset.univ.filter fun i : Fin n => ¬ snf.a i ∣ π ^ E).card + (Fintype.card ι - n) ≤ g)
end Formalism.G0


