-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_StatementBC
-- name    : Formalism_CharacterColumnKernels_StatementBC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:28:02.99036+00:00
-- url     : https://prove2.me/theorems/71fe21ba-48b5-478b-9feb-c2c1fdda7baa
-- title:
--   Statement BC
-- statement:
--   Definitions and structural lemmas for Statement BC, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/StatementBC.lean

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.NG
def StatVccBaseChange : Prop :=
  ∀ (O O' : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [Module.Free O O']
    [Module.Finite O O'] (e : ℕ),
    (∀ y : O, IsDiscreteValuationRing.addVal O' (algebraMap O O' y) =
      e * IsDiscreteValuationRing.addVal O y) →
    ∀ (X : Type*) (T : Subalgebra O (X → O)) (T' : Subalgebra O' (X → O')),
      (T' : Set (X → O')) = Submodule.span O' ((fun f : X → O => algebraMap O O' ∘ f) '' (T : Set (X → O))) →
    ∀ (Z : Set X) (x : X), vcc T' Z x = e * vcc T Z x
end Formalism.NG


