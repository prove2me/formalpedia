-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_CharIdem
-- name    : Formalism_PeriodIntegrals_CharIdem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:44:04.83943+00:00
-- url     : https://prove2.me/theorems/9593869d-2521-4fa8-9803-f66a09ce9851
-- title:
--   Char Idem
-- statement:
--   Definitions and structural lemmas for Char Idem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/CharIdem.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
namespace PI.CharIdem
variable {G : Type} [Group G] [Fintype G]
noncomputable def charIdem (V : FDRep ℂ G) : MonoidAlgebra ℂ G :=
  ∑ g : G, MonoidAlgebra.single g (((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ)) * V.character g⁻¹)
noncomputable def act (V : FDRep ℂ G) : MonoidAlgebra ℂ G →ₐ[ℂ] Module.End ℂ V :=
  MonoidAlgebra.lift ℂ (Module.End ℂ V) G V.ρ
def CharIdem : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (V W : FDRep ℂ G), Simple V → Simple W →
    act V (charIdem V) = 1 ∧
    (IsEmpty (V ≅ W) → act W (charIdem V) = 0) ∧
    IsIdempotentElem (charIdem V) ∧
    (∀ x : MonoidAlgebra ℂ G, charIdem V * x = x * charIdem V) ∧
    (IsEmpty (V ≅ W) → charIdem V * charIdem W = 0)
end PI.CharIdem


