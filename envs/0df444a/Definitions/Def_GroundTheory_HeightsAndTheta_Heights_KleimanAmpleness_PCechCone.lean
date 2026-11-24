-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechCone
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechCone
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:16:50.73906+00:00
-- url     : https://prove2.me/theorems/6e4f4661-05ae-489e-9d95-3c0b3523d8e2
-- title:
--   PCech Cone
-- statement:
--   Definitions and structural lemmas for PCech Cone, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechCone.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u v
namespace Cech.Cone
section Signs
variable {n : ℕ}
end Signs
variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V] {N : ℕ}
def onSet {i : ℕ} (s : Cech.Cochain (fun _ : StdCell N => V) i) (A : Finset (Fin (N + 1))) : V :=
  if h : A.card = i + 1 then
    s ⟨⟨A, Finset.card_pos.mp (by omega), Finset.subset_univ A⟩, h⟩
  else 0
def coneY {i : ℕ} (i₀ : Fin (N + 1)) (z : Cech.Cochain (fun _ : StdCell N => V) (i + 1))
    (A : Finset (Fin (N + 1))) : V :=
  if i₀ ∈ A then 0 else Cech.sgn (insert i₀ A) i₀ • onSet z (insert i₀ A)
end Cech.Cone
end
end GroundTheory.Heights₂.Heights.Kleiman


