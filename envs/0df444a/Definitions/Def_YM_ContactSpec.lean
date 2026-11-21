-- Prove2me | Definitions.Def_YM_ContactSpec
-- name    : YM_ContactSpec
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T11:38:26.719433+00:00
-- url     : https://prove2.me/theorems/b207e859-0f58-4678-9311-f2a5dae1b627
-- title:
--   Contact distributions on collision diagonals
-- statement:
--   Defines the contact-distribution clause: for every character option, arity and label assignment, the separated correlation function extends to a continuous linear functional on compactly supported smooth tests on the full configuration space including collision diagonals, agreeing with the correlation integral on tests supported away from diagonals. Uniqueness of the extension and raw cutoff convergence on diagonals are not asserted.
-- source:
--   https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/ContactSpec.lean

import Definitions.Def_YM_ChallengeSpec

set_option autoImplicit false
noncomputable section
namespace YangMills
open Set MeasureTheory TopologicalSpace
open scoped Distributions
namespace Hierarchy
variable {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)
/-- A distribution on the full configuration space, including every collision diagonal,
whose restriction to pairwise separated insertions is the same correlation function. -/
def Contacts : Prop := ∀ (s : Option T.Character) (n : ℕ) (v : Fin n → T.Tag),
  ∃ D : _root_.TestFunction (⊤ : Opens (Points n)) ℂ ⊤ →L[ℂ] ℂ, ∀ f : _root_.TestFunction (⊤ : Opens (Points n)) ℂ ⊤,
    tsupport f ⊆ WilsonFamily.separated n → D f = ∫ x, f x * T.correlation s v x

end Hierarchy

end YangMills


