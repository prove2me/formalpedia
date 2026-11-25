-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_AttainsBlockListOfWeightsAlongOrbits
-- name    : Development_AutomorphicArithmetic_OrbitLabellings_AttainsBlockListOfWeightsAlongOrbits
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:23:29.253975+00:00
-- url     : https://prove2.me/theorems/931b89b6-459f-40eb-a3f0-2077352487d7
-- title:
--   Attains Block List Of Weights Along Orbits
-- statement:
--   Definitions and structural lemmas for Attains Block List Of Weights Along Orbits, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/OrbitLabellings/AttainsBlockListOfWeightsAlongOrbits.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_RowDefs
import Definitions.Def_Formalism_DropLevelBounds_ThBounds
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral UpperTheory.G2
namespace UpperTheory.G2.RowPlan
variable {d : ℕ} [NeZero d]
noncomputable def supp (y : ZMod d → ℕ → ℕ) : Finset (ZMod d × ℕ) :=
  (Finset.univ ×ˢ oddLevels d).filter fun x => y x.1 x.2 ≠ 0
noncomputable def rst (n : ℕ) (ga : ZMod (2 * d) → ℕ → ℕ) (s : ZMod (2 * d)) : ZMod (2 * d) → ℕ → ℕ :=
  fun a k => if a = s then (if Even s.val ∧ k = n then 0 else ga s k) else 0
variable {C : Type} [Field C] {V : VF C} {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
noncomputable def blocks (X : RowData C V (2 * d) I J) (ev : ZMod d → ZMod (2 * d)) (y : ZMod d → ℕ → ℕ)
    (u : ZMod d → ℕ) (ga : ZMod (2 * d) → ℕ → ℕ) (K : ℕ) : List (RF.GlobalTheory (2 * d) × ℝ) :=
  ((Finset.univ : Finset (ZMod (2 * d))).toList.map fun s =>
      (RF.GlobalTheory.mon 0 (rst X.n ga s) K, (RF.monDegAll X 0 (rst X.n ga s) K : ℝ) / ((V.l : ℝ) - 1))) ++
  (((Finset.univ : Finset (ZMod d)).toList.map fun a =>
      (RF.GlobalTheory.ch 0 (ev a) (u a), RF.chBd V.l X.n X.m (u a))) ++
    ((supp y).toList.map fun x =>
      (RF.GlobalTheory.bi 0 (ev x.1) x.2 (y x.1 x.2), RF.blockBd V.l X.n X.m x.2 (y x.1 x.2))))
end UpperTheory.G2.RowPlan


