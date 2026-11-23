-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_IntCoresB
-- name    : ReciprocityTheory_SemistableReduction_IntCoresB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:35.051043+00:00
-- url     : https://prove2.me/theorems/92152566-81f8-4ab1-bbac-682ebbb21ca6
-- title:
--   Int Cores B
-- statement:
--   Definitions and structural lemmas for Int Cores B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/IntCoresB.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCoresA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric
def BlockPoly (k n : ℕ) (a : Fin k → ℕ) (F : (Fin k → Fin n → ℂ) → ℂ) : Prop :=
  Continuous F ∧ ∀ (b : Fin k) (p : Fin k → Fin n → ℂ), ∃ g : MvPolynomial (Fin n) ℂ,
    g.IsHomogeneous (a b) ∧ ∀ w, F (Function.update p b w) = MvPolynomial.eval w g
def onSpheres {k n : ℕ} (F : (Fin k → Fin n → ℂ) → ℂ) (z : Fin k → UnitSphereC n) : ℂ :=
  F fun b => spherePoint (z b)
end ReciprocityTheory.MultiplicativeHeights


