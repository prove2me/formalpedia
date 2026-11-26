-- Prove2me | Definitions.Def_BKAR_PartialDeriv
-- name    : BKAR_PartialDeriv
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:17:21.346334+00:00
-- url     : https://prove2.me/theorems/e1e93e14-1824-4011-a8e8-3468b6337f99
-- title:
--   Partial Deriv
-- statement:
--   Definitions and structural lemmas for Partial Deriv, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDeriv.lean

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Definitions.Def_BKAR_Interpolation
set_option autoImplicit false
namespace BKAR
variable {V : Type*} [DecidableEq V]
def updateCoord (x : Edge V → ℝ) (e : Edge V) (t : ℝ) : Edge V → ℝ :=
  Function.update x e t
def edgeBasis (e : Edge V) : Edge V → ℝ :=
  Pi.single e (1 : ℝ)
noncomputable def partialDeriv (e : Edge V)
    (ρ : (Edge V → ℝ) → ℝ) (x : Edge V → ℝ) : ℝ :=
  deriv (fun t : ℝ => ρ (updateCoord x e t)) (x e)
noncomputable def mixedPartialList :
    List (Edge V) → ((Edge V → ℝ) → ℝ) → (Edge V → ℝ) → ℝ
  | [], ρ => ρ
  | e :: es, ρ => partialDeriv e (mixedPartialList es ρ)
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (F : Forest V)
noncomputable def mixedPartial (ρ : (Edge V → ℝ) → ℝ) :
    (Edge V → ℝ) → ℝ :=
  mixedPartialList F.edges.toList ρ
end Forest
end BKAR


