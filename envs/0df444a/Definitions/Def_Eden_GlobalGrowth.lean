-- Prove2me | Definitions.Def_Eden_GlobalGrowth
-- name    : Eden_GlobalGrowth
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:37:36.876776+00:00
-- url     : https://prove2.me/theorems/f5c02374-5d14-486f-a71d-36ba66f5f25a
-- title:
--   Global Growth
-- statement:
--   Definitions and structural lemmas for Global Growth, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowth.lean

import Definitions.Def_Eden_IntegerGrowthBounds
set_option autoImplicit true
noncomputable section
open Set
namespace Eden
def integerGrowthValues (c : ℝ) (k : ℕ) (t : ℝ) : Set ℝ :=
  (fun p => singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap k) '' attractor
def supremumSingularProduct (c : ℝ) (k : ℕ) (t : ℝ) : ℝ := sSup (integerGrowthValues c k t)
def globalLogGrowth (c : ℝ) (k : ℕ) (t : ℝ) : ℝ := Real.log (supremumSingularProduct c k t)
end Eden


