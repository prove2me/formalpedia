-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfB
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfB
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T14:34:29.535038+00:00
-- url     : https://prove2.me/theorems/c3c86c2c-a03f-554a-a341-dbab71a1c78b
-- title:
--   Mode Half Statement Pf B
-- statement:
--   Definitions and structural lemmas for Mode Half Statement Pf B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ModeHalfStatementPfB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
namespace ModeHalfB
open Matrix NumberField Complex ReciprocityTheory.ChartRestriction.G.FD Topology Filter ModeHalfA ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def Nid (r : ℕ) : Fin r → Fin r → ℂ := fun a b => if a = b then 1 else 0
noncomputable def Mt (p0 : ℕ) (hp : p0 ≤ r) (q : (Fin r → ℂ) × (Fin r → Fin r → ℂ) × Matrix (Fin p0) (Fin p0) ℂ) : ℝ :=
  2 * (∑ a : Fin p0, ∑ b : Fin p0, sf p0 q.1 (cl q.2.1 (Fin.castLE hp a)) * q.2.2 a b *
    conj (sf p0 q.1 (cl q.2.1 (Fin.castLE hp b)))).re - (sf p0 q.1 q.1).re
end ModeHalfB
end ReciprocityTheory.ChartRestriction.G.AR.Up


