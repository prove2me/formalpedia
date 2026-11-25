-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfA
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfA
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T14:19:34.139666+00:00
-- url     : https://prove2.me/theorems/a4a29ab9-b8e1-4274-a415-5ea924ab0886
-- title:
--   Mode Half Statement Pf A
-- statement:
--   Definitions and structural lemmas for Mode Half Statement Pf A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ModeHalfStatementPfA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantNormalForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CompactEntryBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
namespace ModeHalfA
open Matrix NumberField Complex ReciprocityTheory.ChartRestriction.G.FD Topology Filter
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
noncomputable def sf (p0 : ℕ) (α β : Fin r → ℂ) : ℂ :=
  ∑ k : Fin r, ((sgn p0 (k : ℕ) : ℝ) : ℂ) * α k * conj (β k)
def cl (N : Fin r → Fin r → ℂ) (a : Fin r) : Fin r → ℂ := fun k => N k a
noncomputable def Ag (p0 : ℕ) (hp : p0 ≤ r) (N : Fin r → Fin r → ℂ) : Matrix (Fin p0) (Fin p0) ℂ :=
  Matrix.of fun a b => sf p0 (cl N (Fin.castLE hp a)) (cl N (Fin.castLE hp b))
noncomputable def Ms (p0 : ℕ) (hp : p0 ≤ r) (N : Fin r → Fin r → ℂ) (v : Fin r → ℂ) : ℝ :=
  2 * (∑ a : Fin p0, ∑ b : Fin p0, sf p0 v (cl N (Fin.castLE hp a)) * (Ag p0 hp N)⁻¹ a b *
    conj (sf p0 v (cl N (Fin.castLE hp b)))).re - (sf p0 v v).re
end ModeHalfA
end ReciprocityTheory.ChartRestriction.G.AR.Up


