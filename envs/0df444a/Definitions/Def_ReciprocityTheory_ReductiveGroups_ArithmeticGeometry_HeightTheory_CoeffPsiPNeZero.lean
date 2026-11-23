-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffPsiPNeZero
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffPsiPNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:14.721295+00:00
-- url     : https://prove2.me/theorems/7bd8e055-471f-4d0b-8a04-bc8a01ad79cc
-- title:
--   Coeff Psi PNe Zero
-- statement:
--   Definitions and structural lemmas for Coeff Psi PNe Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CoeffPsiPNeZero.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0.WH
open MvPolynomial
variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] (p : σ → Prop) [DecidablePred p]
def wt (s : σ →₀ ℕ) : ℕ := ∑ v, if p v then s v else 0
noncomputable def psiP : MvPolynomial σ K →ₐ[K] Polynomial (MvPolynomial σ K) :=
  aeval fun v => if p v then Polynomial.C (X v) * Polynomial.X else Polynomial.C (X v)
end ReciprocityTheory.ChartRestriction.G.T0.WH


