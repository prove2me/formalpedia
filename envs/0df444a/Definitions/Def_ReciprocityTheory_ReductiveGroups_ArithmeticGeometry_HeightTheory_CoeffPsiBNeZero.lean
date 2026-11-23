-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffPsiBNeZero
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffPsiBNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:16.618204+00:00
-- url     : https://prove2.me/theorems/0cc5e131-05f2-4e55-a779-60851477368c
-- title:
--   Coeff Psi BNe Zero
-- statement:
--   Definitions and structural lemmas for Coeff Psi BNe Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CoeffPsiBNeZero.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0.MHF
open MvPolynomial ReciprocityTheory.MultiplicativeHeights
variable {K : Type*} [Field K] {B n : ℕ}
def bw (b : Fin B) (s : Fin B × Fin n →₀ ℕ) : ℕ := ∑ j, s (b, j)
noncomputable def psiB (b : Fin B) :
    MvPolynomial (Fin B × Fin n) K →ₐ[K] Polynomial (MvPolynomial (Fin B × Fin n) K) :=
  aeval fun v => if v.1 = b then Polynomial.C (X v) * Polynomial.X else Polynomial.C (X v)
end ReciprocityTheory.ChartRestriction.G.T0.MHF


