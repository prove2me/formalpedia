-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsIntMultiple
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsIntMultiple
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-27T05:38:58.583872+00:00
-- url     : https://prove2.me/theorems/76cd3956-e0fc-52ab-a3a9-40f9233e79ba
-- title:
--   Exists Int Multiple
-- statement:
--   Definitions and structural lemmas for Exists Int Multiple, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsIntMultiple.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussAbsMulSupportFinite
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply


set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]
noncomputable def mS {κ : Type} (S : Finset (κ →₀ ℕ)) (j : Fin S.card) : κ →₀ ℕ :=
  (S.equivFin.symm j : κ →₀ ℕ)
noncomputable def polyOf {κ : Type} (S : Finset (κ →₀ ℕ)) (p : Fin S.card → K) : MvPolynomial κ K :=
  ∑ j, MvPolynomial.monomial (mS S j) (p j)
def coordVec {κ : Type} {T : Finset (κ →₀ ℕ)} {r : ℕ} (e : T ≃ Fin r) (P : MvPolynomial κ K) :
    Fin r → K :=
  fun i => P.coeff (e.symm i : κ →₀ ℕ)
noncomputable def bG {κ : Type} (G : MvPolynomial κ K) (S : Finset (κ →₀ ℕ)) {T : Finset (κ →₀ ℕ)}
    {r : ℕ} (e : T ≃ Fin r) (j : Fin S.card) : Fin r → K :=
  coordVec e (G * MvPolynomial.monomial (mS S j) 1)
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
noncomputable def phiB {k r : ℕ} (b : Fin k → Fin r → K) : (Fin k → K) →+ (Fin r → K) :=
  AddMonoidHom.mk' (fun p => ∑ j, p j • b j) (by
    intro p q
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib])
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField
variable {K : Type} [Field K] [NumberField K]
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors


