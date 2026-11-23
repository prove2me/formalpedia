-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpLatticeTransfer
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpLatticeTransfer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:10.608514+00:00
-- url     : https://prove2.me/theorems/b5dd2e61-cde8-4012-8634-983313450fe3
-- title:
--   Perp Lattice Transfer
-- statement:
--   Definitions and structural lemmas for Perp Lattice Transfer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpLatticeTransfer.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpBasisExistence
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_integer_smul_eq_coe_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero


set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)
variable {n : ℕ} (β : Fin n → Fin r → E) (ξ : Fin r → E)
lemma smul_O_E (a : 𝓞 E) (x : E) : a • x = (a : E) * x := by
  rw [Algebra.smul_def]
def Tmap : ((Fin n → E) × E) →ₗ[𝓞 E] (Fin r → E) where
  toFun p := ∑ k, p.1 k • β k + p.2 • ξ
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' a p := by
    simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]
    rw [integer_smul_eq_coe_smul a p.1, integer_smul_eq_coe_smul a (∑ k, p.1 k • β k + p.2 • ξ), smul_O_E]
    simp only [Pi.smul_apply, smul_eq_mul, smul_add, Finset.smul_sum, mul_smul]
def Sform : ReciprocityTheory.MultiplicativeHeights.HermForm E n where
  c := (IsCMField.complexConj E).toRingEquiv.toRingHom
  c_invol x := IsCMField.complexConj_apply_apply E x
  c_emb σ x := IsCMField.complexEmbedding_complexConj E σ x
  G := Matrix.of fun a b => herm X.Gm (β b) (β a)
  G_herm a b := HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm (β b) (β a)
end
end ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer


