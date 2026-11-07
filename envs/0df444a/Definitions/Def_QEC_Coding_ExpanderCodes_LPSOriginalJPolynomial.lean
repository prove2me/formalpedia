-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:32:34.893878+00:00
-- url     : https://prove2.me/theorems/d41f9fcb-11fb-4c91-84ab-716fffdc241a
-- title:
--   LPSOriginal JPolynomial
-- statement:
--   Definitions and structural lemmas for LPSOriginal JPolynomial, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJPolynomial.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Separation.Connected
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilation_Gamma0_le_translated_SL

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section
def lpsOriginalE4CubePower (m : ℕ) : ModularForm 𝒮ℒ (12*(m:ℤ)) :=
  ModularForm.mcast (by push_cast; ring) (ModularForm.E₄.pow (3*m))
def lpsOriginalJPolynomialEvalHom : Polynomial ℂ →+* (ℍ→ℂ) :=
  RingHom.pi (fun τ => Polynomial.evalRingHom (lpsOriginalJInvariant τ))
def lpsOriginalDeltaDilatedForm (N : ℕ) (hN : 0<N) :
    ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 12 :=
  let f := CuspForm.translate CuspForm.discriminant (lpsE2AffineMatrix N hN 0)
  { toFun := f
    slash_action_eq' g hg := f.slash_action_eq' g
      (lpsOriginalJDilation_Gamma0_le_translated_SL N hN hg)
    holo' := f.holo'
    bdd_at_cusps' hc := ModularFormClass.bdd_at_cusps f
      (hc.mono (lpsOriginalJDilation_Gamma0_le_translated_SL N hN)) }
def lpsOriginalDeltaDilatedNorm (N : ℕ) [NeZero N] (hN : 0<N) :
    ModularForm 𝒮ℒ (12*(Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ):ℤ)) :=
  ModularForm.norm 𝒮ℒ (lpsOriginalDeltaDilatedForm N hN)
end
end QEC.Coding.TannerLiftedProduct


