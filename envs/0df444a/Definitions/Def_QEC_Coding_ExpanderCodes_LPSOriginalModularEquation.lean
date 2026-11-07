-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:50:55.284247+00:00
-- url     : https://prove2.me/theorems/968c3cf8-4a9d-4cb2-896f-838d39c05e01
-- title:
--   LPSOriginal Modular Equation
-- statement:
--   Definitions and structural lemmas for LPSOriginal Modular Equation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilation_Gamma0_le_translated_SL
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelOne_unique_polynomial_j

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section
def lpsOriginalE4DilatedForm (N : ℕ) (hN : 0<N) :
    ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 4 :=
  let f := ModularForm.translate ModularForm.E₄ (lpsE2AffineMatrix N hN 0)
  { toFun := f
    slash_action_eq' g hg := f.slash_action_eq' g
      (lpsOriginalJDilation_Gamma0_le_translated_SL N hN hg)
    holo' := f.holo'
    bdd_at_cusps' hc := f.bdd_at_cusps'
      (hc.mono (lpsOriginalJDilation_Gamma0_le_translated_SL N hN)) }
def lpsOriginalJNumeratorForm (N : ℕ) (hN : 0<N) :
    ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 12 :=
  (N:ℂ)^2 • ModularForm.mcast (by norm_num) ((lpsOriginalE4DilatedForm N hN).pow 3)
def lpsOriginalModularNormInput (N : ℕ) (hN : 0<N) (c : ℂ) :
    ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 12 :=
  lpsOriginalJNumeratorForm N hN-c • lpsOriginalDeltaDilatedForm N hN
def lpsOriginalModularNorm (N : ℕ) [NeZero N] (hN : 0<N) (c : ℂ) :
    ModularForm 𝒮ℒ (12*(Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ):ℤ)) :=
  ModularForm.norm 𝒮ℒ (lpsOriginalModularNormInput N hN c)
lemma lpsOriginalModularNorm_unique_polynomial (N : ℕ) [NeZero N] (hN : 0<N) (c : ℂ) :
    ∃! P : Polynomial ℂ,
      P.natDegree≤Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∧
      ∀ τ : ℍ, lpsOriginalModularNorm N hN c τ=
        ModularForm.discriminant τ^(Nat.card (𝒮ℒ ⧸
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))*
          P.eval (lpsOriginalJInvariant τ) :=
  lpsOriginalLevelOne_unique_polynomial_j _ (lpsOriginalModularNorm N hN c)
def lpsOriginalModularCosetPolynomial (N : ℕ) [NeZero N] (hN : 0<N) (τ : ℍ) :
    Polynomial ℂ := by
  classical
  letI := Fintype.ofFinite (𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  exact ∏ q : (𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ),
    (Polynomial.C (SlashInvariantForm.quotientFunc (lpsOriginalJNumeratorForm N hN) q τ)-
      Polynomial.X*Polynomial.C
        (SlashInvariantForm.quotientFunc (lpsOriginalDeltaDilatedForm N hN) q τ))
def lpsOriginalModularNormCoefficient (N : ℕ) [NeZero N] (hN : 0<N) (c : ℂ) :
    Polynomial ℂ :=
  Classical.choose (lpsOriginalModularNorm_unique_polynomial N hN c).exists
def lpsOriginalModularEquationComplex (N : ℕ) [NeZero N] (hN : 0<N) :
    Polynomial (Polynomial ℂ) := by
  classical
  let r := Nat.card (𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  exact ∑ i : Fin (r+1),
    Polynomial.C (lpsOriginalModularNormCoefficient N hN (i.val:ℂ))*
      (Lagrange.basis (Finset.univ:Finset (Fin (r+1))) (fun j => (j.val:ℂ)) i).map Polynomial.C
end
end QEC.Coding.TannerLiftedProduct


