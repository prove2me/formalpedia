-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:04:12.436374+00:00
-- url     : https://prove2.me/theorems/802cafff-bba5-4967-8667-a5e23262d522
-- title:
--   LPSOriginal Level Cusp Arithmetic
-- statement:
--   Definitions and structural lemmas for LPSOriginal Level Cusp Arithmetic, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelCuspArithmetic.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
def lpsOriginalCuspLevelDegree (N M : ℕ) [NeZero N] [NeZero M] (ρ : SL(2, ℤ)) : ℕ :=
  lpsOriginalCuspWidthNat M ρ / lpsOriginalCuspWidthNat N ρ
def lpsOriginalInteriorForgetLevel (N M : ℕ) (hNM : N ∣ M) :
    MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) ℍ →
      MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ :=
  Quotient.map id (by
    intro a b hab
    change MulAction.orbitRel (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) ℍ a b at hab
    change MulAction.orbitRel (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ a b
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hab ⊢
    obtain ⟨g, hg⟩ := hab
    exact ⟨⟨g.val, (Subgroup.map_mono (lpsGamma0_level_le N M hNM)) g.property⟩, hg⟩)
def lpsOriginalCuspForgetLevel (N M : ℕ) (hNM : N ∣ M) :
    CuspOrbits (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) →
      CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) :=
  Quotient.map
    (fun c : cuspsSubMulAction (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) =>
      (⟨c.val, c.property.mono (Subgroup.map_mono (lpsGamma0_level_le N M hNM))⟩ :
        cuspsSubMulAction (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))))
    (by
      intro a b hab
      change MulAction.orbitRel (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ))
        (cuspsSubMulAction (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ))) a b at hab
      change MulAction.orbitRel (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
        (cuspsSubMulAction (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) _ _
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hab ⊢
      obtain ⟨g, hg⟩ := hab
      refine ⟨⟨g.val, (Subgroup.map_mono (lpsGamma0_level_le N M hNM)) g.property⟩, ?_⟩
      apply Subtype.ext
      exact congrArg (fun x : cuspsSubMulAction
        (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) => (x.val : OnePoint ℝ)) hg)
def lpsOriginalFilledForgetLevel (N M : ℕ) (hNM : N ∣ M) :
    LPSOriginalFilledCurve M → LPSOriginalFilledCurve N :=
  Sum.map (lpsOriginalInteriorForgetLevel N M hNM) (lpsOriginalCuspForgetLevel N M hNM)
end
end QEC.Coding.TannerLiftedProduct


