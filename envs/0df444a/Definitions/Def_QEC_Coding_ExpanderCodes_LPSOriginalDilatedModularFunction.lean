-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:02:17.84367+00:00
-- url     : https://prove2.me/theorems/b01cedf8-df64-427c-97cd-86f404c9e648
-- title:
--   LPSOriginal Dilated Modular Function
-- statement:
--   Definitions and structural lemmas for LPSOriginal Dilated Modular Function, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
def lpsOriginalJDilated (N : ℕ) (hN : 0<N) (τ : ℍ) : ℂ :=
  lpsOriginalJInvariant (lpsE2AffineMatrix N hN 0 • τ)
lemma lpsOriginalJDilated_integral_Gamma0_invariant (N : ℕ) (hN : 0<N)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    lpsOriginalJDilated N hN (γ•τ)=lpsOriginalJDilated N hN τ := by
  rw [CongruenceSubgroup.Gamma0_mem] at hγ
  have hdvd : (N:ℤ)∣γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) N).mp hγ
  obtain ⟨k,hk⟩ := hdvd
  let δ := lpsE2DilationConjugate N γ k hk
  have ha := lpsE2DilationConjugate_action N hN γ δ k hk rfl rfl rfl rfl τ
  change lpsOriginalJInvariant (lpsE2AffineMatrix N hN 0 • (γ•τ))=_
  rw [←ha]
  exact lpsOriginalJInvariant_SL_invariant (Matrix.SpecialLinearGroup.mapGL ℝ δ)
    ⟨δ,rfl⟩ (lpsE2AffineMatrix N hN 0 • τ)
lemma lpsOriginalJDilated_Gamma0_invariant (N : ℕ) (hN : 0<N)
    (g : GL (Fin 2) ℝ) (hg : g∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (τ : ℍ) : lpsOriginalJDilated N hN (g•τ)=lpsOriginalJDilated N hN τ := by
  obtain ⟨γ,hγ,rfl⟩ := hg
  exact lpsOriginalJDilated_integral_Gamma0_invariant N hN γ hγ τ
def lpsOriginalJDilatedQuotient (N : ℕ) (hN : 0<N) :
    MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → ℂ :=
  Quotient.lift (lpsOriginalJDilated N hN) (by
    intro τ σ h
    change MulAction.orbitRel (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ τ σ at h
    rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff] at h
    obtain ⟨g,hg⟩ := h
    rw [←hg]
    exact lpsOriginalJDilated_Gamma0_invariant N hN g.val g.property σ)
def lpsOriginalJDilationCuspE4 (N : ℕ) (hN : 0<N) (ρ : SL(2,ℤ)) :=
  ModularForm.translate (ModularForm.translate ModularForm.E₄ (lpsE2AffineMatrix N hN 0))
    (Matrix.SpecialLinearGroup.mapGL ℝ ρ)
def lpsOriginalJDilationCuspDelta (N : ℕ) (hN : 0<N) (ρ : SL(2,ℤ)) :=
  CuspForm.translate (CuspForm.translate CuspForm.discriminant (lpsE2AffineMatrix N hN 0))
    (Matrix.SpecialLinearGroup.mapGL ℝ ρ)
def lpsOriginalJDilationCuspCoefficient (N : ℕ) (hN : 0<N) (ρ : SL(2,ℤ)) (q : ℂ) : ℂ :=
  (N:ℂ)^2 * (UpperHalfPlane.cuspFunction (lpsOriginalCuspGroup N ρ).strictWidthInfty
    (lpsOriginalJDilationCuspE4 N hN ρ) q)^3 /
    UpperHalfPlane.cuspFunction (lpsOriginalCuspGroup N ρ).strictWidthInfty
      (lpsOriginalJDilationCuspDelta N hN ρ) q
def lpsOriginalFilledJDilated (N : ℕ) (hN : 0<N) : LPSOriginalFilledCurve N → ℂ :=
  Sum.elim (lpsOriginalJDilatedQuotient N hN) (fun _ => 0)
end
end QEC.Coding.TannerLiftedProduct


