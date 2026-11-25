-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreSide
-- name    : Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreSide
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T13:07:40.151148+00:00
-- url     : https://prove2.me/theorems/6fd2e384-d92d-5b6c-a894-cf36d0bd5221
-- title:
--   Core Side
-- statement:
--   Definitions and structural lemmas for Core Side, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreSide.lean

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreStar
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreGen
import Theorems.Thm_PI_FockOneDegW_Core_key
import Theorems.Thm_PositivityTheory_KReal_fockAct2_unit
import Theorems.Thm_PositivityTheory_KReal_twAct_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
namespace PositivityTheory.KReal
namespace GoodSideLattices
variable {p q r s : ℕ}
def sd_hA (p q r s d : ℕ) : Submodule ℂ (FV p q r s) := homog (Ix p q × Ix r s) d
instance sd_hA_fd (d : ℕ) : FiniteDimensional ℂ (sd_hA p q r s d) :=
  Module.Finite.iff_fg.2 (homogeneousSubmodule_fg (Ix p q × Ix r s) ℂ d)
def sd_fvTw (p q r s : ℕ) (τ : ℂ) : Mat r s →ₗ[ℂ] Module.End ℂ (FV p q r s) := twAct p q r s τ
theorem sd_fvTw_apply (τ : ℂ) (W : Mat r s) (u : FV p q r s) :
    sd_fvTw p q r s τ W u = fvAct2 p q r s W u + (τ * W.trace) • u :=
  twAct_apply p q r s τ W u
theorem isHomogeneous_X_mul_pderiv {σ : Type} (i j : σ) {n : ℕ} {φ : MvPolynomial σ ℂ}
    (h : φ.IsHomogeneous n) : (X i * pderiv j φ).IsHomogeneous n := by
  have e : X i * pderiv j φ = pderiv j (X i * φ) - pderiv j (X i) * φ := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring
  rw [e, ← mem_homogeneousSubmodule]
  refine Submodule.sub_mem _ ?_ ?_
  · rw [mem_homogeneousSubmodule]
    simpa using ((isHomogeneous_X (R := ℂ) i).mul h).pderiv (i := j)
  · rw [mem_homogeneousSubmodule]
    by_cases hij : j = i
    · subst hij
      simpa using h
    · rw [pderiv_X_of_ne (Ne.symm hij), zero_mul]
      exact isHomogeneous_zero _ _ _
theorem omE_mem_homogeneousSubmodule_of_sameBlock {d : ℕ} (i : Ix p q) {a b : Ix r s} (hab : sameBlock a b)
    {x : Pol p q r s} (hx : x ∈ homogeneousSubmodule (Ix p q × Ix r s) ℂ d) :
    omE (i, a) (i, b) x ∈ homogeneousSubmodule (Ix p q × Ix r s) ℂ d := by
  have hl : linePos (i, a) = linePos (i, b) := by
    rcases i with i | i <;> rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock, linePos]
  rw [mem_homogeneousSubmodule] at hx
  simp only [omE, LinearMap.add_apply, Module.End.mul_apply]
  refine Submodule.add_mem _ ?_ ?_
  · simp only [raiB, lowB, ← hl]
    split_ifs with h
    · rw [LinearMap.mulLeft_apply, mem_homogeneousSubmodule]
      exact isHomogeneous_X_mul_pderiv _ _ hx
    · rw [LinearMap.neg_apply, LinearMap.mulLeft_apply]
      refine Submodule.neg_mem _ ?_
      rw [mem_homogeneousSubmodule]
      simpa using ((isHomogeneous_X (R := ℂ) (i, b)).mul hx).pderiv (i := (i, a))
  · split_ifs
    · exact Submodule.smul_mem _ _ ((mem_homogeneousSubmodule _ _).2 hx)
    · exact Submodule.zero_mem _
theorem sd_fvTw_mem (τ : ℂ) (d : ℕ) {a b : Ix r s} (hab : sameBlock a b) :
    ∀ x ∈ sd_hA p q r s d, sd_fvTw p q r s τ (Eab a b) x ∈ sd_hA p q r s d := by
  intro x hx
  rw [sd_fvTw_apply]
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ hx)
  have e := fockAct2_unit (p := p) (q := q) a b (show Pol p q r s from x)
  have key : (fockAct2 p q r s (Eab a b)) (show Pol p q r s from x) ∈
      homogeneousSubmodule (Ix p q × Ix r s) ℂ d := by
    rw [e]
    exact Submodule.sum_mem _ (fun i _ => omE_mem_homogeneousSubmodule_of_sameBlock i hab hx)
  exact key
def sd_rhoA (p q r s : ℕ) (τ : ℂ) (d : ℕ) (a b : Ix r s) : Module.End ℂ (sd_hA p q r s d) :=
  if h : sameBlock a b then (sd_fvTw p q r s τ (Eab a b)).restrict (sd_fvTw_mem τ d h) else 0
def sd_fvMk (p q r s : ℕ) (c : ℂ) : FV p q r s →ₗ[ℂ] ThC p q r s c := thMkC p q r s c
end GoodSideLattices
end PositivityTheory.KReal
end


