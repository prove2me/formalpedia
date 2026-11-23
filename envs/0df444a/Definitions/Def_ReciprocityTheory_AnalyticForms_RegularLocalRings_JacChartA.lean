-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:46:33.647576+00:00
-- url     : https://prove2.me/theorems/cfa0d44e-fe21-4e42-bfef-b767219b1ec7
-- title:
--   Jac Chart A
-- statement:
--   Definitions and structural lemmas for Jac Chart A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChartA.lean

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftMore_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R.JacobianCriterionAlt
open MvPolynomial IsLocalRing
noncomputable section
variable {n : ℕ}
def ptI (p : Fin n → ℂ) : Ideal (MvPolynomial (Fin n) ℂ) :=
  RingHom.ker (MvPolynomial.eval p : MvPolynomial (Fin n) ℂ →+* ℂ)
instance ptI_isPrime (p : Fin n → ℂ) : (ptI p).IsPrime :=
  RingHom.ker_isPrime _
abbrev localization₂ (p : Fin n → ℂ) : Type :=
  Localization.AtPrime (ptI p)
abbrev locR (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) : Type :=
  localization₂ p ⧸ Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (localization₂ p)) K
def gradP (p : Fin n → ℂ) (h : MvPolynomial (Fin n) ℂ) : Fin n → ℂ :=
  fun j => eval p (pderiv j h)
def jacS (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) : Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ (gradP p '' (K : Set (MvPolynomial (Fin n) ℂ)))
theorem mem_ptIdeal {p : Fin n → ℂ} {a : MvPolynomial (Fin n) ℂ} : a ∈ ptI p ↔ eval p a = 0 :=
  RingHom.mem_ker
def evLoc (p : Fin n → ℂ) : localization₂ p →+* ℂ :=
  IsLocalization.lift (M := (ptI p).primeCompl) (S := localization₂ p)
    (g := (eval p : MvPolynomial (Fin n) ℂ →+* ℂ))
    (fun y => isUnit_iff_ne_zero.mpr fun h => y.2 (mem_ptIdeal.mpr h))
theorem evLoc_algebraMap (p : Fin n → ℂ) (a : MvPolynomial (Fin n) ℂ) :
    evLoc p (algebraMap _ (localization₂ p) a) = eval p a :=
  IsLocalization.lift_eq _ _
variable {p : Fin n → ℂ} (K : Ideal (MvPolynomial (Fin n) ℂ))
abbrev psi (p : Fin n → ℂ) (K : Ideal (MvPolynomial (Fin n) ℂ)) : MvPolynomial (Fin n) ℂ →+* locR K p :=
  (Ideal.Quotient.mk _).comp (algebraMap _ (localization₂ p))
def evRing (hK : K ≤ ptI p) : locR K p →+* ℂ :=
  Ideal.Quotient.lift _ (evLoc p) (by
    intro x hx
    have : Ideal.map (algebraMap _ (localization₂ p)) K ≤ RingHom.ker (evLoc p) := by
      rw [Ideal.map_le_iff_le_comap]
      intro k hk
      rw [Ideal.mem_comap, RingHom.mem_ker, evLoc_algebraMap]
      exact mem_ptIdeal.mp (hK hk)
    exact RingHom.mem_ker.mp (this hx))
end
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt


