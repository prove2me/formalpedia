-- Prove2me | Definitions.Def_QAlgorithms_Defs_RealLabelRegisters
-- name    : QAlgorithms_Defs_RealLabelRegisters
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:37:06.63878+00:00
-- url     : https://prove2.me/theorems/7924809d-28d6-4adb-b07b-58419ce222be
-- title:
--   RealLabelRegisters
-- statement:
--   RealLabelRegisters
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\RealLabelRegisters.lean

import Mathlib

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.RealRegisters

/-- Abbreviation of Mathlib lp (fun _ : Label => Complex) 2 with exact-real location/value tuple basis labels. ket=lp.single 2 label 1; states may have countable support. Finite source meshes embed orthogonally. No uniform probability on all real labels or finite-qubit encoding of all reals. Source: arxiv-2007.10253v3 PDF p.3; arxiv-2510.08509v1 PDF p.8. -/
abbrev Hilbert (Label : Type*) := lp (fun _ : Label => ℂ) 2

/-- Norm-one predicate on general Hilbert spaces. Frozen IsState is reused on finite EuclideanSpace; its Fintype signature cannot accept infinite atomic lp or continuum Lp. Source: arxiv-2007.10253v3 PDF p.3; arxiv-2510.08509v1 PDF p.8; arxiv-2503.24332v2 PDF p.13. -/
def IsUnitVector {H : Type*} [NormedAddCommGroup H] (psi : H) : Prop := ‖psi‖ = 1

/-- Construct PMF with atoms |psi(label)|^2 from square summability and norm one, including countable support on possibly uncountable labels. Lawful measurable instruments are required for adaptive/coarse observations. Source: arxiv-2007.10253v3 PDF p.3; arxiv-2510.08509v1 PDF p.8. -/
def atomicBornLaw {Label : Type*} (psi : Hilbert Label) (hpsi : IsUnitVector psi) : PMF Label := by
  classical
  have hs : ∑' i, ‖psi i‖ ^ 2 = 1 := by
    have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) psi
    norm_num only [ENNReal.toReal_ofNat, Real.rpow_two] at h
    rw [← h, hpsi]
    norm_num
  have he : ∑' i, ENNReal.ofReal (‖psi i‖ ^ 2) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) (by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (lp.memℓp psi).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)), hs]
    simp
  exact ⟨fun i => ENNReal.ofReal (‖psi i‖ ^ 2), he ▸ ENNReal.summable.hasSum⟩

example {Label : Type*} (psi : Hilbert Label) (hpsi : IsUnitVector psi) :
    ∑' i, atomicBornLaw psi hpsi i = 1 := (atomicBornLaw psi hpsi).tsum_coe

example {H : Type*} [NormedAddCommGroup H] : ¬ IsUnitVector (0 : H) := by
  simp [IsUnitVector]

end QAlgorithms.RealRegisters


