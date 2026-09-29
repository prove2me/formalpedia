-- Prove2me | Definitions.Def_MTT_EigenformCoefficientCompletion
-- name    : MTT_EigenformCoefficientCompletion
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-23T21:50:50.631927+00:00
-- url     : https://prove2.me/theorems/c81c0f91-26a1-4450-9131-36307941efd6
-- title:
--   The integral completion of an eigenform coefficient field
-- statement:
--   For a normalized algebraic eigenform $f$ and a chosen embedding into $\mathbb C_p$, let $K_f$ be its canonical coefficient field and let $\mathfrak p_f$ be the canonical prime selected by that embedding. Define
--
--   $$\widehat{\mathcal O}_{f,\mathfrak p_f}
--   =\varprojlim_n\mathcal O_{K_f}/\mathfrak p_f^n.$$
--
--   This is the actual adic completion, not additional representation data. Its canonical reduction is the projection
--
--   $$\widehat{\mathcal O}_{f,\mathfrak p_f}\longrightarrow
--   \mathcal O_{K_f}/\mathfrak p_f.$$
--
--   The definition includes proofs that this projection is surjective and its composite with the coefficient-ring inclusion is the original ideal quotient map. These constructions connect integral representations to exactly the coefficient residue field chosen by the mission.
-- source:
--   Deligne–Serre, Formes modulaires de poids 1, Ann. Sci. ENS 7 (1974), Theorem 6.1, p.520 (all weights at least two, arbitrary nebentype and any coefficient number field containing the eigenvalues), and §6.12, p.523 (stable integral lattice and reduction). Arithmetic Frobenius convention: footnote on p.513. https://publications.ias.edu/sites/default/files/Number24.pdf. The integral representation and its residual reduction are used in Kriz–Nordentoft, arXiv:2310.20678v3, §4, equation (4.2).

import Definitions.Def_MTT_EigenformCoefficientResidueField
import Mathlib.RingTheory.AdicCompletion.Algebra

set_option autoImplicit false
noncomputable section

open NumberField

namespace MTT.Eigenform

/-- The integral completion of the coefficient field at the chosen place. -/
abbrev coefficientCompletion
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :=
  AdicCompletion (f.coefficientPrime ιp) (𝓞 f.coefficientField)

/-- Reduction from the canonical integral completion to the canonical residue field. -/
def coefficientReduction
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    f.coefficientCompletion ιp →+* f.coefficientResidueField ιp :=
  (AdicCompletion.evalOneₐ (f.coefficientPrime ιp)).toRingHom

@[simp]
theorem coefficientReduction_algebraMap
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p])
    (x : 𝓞 f.coefficientField) :
    f.coefficientReduction ιp (algebraMap _ (f.coefficientCompletion ιp) x) =
      Ideal.Quotient.mk (f.coefficientPrime ιp) x := rfl

theorem coefficientReduction_surjective
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    Function.Surjective (f.coefficientReduction ιp) :=
  AdicCompletion.evalOneₐ_surjective (f.coefficientPrime ιp)

end MTT.Eigenform


