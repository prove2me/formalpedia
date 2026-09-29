-- Prove2me | Definitions.Def_MTT_EigenformCoefficientResidueField
-- name    : MTT_EigenformCoefficientResidueField
-- status  : Definition
-- author  : @davidloeffler
-- created : 2026-09-20T11:10:50.38115+00:00
-- url     : https://prove2.me/theorems/a485a2f4-4a2d-45de-99b1-e2169b0a7f1e
-- title:
--   The finite coefficient residue field of an MTT eigenform
-- statement:
--   Let $f$ be an MTT eigenform, let $K_f$ be its coefficient field, and
--   let $\iota_p:\overline{\mathbf Q}\hookrightarrow\mathbf C_p$ select the prime
--   $\lambda_{\iota_p}\subset\mathcal O_{K_f}$. Define the canonical coefficient
--   residue field
--   $$
--   k_{f,\iota_p}=\mathcal O_{K_f}/\lambda_{\iota_p}.
--   $$
--   The definition bundle derives its field structure from maximality of
--   $\lambda_{\iota_p}$ and its finite type from finite quotients of rings of
--   integers. Neither structure is additional data attached to $f$.
-- source:
--   Standard residue field of a number field at a nonzero prime ideal.

import Definitions.Def_MTT_EigenformCoefficientPrime
import Theorems.Thm_MTT_Eigenform_coefficientPrime_isMaximal
import Theorems.Thm_MTT_Eigenform_coefficientPrime_ne_bot
import Theorems.Thm_MTT_numberField_coefficientField
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients

set_option autoImplicit false
noncomputable section

open NumberField

namespace MTT.Eigenform

/-- The residue ring of the coefficient field at the prime selected by a
`p`-adic embedding. -/
abbrev coefficientResidueField
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :=
  (𝓞 f.coefficientField) ⧸ f.coefficientPrime ιp

/-- The coefficient residue ring is a field. This is a derived structure,
not additional data attached to the eigenform. -/
noncomputable abbrev coefficientResidueFieldField
    {N k p : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    Field (f.coefficientResidueField ιp) := by
  letI : (f.coefficientPrime ιp).IsMaximal :=
    f.coefficientPrime_isMaximal hN hk ιp
  exact Ideal.Quotient.field (f.coefficientPrime ιp)

/-- The coefficient residue field is finite. This is a derived structure,
not additional data attached to the eigenform. -/
noncomputable abbrev coefficientResidueFieldFintype
    {N k p : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    Fintype (f.coefficientResidueField ιp) := by
  letI : NumberField f.coefficientField :=
    MTT.numberField_coefficientField hN hk ι f
  letI : Finite (f.coefficientResidueField ιp) :=
    Ring.HasFiniteQuotients.finiteQuotient
      (f.coefficientPrime_ne_bot ιp)
  exact Fintype.ofFinite _

end MTT.Eigenform


