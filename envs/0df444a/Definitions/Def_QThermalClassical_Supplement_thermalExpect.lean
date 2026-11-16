-- Prove2me | Definitions.Def_QThermalClassical_Supplement_thermalExpect
-- name    : QThermalClassical_Supplement_thermalExpect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:36:22.295808+00:00
-- url     : https://prove2.me/theorems/92b807e5-7a8e-43ee-aa15-e8b7e8a21a8b
-- title:
--   Thermal expectation $\langle O\rangle_\beta$
-- statement:
--   The **thermal expectation** of an operator $O$ in the Gibbs state of $H$ at inverse temperature $\beta$ is
--   $$
--   \langle O\rangle_\beta=\mathrm{Tr}\big(O\,\rho_\beta(H)\big).
--   $$
--   It is a complex number; for a product $AB$ of Hermitian observables it need not be real.
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), §5.4, Lemma 26, eq. (280), p.58; Theorem 5, eq. (42), p.17

import Mathlib
import Definitions.Def_QThermalClassical_gibbs

set_option autoImplicit false

namespace QThermalClassical.Supplement

/-- The thermal expectation `⟨O⟩_β = Tr(O ρ_β(H))` of an operator `O` in the Gibbs state of `H`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), §5.4 (Lemma 26, eq. (280), p.58) and Theorem 5, eq. (42), p.17.

**Formalization Note.** A complex number; for the non-Hermitian product `AB` of (42) it need
not be real, and (42) bounds its modulus. -/
noncomputable def thermalExpect {Q : Type} [Fintype Q] [DecidableEq Q] (H : Op Q) (β : ℝ)
    (O : Op Q) : ℂ :=
  (O * gibbs H β).trace

end QThermalClassical.Supplement


