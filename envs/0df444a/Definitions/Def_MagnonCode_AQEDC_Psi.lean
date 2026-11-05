-- Prove2me | Definitions.Def_MagnonCode_AQEDC_Psi
-- name    : MagnonCode_AQEDC_Psi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:38:25.874057+00:00
-- url     : https://prove2.me/theorems/d1b6e337-57a6-45a2-9e57-d8e37d9f10d0
-- title:
--   Eq. (81): the one-magnon state $|\Psi\rangle$
-- statement:
--   The one-magnon state on $n$ qubits is
--
--   $$
--   |\Psi\rangle=\overline\omega\sum_{r=1}^n\omega^r s^-_r|1\rangle^{\otimes n},\qquad\omega=e^{2\pi i/n}.
--   $$
--
--   It is a highest weight vector for angular momentum $n/2-1$, and the code states of the mission are its descendants.
--
--   **Formalization Note** The prefactor is the complex conjugate $\overline\omega$, as printed; the bar is lost in the PDF's text layer. The site printed $r$ is `r.val + 1`, so the exponent of $\omega$ is `r.val + 1`.
-- source:
--   Gschwendtner, König, Şahinoğlu, Tang, Quantum Error-Detection at Low Energies, arXiv:1902.02115v2, Eq. (81), p. 54

import Mathlib
import Definitions.Def_MagnonCode_AQEDC_sMinus
import Definitions.Def_MagnonCode_AQEDC_omega

open scoped Matrix

namespace MagnonCode.AQEDC

/-- **Eq. (81)** (Gschwendtner, König, Şahinoğlu, Tang, *Quantum Error-Detection at Low Energies*, arXiv:1902.02115v2, p. 54): the one-magnon state `|Ψ⟩ = ω̄ Σ_{r=1}^n ω^r s⁻_r |1⟩^{⊗n}`.

**Formalization Note** The prefactor is the complex conjugate `ω̄`, as printed on the rendered page
(the text layer of the PDF drops the bar). Sites are `r : Fin n`, printed `r.val + 1`, hence the
exponent `r.val + 1`. Eq. (2) on p. 9 has no prefactor; (81) is the body's definition, and the
prefactor is a global phase. -/
noncomputable def Psi (n : ℕ) : (Fin n → Fin 2) → ℂ :=
  star (omega n) • ∑ r : Fin n, omega n ^ (r.val + 1) •
    (sMinus r *ᵥ Pi.single (fun _ => (1 : Fin 2)) (1 : ℂ))

end MagnonCode.AQEDC


