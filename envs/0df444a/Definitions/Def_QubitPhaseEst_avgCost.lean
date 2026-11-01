-- Prove2me | Definitions.Def_QubitPhaseEst_avgCost
-- name    : QubitPhaseEst_avgCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:18:31.243664+00:00
-- url     : https://prove2.me/theorems/e2593915-4627-4517-a42c-4d1f85822b35
-- title:
--   Averaged cost $\langle C\rangle$ of a covariant measurement, Eq. (3)
-- statement:
--   Let $R$ be the state of the $N$ qubits, $\xi$ the seed of a covariant measurement and $C:\mathbb R\to\mathbb R$ a cost function of the difference between the true phase $\phi$ and the estimate $\phi'$. With a uniform prior on $\phi$, the **averaged cost** is
--
--   $$
--   \langle C\rangle=\int_0^{2\pi}\frac{d\phi}{2\pi}\int_0^{2\pi}\frac{d\phi'}{2\pi}\,C(\phi-\phi')\,\mathrm{Tr}\bigl[U_\phi R\,U_\phi^\dagger\,U_{\phi'}\xi U_{\phi'}^\dagger\bigr].
--   $$
--
--   This is Eq. (3) with the covariant POVM $P(d\phi')=U_{\phi'}\xi U_{\phi'}^\dagger\,d\phi'/2\pi$ of Eq. (4). The **averaged cosine** $\langle c\rangle$ of Eq. (9) is $\langle C\rangle$ for $C=\cos$.
--
--   **Formalization Note** The real part of the trace is taken; it equals the trace whenever $R$ and $\xi$ are Hermitian, as in every instance of the paper. The definition is the double integral (3), not the closed forms (9)–(10), which are milestones.
-- source:
--   D'Ariano, Macchiavello, Perinotti, Optimal phase estimation for qubit mixed states, arXiv:quant-ph/0411133v3, Sec. II, Eq. (3) with Eq. (4), p. 2; Eq. (9), p. 2 (C = cos)

import Mathlib
import Definitions.Def_QubitPhaseEst_phaseShift

open scoped Matrix

namespace QubitPhaseEst

/-- **The averaged cost of a covariant measurement.** arXiv:quant-ph/0411133v3, Sec. II, Eq. (3)
with `P(dφ′)` of Eq. (4), p. 2:
`⟨C⟩ = ∫_0^{2π} dφ/2π ∫_0^{2π} dφ′/2π C(φ − φ′) Tr[U_φ R U_φ† U_φ′ ξ U_φ′†]`.

**Formalization Note.** `Tr[…]` is real for Hermitian `R`, `ξ`; `.re` makes the integrand real for
all matrices and changes no instance of the paper. The averaged cosine `⟨c⟩` of Eq. (9) is
`avgCost Real.cos R ξ`. It is deliberately defined by the double integral, not by Eq. (10). For the
costs used here the integrand is continuous, so no junk value of the integral occurs. -/
noncomputable def avgCost {N : ℕ} (C : ℝ → ℝ) (R ξ : Matrix (Qb N) (Qb N) ℂ) : ℝ :=
  (1 / (2 * Real.pi)) ^ 2 * ∫ φ in (0 : ℝ)..(2 * Real.pi), ∫ φ' in (0 : ℝ)..(2 * Real.pi),
    C (φ - φ') * (Matrix.trace (phaseShift N φ * R * (phaseShift N φ)ᴴ *
      (phaseShift N φ' * ξ * (phaseShift N φ')ᴴ))).re

end QubitPhaseEst


