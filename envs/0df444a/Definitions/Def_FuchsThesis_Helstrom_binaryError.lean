-- Prove2me | Definitions.Def_FuchsThesis_Helstrom_binaryError
-- name    : FuchsThesis_Helstrom_binaryError
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:22.391919+00:00
-- url     : https://prove2.me/theorems/46239079-1f11-4676-a420-ceaca7a6f6e1
-- title:
--   Error probability of a binary-valued POVM, $\pi_0\,\mathrm{tr}(\hat\rho_0\hat E_1) + \pi_1\,\mathrm{tr}(\hat\rho_1\hat E_0)$ (eq. 3.10)
-- statement:
--   Let $\{\hat E_0, \hat E_1\}$ be a binary-valued POVM, used as a "measurement + guess": on outcome $0$ the observer chooses $\hat\rho_0$, on outcome $1$ the state $\hat\rho_1$. With priors $\pi_0, \pi_1$ the expected probability of error of this decision is
--
--   $$
--   P_e = \pi_0\,\mathrm{tr}(\hat\rho_0\hat E_1) + \pi_1\,\mathrm{tr}(\hat\rho_1\hat E_0).
--   $$
--
--   Every measurement followed by a guess can be summarized by such a binary POVM, which is why minimizing this quantity over binary POVMs gives the same value as the quantum error probability (3.9).
--
--   **Formalization Note** The binary POVM is a family `E : Fin 2 → Matrix n n ℂ` with $\hat E_0 = E\,0$, $\hat E_1 = E\,1$; traces are real parts.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (3.10), p.44 (PDF p.53)

import Mathlib
import Definitions.Def_FuchsVdGraaf_outcomeDist

namespace FuchsThesis.Helstrom

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, eq. (3.10), p.44 (PDF p.53): for a binary-valued POVM `{Ê₀, Ê₁}`, where
outcome `0` is read as "the state is `ρ̂₀`" and outcome `1` as "the state is `ρ̂₁`", the expected
probability of error is `P_e = π₀ tr(ρ̂₀Ê₁) + π₁ tr(ρ̂₁Ê₀)`.

**Formalization Note.** The binary POVM is `E : Fin 2 → Matrix n n ℂ` with `Ê₀ = E 0`,
`Ê₁ = E 1`; `tr(ρ̂Ê)` is the real part of the trace (`FuchsVdGraaf.outcomeDist`). -/
noncomputable def binaryError {n : Type} [Fintype n] (π0 π1 : ℝ) (ρ0 ρ1 : Matrix n n ℂ)
    (E : Fin 2 → Matrix n n ℂ) : ℝ :=
  π0 * FuchsVdGraaf.outcomeDist ρ0 E 1 + π1 * FuchsVdGraaf.outcomeDist ρ1 E 0

end FuchsThesis.Helstrom


