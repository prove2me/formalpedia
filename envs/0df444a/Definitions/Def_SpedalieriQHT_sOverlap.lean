-- Prove2me | Definitions.Def_SpedalieriQHT_sOverlap
-- name    : SpedalieriQHT_sOverlap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:47:13.596878+00:00
-- url     : https://prove2.me/theorems/e712e33f-cc8c-486b-9158-4b5bf249aa1b
-- title:
--   The s-overlap $C_s=\operatorname{Tr}(\rho_0^s\rho_1^{1-s})$
-- statement:
--   For bounded operators $\rho_0,\rho_1$ on a complex Hilbert space and a real number $s$, the **s-overlap** is
--   $$
--   C_s=\operatorname{Tr}\bigl(\rho_0^{\,s}\,\rho_1^{\,1-s}\bigr),
--   $$
--   where the real powers are taken by the continuous functional calculus. For positive $\rho$, $\rho^0=I$; hence for density operators $C_0=\operatorname{Tr}\rho_1=1$, the convention of footnote [20].
--
--   The s-overlap is the quantity inside the quantum Hoeffding bound (15); for two Gaussian states the paper computes it in closed form.
--
--   **Formalization Note** The trace is the basis-sum trace $\sum_i\langle e_i,Te_i\rangle$ of `Def_QAlgorithms_Papers_Independent_Next46_P02`, and Lean records its real part ($C_s$ is real for states). That $\rho_0^s\rho_1^{1-s}$ is trace class for states is a proof obligation, not part of the definition. The definition is not specialized to pure states.
-- source:
--   Spedalieri–Braunstein, Asymmetric quantum hypothesis testing with Gaussian states, arXiv:1407.0884v3, Sec. II B, Eq. (16), p.3; footnote [20], p.8

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02

open QAlgorithms.Papers.Independent.Next46.P02

namespace SpedalieriQHT

/-- The s-overlap `C_s = Tr(ρ0^s ρ1^{1−s})`.

Spedalieri–Braunstein, arXiv:1407.0884v3, Sec. II B, Eq. (16), p.3: "C_s := Tr(ρ0^s ρ1^{1−s})
is the 's-overlap' between the single-copy states ρ0 and ρ1."

**Formalization Note.** Defined for all bounded operators `ρ0, ρ1` on a complex Hilbert space;
nothing here is special to pure states. The powers are Mathlib's continuous functional calculus
`CFC.rpow` with real exponent, for which `ρ ^ (0 : ℝ) = 1` on positive `ρ` (`CFC.rpow_zero`),
the paper's convention in footnote [20], p.8 ("P(r, 0) = −ln C0 = 0", i.e. `C_0 = Tr ρ1 = 1`).
The trace is the published basis-sum trace `basisOperatorTrace` (`∑' i, ⟨eᵢ, T eᵢ⟫`); that
`ρ0^s ρ1^{1−s}` is trace class for states is a proof obligation, not a hypothesis. `C_s` is
real for states, and Lean records its real part. -/
noncomputable def sOverlap {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (ρ0 ρ1 : H →L[ℂ] H) (s : ℝ) : ℝ :=
  (basisOperatorTrace (ρ0 ^ s * ρ1 ^ (1 - s))).re

end SpedalieriQHT


