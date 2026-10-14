-- Prove2me | Definitions.Def_HeathcoteUnbounded_PositionDomain
-- name    : HeathcoteUnbounded_PositionDomain
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-13T14:33:36.990921+00:00
-- url     : https://prove2.me/theorems/dc1f0ebc-204b-4e35-aa97-a23e73612247
-- title:
--   Domain $D(Q)$ of the position operator on $L^2(\mathbb R)$, eq. (3)
-- statement:
--   The position operator $Q$ on $L^2(\mathbb R)$ acts by $(Q\psi)(x)=x\,\psi(x)$. Its domain, equation (3) of the source, is
--
--   $$D(Q)=\Big\{\psi\in L^2(\mathbb R)\ :\ \int_{\mathbb R} x^2\,|\psi(x)|^2\,dx<\infty\Big\},$$
--
--   i.e. exactly those square-integrable $\psi$ for which $x\psi(x)$ is again square-integrable.
--
--   **Formalization Note** $D(Q)$ is a subset of Mathlib's `Lp ℂ 2 volume` on `ℝ`; the integral is a Lebesgue integral in $[0,\infty]$ of $|x|^2|\psi(x)|^2$, which does not depend on the chosen representative.
-- source:
--   A. Heathcote, "Unbounded Operators and the Incompleteness of Quantum Mechanics", Philosophy of Science 57 (1990), 523–534, p. 4, eq. (3)

import Mathlib

open MeasureTheory

namespace HeathcoteUnbounded

/-- Domain of the position operator `(Qψ)(x) = x ψ(x)` on `L²(ℝ)`, eq. (3):
`D(Q) = {ψ ∈ L²(ℝ) : ∫ x² |ψ(x)|² dx < ∞}`. -/
def positionDomain : Set (Lp ℂ 2 (volume : Measure ℝ)) :=
  {f | ∫⁻ x : ℝ, ‖x‖ₑ ^ 2 * ‖(f : ℝ → ℂ) x‖ₑ ^ 2 < ⊤}

end HeathcoteUnbounded


