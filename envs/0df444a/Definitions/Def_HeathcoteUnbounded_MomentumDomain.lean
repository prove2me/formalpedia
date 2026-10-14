-- Prove2me | Definitions.Def_HeathcoteUnbounded_MomentumDomain
-- name    : HeathcoteUnbounded_MomentumDomain
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-13T14:33:51.782988+00:00
-- url     : https://prove2.me/theorems/d355e0ab-da03-41d3-b73c-e797a7ed1d81
-- title:
--   Domain $D(P)$ of the momentum operator on $L^2(\mathbb R)$ (absolutely continuous elements)
-- statement:
--   The momentum operator is $P\psi=\hbar\, i^{-1}\,\frac{d\psi}{dx}$. Following p. 5 of the source, its domain $D(P)$ "consists of all absolutely continuous functions $f\in L^2(\mathbb R)$":
--
--   $$D(P)=\{\,f\in L^2(\mathbb R)\ :\ f \text{ has a representative } g \text{ that is absolutely continuous on every compact interval } [a,b]\,\}.$$
--
--   **Formalization Note** Absolute continuity on $[a,b]$ is Mathlib's `AbsolutelyContinuousOnInterval`. The source omits the usual extra condition $f'\in L^2(\mathbb R)$ of the standard self-adjoint momentum domain; the set defined here is therefore a superset of the standard domain, so showing that a state is *not* in it is a (slightly) stronger statement than non-membership in the standard domain.
-- source:
--   A. Heathcote, "Unbounded Operators and the Incompleteness of Quantum Mechanics", Philosophy of Science 57 (1990), 523–534, p. 5

import Mathlib

open MeasureTheory

namespace HeathcoteUnbounded

/-- Domain of the momentum operator `P = ħ i⁻¹ d/dx` as described on p. 5 of the source:
the elements of `L²(ℝ)` that are (represented by) absolutely continuous functions, i.e. have a
representative that is absolutely continuous on every compact interval. -/
def momentumDomain : Set (Lp ℂ 2 (volume : Measure ℝ)) :=
  {f | ∃ g : ℝ → ℂ, (f : ℝ → ℂ) =ᵐ[volume] g ∧ ∀ a b : ℝ, AbsolutelyContinuousOnInterval g a b}

end HeathcoteUnbounded


