-- Prove2me | Definitions.Def_ScutaruFid_IsDensityOperator
-- name    : ScutaruFid_IsDensityOperator
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:25.312021+00:00
-- url     : https://prove2.me/theorems/6473dfc5-ad3a-4b9d-97d0-11c1c1975e41
-- title:
--   Density operator: trace class, positive, trace $1$
-- statement:
--   Let $H$ be a complex Hilbert space with Hilbert basis $(b_i)_{i\in\iota}$. A bounded operator $\rho$ on $H$ is a **density operator** if
--
--   1. $\rho$ is trace class,
--   2. $\rho$ is positive: $\rho^*=\rho$ and $\langle x,\rho x\rangle\ge 0$ for every $x\in H$,
--   3. $\operatorname{trace}\rho=\sum_i\langle b_i,\rho\, b_i\rangle=1$.
--
--   These are the paper's requirements "Hermitian, normalizable and non-negative" (p.1).
--
--   **Formalization Note** Trace class, positivity and the basis trace are the published `Dependency50.P13.IsTraceClass`, `IsPositive` and `operatorTrace`. The trace of a trace-class operator is independent of the basis; the mission's theorems quantify over the basis.
-- source:
--   Scutaru, Fidelity for displaced squeezed thermal states and the oscillator semigroup, arXiv:quant-ph/9708013v1, p.1, paragraph after (3) ("In order that ρ be a quantum density operator it must be Hermitian, normalizable and non-negative")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13

open QAlgorithms.Papers.Independent.Dependency50.P13

namespace ScutaruFid

/-- **Density operator.** Scutaru, arXiv:quant-ph/9708013v1, p.1, paragraph after (3): "In order
that ρ be a quantum density operator it must be Hermitian, normalizable and non-negative".

`IsDensityOperator b ρ` says that the bounded operator `ρ` on the complex Hilbert space `H` is
trace class, positive (self-adjoint with `⟨x, ρx⟩ ≥ 0` for all `x`) and has trace `1`, the trace
being computed in the Hilbert basis `b`.

**Formalization Note** Trace class, positivity and the basis trace `∑ᵢ ⟨bᵢ, ρ bᵢ⟩` are the
published `Dependency50.P13.IsTraceClass`, `IsPositive` and `operatorTrace`. The trace of a
trace-class operator does not depend on the basis; theorems of the mission quantify over the
basis wherever it appears. -/
def IsDensityOperator {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} (b : HilbertBasis ι ℂ H) (ρ : H →L[ℂ] H) : Prop :=
  IsTraceClass ρ ∧ IsPositive ρ ∧ operatorTrace b ρ = 1

end ScutaruFid


