-- Prove2me | Definitions.Def_HayashiHoeffding_IsDensityOp
-- name    : HayashiHoeffding_IsDensityOp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:24.033854+00:00
-- url     : https://prove2.me/theorems/ee20ea5a-c8be-44e5-ad09-3b5dc52f0d83
-- title:
--   Density operator on a Hilbert space
-- statement:
--   A bounded operator $\rho$ on a complex Hilbert space $\mathcal H$ is a **density operator** if
--
--   1. $\rho \ge 0$ (it is a positive operator),
--   2. $\rho$ is trace class, and
--   3. $\operatorname{Tr} \rho = 1$.
--
--   Density operators are the quantum states; the paper's hypotheses $\rho$ and $\sigma$ are arbitrary density operators, possibly singular and non-commuting, on a possibly infinite-dimensional $\mathcal H$.
--
--   **Formalization Note** Trace class and trace are the published `IsModulusTraceClass` (summability of $\langle e_i, |\rho| e_i \rangle$ over a chosen Hilbert basis) and `basisOperatorTrace` ($\sum_i \langle e_i, \rho e_i\rangle$), with scalar field $\mathbb C$. The order is Mathlib's Loewner order.
-- source:
--   Hayashi, Error Exponent in Asymmetric Quantum Hypothesis Testing and Its Application to Classical-Quantum Channel coding, arXiv:quant-ph/0611013v2, "Formulation and main results", p.2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02

open QAlgorithms.Papers.Independent.Next46.P02

namespace HayashiHoeffding

universe u

/-- A density operator on a complex Hilbert space `H`: a positive bounded operator that is
trace class and has trace `1`.

Hayashi, arXiv:quant-ph/0611013v2, "Formulation and main results", p.2 ("arbitrarily given
density operators ρ and σ on H").

**Formalization Note.** Trace class and the trace are the published
`IsModulusTraceClass` (summability of `⟨eᵢ, |ρ| eᵢ⟩` over a chosen Hilbert basis) and
`basisOperatorTrace` (`∑' i, ⟨eᵢ, ρ eᵢ⟩`) of `Def_QAlgorithms_Papers_Independent_Next46_P02`,
with scalar field `ℂ`. `0 ≤ ρ` is Mathlib's Loewner order (`ρ` is a positive operator, hence
self-adjoint). No finite dimension or separability is assumed. -/
def IsDensityOp {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : H →L[ℂ] H) : Prop :=
  0 ≤ ρ ∧ IsModulusTraceClass ρ ∧ basisOperatorTrace ρ = 1

end HayashiHoeffding


