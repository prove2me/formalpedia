-- Prove2me | Definitions.Def_ArgmaxDeFinetti_supportFn
-- name    : ArgmaxDeFinetti_supportFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:39:20.597833+00:00
-- url     : https://prove2.me/theorems/4adb4153-e038-465a-9a8d-5977894979ab
-- title:
--   Support function $h_C(M)=\max_{\rho\in C}\operatorname{Tr}(M\rho)$
-- statement:
--   For a set $C$ of states and a Hermitian operator $M$, the support function is
--   $$
--   h_C(M)=\max_{\rho\in C}\operatorname{Tr}(M\rho).
--   $$
--   The distance dualities of Lemma 2.1 are stated as gaps of support functions.
--
--   **Formalization Note** $\operatorname{Tr}(M\rho)$ is real for Hermitian $M,\rho$ and its real part is taken; the maximum is written as a supremum, attained on nonempty compact sets.
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §2.2, p.20, eq. (2.8)

import Mathlib

open Matrix

namespace ArgmaxDeFinetti

/-- The support function `h_C(M) = max_{ρ∈C} Tr(Mρ)` of a set `C` of states, for Hermitian `M`,
Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), eq. (2.8), p.20.

**Formalization Note** `Tr(Mρ)` is real for Hermitian `M` and `ρ`; its real part is taken. The maximum is
written as `sSup`; on a nonempty compact `C` it is attained. -/
noncomputable def supportFn {ι : Type} [Fintype ι] (C : Set (Matrix ι ι ℂ)) (M : Matrix ι ι ℂ) : ℝ :=
  sSup ((fun ρ => (Matrix.trace (M * ρ)).re) '' C)

end ArgmaxDeFinetti


