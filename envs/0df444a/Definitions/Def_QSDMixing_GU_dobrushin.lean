-- Prove2me | Definitions.Def_QSDMixing_GU_dobrushin
-- name    : QSDMixing_GU_dobrushin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:51:55.860705+00:00
-- url     : https://prove2.me/theorems/ad272b46-fc6e-4af4-8e4e-9543cf247394
-- title:
--   The quantum Dobrushin coefficient $\kappa(T)$
-- statement:
--   The quantum Dobrushin coefficient of a map $T$ on a matrix algebra $\mathcal A$ is
--
--   $$
--   \kappa(T)=\sup_{\rho\ne\sigma\in\mathcal D(\mathcal A)}\frac{\|T(\rho)-T(\sigma)\|_1}{\|\rho-\sigma\|_1}.
--   $$
--
--   It measures the trace-norm contraction of $T$ on the states of $\mathcal A$.
--
--   **Formalization Note** If $\mathcal D(\mathcal A)$ has at most one point, the supremum is over the empty set and the value is $0$. For a linear $T$ the ratios are bounded, so the supremum is genuine. The supremum is restricted to $\mathcal D(\mathcal A)$: over all density matrices, the Hadamard channel would have coefficient $1$, since it fixes every diagonal matrix.
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), eq. (50), p.15

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_QSDMixing_GU_densityIn

set_option autoImplicit false

namespace QSDMixing.GU

/-- The quantum Dobrushin coefficient `κ(T) = sup_{ρ ≠ σ ∈ D(A)} ‖T ρ - T σ‖₁ / ‖ρ - σ‖₁`.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), eq. (50), p.15.

**Formalization Note.** The supremum is over `D(A)`, not over all states, and `‖·‖₁` is the published
`WildeQIT.traceNorm`. Real `sSup` is `0` on an empty or unbounded set. If `D(A)` has at most one point the
set is empty and the value is `0`. For a linear map sending `D(A)` into itself the ratios lie in `[0, 1]`,
so the supremum is genuine. -/
noncomputable def dobrushin {n : Type} [Fintype n] [DecidableEq n]
    (A : StarSubalgebra ℂ (Matrix n n ℂ)) (T : Matrix n n ℂ → Matrix n n ℂ) : ℝ :=
  sSup {r | ∃ ρ ∈ densityIn A, ∃ σ ∈ densityIn A, ρ ≠ σ ∧
    r = WildeQIT.traceNorm (T ρ - T σ) / WildeQIT.traceNorm (ρ - σ)}

end QSDMixing.GU


