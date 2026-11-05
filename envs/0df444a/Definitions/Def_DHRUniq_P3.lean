-- Prove2me | Definitions.Def_DHRUniq_P3
-- name    : DHRUniq_P3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:41.828096+00:00
-- url     : https://prove2.me/theorems/e6e4ee48-1809-4a61-b286-2675d2a6b2f2
-- title:
--   Condition (P3): asymptotic continuity on pure states
-- statement:
--   Let $(\mathcal H_n^A)$ and $(\mathcal H_n^B)$ be sequences of Hilbert spaces and $\mathcal H_n=\mathcal H_n^A\otimes\mathcal H_n^B$. For all sequences of pure states $\varrho_n,\sigma_n$ on $\mathcal H_n$ with $\|\varrho_n-\sigma_n\|_1\to0$,
--
--   $$
--   \frac{E(\varrho_n)-E(\sigma_n)}{1+\log_2\dim\mathcal H_n}\to0.
--   $$
--
--   The dimensions may grow with $n$, which is what separates this condition from ordinary continuity.
--
--   This is one of the conditions on an entanglement measure $E$ in §5 of the paper.
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, §5.2, (P3), p. 10

import Mathlib
import Definitions.Def_DHRUniq_BipartiteFunctional
import Definitions.Def_DHRUniq_IsUnitVec
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_ObliviousRSP_pureState

open Filter Topology
open ObliviousRSP (pureState)
open WildeQIT (traceNorm)

namespace DHRUniq

/-- **Condition (P3), asymptotic continuity on pure states** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, §5.2, p. 10): "Let
`(H_n^A)_{n∈ℕ}` and `(H_n^B)_{n∈ℕ}` be sequences of Hilbert spaces and let `H_n ≡ H_n^A ⊗ H_n^B` for
all `n`. For all sequences `(ϱ_n)_{n∈ℕ}` and `(σ_n)_{n∈ℕ}` of states with
`ϱ_n, σ_n ∈ Σ_p(H_n^A ⊗ H_n^B)`, such that `‖ϱ_n − σ_n‖_1 → 0`, we require that
`(E(ϱ_n) − E(σ_n)) / (1 + log_2 dim H_n) → 0`."

**Formalization Note** The local spaces form sequences `a b : ℕ → Type`, so their dimensions may
grow; on a fixed space this would be ordinary continuity, a different condition.
`dim H_n = card (a n) · card (b n)`, and a unit vector forces both to be nonzero, so the denominator
is at least `1`. -/
def P3 (E : BipartiteFunctional) : Prop :=
  ∀ (a b : ℕ → Type) [∀ n, Fintype (a n)] [∀ n, DecidableEq (a n)] [∀ n, Fintype (b n)]
    [∀ n, DecidableEq (b n)] (ψ φ : ∀ n, a n × b n → ℂ),
    (∀ n, IsUnitVec (ψ n)) → (∀ n, IsUnitVec (φ n)) →
    Tendsto (fun n => traceNorm (pureState (ψ n) - pureState (φ n))) atTop (𝓝 0) →
    Tendsto (fun n => (E (pureState (ψ n)) - E (pureState (φ n))) /
      (1 + Real.logb 2 ((Fintype.card (a n) : ℝ) * (Fintype.card (b n) : ℝ)))) atTop (𝓝 0)

end DHRUniq


