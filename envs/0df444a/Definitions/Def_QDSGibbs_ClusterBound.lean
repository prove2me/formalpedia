-- Prove2me | Definitions.Def_QDSGibbs_ClusterBound
-- name    : QDSGibbs_ClusterBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:38:25.133312+00:00
-- url     : https://prove2.me/theorems/f121324b-2211-46dc-9f1d-92bdde445294
-- title:
--   The interval covariance bound (5.18) for a block Gibbs state
-- statement:
--   A state $\sigma$ satisfies the **interval covariance bound** inside an interval $B$, with constant $C_{\mathrm{cl}}$ and profile $f$, if for all observables $A,Y$ supported on disjoint intervals contained in $B$,
--
--   $$
--   |\sigma(AY)-\sigma(A)\sigma(Y)|\le C_{\mathrm{cl}}\|A\|\,\|Y\|\,f(\mathrm{dist}(A,Y)).
--   $$
--
--   This is the hypothesis through which field-uniform clustering (Theorem 5.2) enters the influence estimates of §5.3.
--
--   **Formalization Note** "$f(\mathrm{dist}(A,Y))$" is encoded as the bound with $f(v)$ for every $v$ not exceeding the distance; for a nonincreasing $f$ this is the same condition. Observables are arbitrary operators; for the block Gibbs state $\sigma^B_\beta$ the full-space form $\sigma^B_\beta\otimes\mathbb 1/\dim$ is used, with the same covariances.
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), (5.18), p.45

import Mathlib
import Definitions.Def_QDSGibbs_chainGen
import Definitions.Def_QDSGibbs_cov

open scoped Matrix

namespace QDSGibbs

/-- The **interval covariance bound** (5.18) for a state `σ` inside an interval `B`
(arXiv:2610.03578, held file sha256 ede55815…, (5.18), p.45): for all observables `A, Y` supported on
disjoint intervals inside `B`, `|σ(AY) − σ(A)σ(Y)| ≤ C_cl ‖A‖‖Y‖ f(dist(A, Y))`.

**Formalization Note** "`f(dist(A, Y))`" is encoded as: for every `v` with `dist ≥ v`, the bound with
`f(v)`. For a nonincreasing profile `f` (the paper's case) this is the same condition. The state
`σ = gibbs β (hamOn I B)` is the full-space form of `σ^B_β`; covariances of observables inside `B`
are unchanged. Observables are arbitrary operators. -/
def ClusterBound {N : ℕ} {d : Fin N → ℕ} (σ : Op d) (B : Finset (Fin N)) (Ccl : ℝ) (f : ℝ → ℝ) :
    Prop :=
  ∀ SA SY : Finset (Fin N), IsInterval SA → IsInterval SY → SA ⊆ B → SY ⊆ B → Disjoint SA SY →
    ∀ v : ℝ, DistGe SA SY v → ∀ A Y : Op d, SupportedOn SA A → SupportedOn SY Y →
      ‖cov σ A Y‖ ≤ Ccl * opNorm A * opNorm Y * f v

end QDSGibbs


