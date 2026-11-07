-- Prove2me | Definitions.Def_DimFreeShadow_thresholdObs
-- name    : DimFreeShadow_thresholdObs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:01:53.658418+00:00
-- url     : https://prove2.me/theorems/8f6e4267-fc1c-4610-9a6a-888fc143d7a0
-- title:
--   Algorithm 3, line 11 — the threshold observable $F$ on $\mathcal H^{\otimes k}$
-- statement:
--   For an effect $E$ on $\mathcal H$, a block length $k$ and a threshold $c$,
--
--   $$
--   F=\sum_{\substack{v\in\{0,1\}^k\\ k^{-1}\sum_i v_i\ge c}}\ \bigotimes_{i=1}^k\begin{cases}E,&v_i=1,\\ I-E,&v_i=0.\end{cases}
--   $$
--
--   It tests whether $k$ independent measurements of $E$ have empirical mean at least $c$. Algorithm 3 applies Corollary 5.7 at constant accuracy to these observables.
--
--   **Formalization Note** $\{0,1\}^k$ is `Fin k → Bool`, with `true` for $1$. The helper `tensorProd` is the tensor product of $k$ operators on the index `Fin k → d`.
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), Algorithm 3, line 11, p.29

import Mathlib

namespace DimFreeShadow

/-- **Tensor product of `k` operators** `A₁ ⊗ ⋯ ⊗ A_k` on `H^{⊗k}` (indexed by `Fin k → d`):
entry `(x, y)` is `∏_i A_i(x_i, y_i)`. Helper for `thresholdObs`. -/
def tensorProd {d : Type} {k : ℕ} (A : Fin k → Matrix d d ℂ) :
    Matrix (Fin k → d) (Fin k → d) ℂ :=
  Matrix.of fun x y => ∏ i, A i (x i) (y i)

/-- **The threshold observable of Algorithm 3** (arXiv:2608.06345, sha256 a1a42249…,
Algorithm 3, line 11, p.29): for an effect `E` on `H`, a block length `k` and a threshold `c`,
`F := Σ_{v ∈ {0,1}^k : k⁻¹ Σ_i v_i ≥ c} ⊗_{i=1}^k (E if v_i = 1, I − E if v_i = 0)` on `H^{⊗k}`.

**Formalization Note** `{0,1}^k` is `Fin k → Bool` (`true` = 1); the factor index is 0-based. -/
noncomputable def thresholdObs {d : Type} [Fintype d] [DecidableEq d]
    (E : Matrix d d ℂ) (k : ℕ) (c : ℝ) : Matrix (Fin k → d) (Fin k → d) ℂ := by
  classical
  exact ∑ v ∈ Finset.univ.filter
      (fun v : Fin k → Bool => c ≤ (k : ℝ)⁻¹ * ∑ i, (if v i then (1 : ℝ) else 0)),
    tensorProd (fun i => if v i then E else 1 - E)

end DimFreeShadow


