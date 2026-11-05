-- Prove2me | Definitions.Def_BauerleRiederMDP_PartialObs_dSeq
-- name    : BauerleRiederMDP_PartialObs_dSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:03:13.65906+00:00
-- url     : https://prove2.me/theorems/860f1c4b-e8ad-4c72-9ee9-93432bf6137d
-- title:
--   The functions $d_n(\rho)$ of the mean-variance recursion (6.7)
-- statement:
--   For a horizon $N$ define functions $d_n$ on $\mathbb P(E_Y)$, $n=0,1,\dots,N$, by backward recursion:
--   $$
--   d_N(\rho)=1,\qquad d_n(\rho)=\underline d_{n+1}(\rho)-\ell_{n+1}(\rho)^\top C_{n+1}(\rho)^{-1}\ell_{n+1}(\rho),\tag{6.7}
--   $$
--   where $\underline d_{n+1}$, $\ell_{n+1}$ and $C_{n+1}$ are the integrals of $d_{n+1}$ against $Q^R(dz\mid y)\rho(dy)$ (with weights $1$, $z$ and $zz^\top$, after applying the Bayes operator).
--
--   **Formalization Note** The sequence is indexed by the number of stages to go: the book's $d_n$ for horizon $N$ is the $(N-n)$-th term. $C^{-1}$ is Mathlib's matrix inverse, which is the true inverse because $C_{n+1}(\rho)$ is positive definite under (FM).
-- source:
--   Bäuerle & Rieder (2011), §6.2, eq. (6.7), p.185 (PDF 198)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_dUnder
import Definitions.Def_BauerleRiederMDP_PartialObs_ell
import Definitions.Def_BauerleRiederMDP_PartialObs_Cmat

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BauerleRiederMDP.PartialObs

/-- **The functions `d_n(ρ)` of the mean-variance problem**, backward recursion (6.7).
Bäuerle & Rieder (2011), §6.2, eq. (6.7), p.185 (PDF 198): for `ρ ∈ IP(E_Y)` and
`n = 0, 1, …, N`,
`d_N(ρ) = 1`,
`d_n(ρ) = d̲_{n+1}(ρ) − ℓ_{n+1}(ρ)ᵀ C_{n+1}(ρ)^{−1} ℓ_{n+1}(ρ)`,
with `d̲_{n+1}`, `ℓ_{n+1}`, `C_{n+1}` the integrals (`dUnder`, `ell`, `Cmat`) of `d_{n+1}`.

`dSeq M k` is indexed by the number `k = N − n` of stages to go: the book's `d_n` for horizon `N`
is `dSeq M (N − n)`; `dSeq M 0 ≡ 1` and
`dSeq M (k+1) = dUnder (dSeq M k) − ell (dSeq M k) ⬝ᵥ (Cmat (dSeq M k))⁻¹ ell (dSeq M k)`.

**Formalization Note.** `(·)⁻¹` is Mathlib's matrix inverse (`0` for a singular matrix);
`C_{n+1}(ρ)` is positive definite under (FM) and Lemma 6.2.1, so it is the true inverse there. -/
noncomputable def dSeq {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : Market EY d) :
    ℕ → ProbabilityMeasure EY → ℝ
  | 0, _ => 1
  | k + 1, ρ => dUnder M (dSeq M k) ρ -
      ell M (dSeq M k) ρ ⬝ᵥ ((Cmat M (dSeq M k) ρ)⁻¹ *ᵥ ell M (dSeq M k) ρ)

end BauerleRiederMDP.PartialObs


