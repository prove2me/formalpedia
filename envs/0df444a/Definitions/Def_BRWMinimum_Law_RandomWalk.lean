-- Prove2me | Definitions.Def_BRWMinimum_Law_RandomWalk
-- name    : BRWMinimum_Law_RandomWalk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T00:31:48.605956+00:00
-- url     : https://prove2.me/theorems/14b95b6f-3726-49ab-a9c6-df233364d70a
-- title:
--   Many-to-one step law, the associated random walk Sₙ and its ladder-height renewal function R (2.11)
-- statement:
--   This file defines the one-dimensional random walk attached to the branching random walk by the many-to-one lemma, and its renewal function.
--
--   1. **Step law.** For a Borel set $B\subseteq\mathbb R$,
--   $$\mu(B)=\mathbf E\Big[\sum_{|x|=1}e^{-V(x)}\mathbf 1_B(V(x))\Big].$$
--   Under the boundary case (1.1), $\mu$ is a probability measure with mean $0$.
--   2. **Walk.** $S_0=0$ and $S_k=Y_0+\dots+Y_{k-1}$ with $(Y_i)_{i\ge0}$ i.i.d. of law $\mu$.
--   3. **Renewal function (2.11).** $R(x)=0$ for $x<0$ and, for $x\ge0$,
--   $$R(x)=\sum_{k\ge0}\mathbf P\Big(S_k\ge-x,\ S_k<\min_{0\le j\le k-1}S_j\Big),$$
--   the expected number of strict descending ladder heights of $S$ that are $\ge-x$. The minimum over the empty range ($k=0$) is $+\infty$, so the $k=0$ term equals $1$ and $R(0)=1$, as in the paper.
--
--   **Formalization Note** $\mu$ is the mixture $\int\sum_{v\in c}e^{-v}\delta_v\,L(dc)$ (`Measure.bind`); the kernel $c\mapsto\sum_{v\in c}e^{-v}\delta_v$ is measurable, so $\mu(B)$ is the displayed expectation. The step sequence has law Mathlib's `Measure.infinitePi` of copies of $\mu$, which is the i.i.d. product whenever $\mu$ is a probability measure (guaranteed by (1.1); otherwise `infinitePi` is $0$). "$S_k<\min_{j<k}S_j$" is encoded as "$S_k<S_j$ for every $j<k$", which is vacuous at $k=0$. $R$ takes values in $[0,\infty]$; its finiteness is part of a theorem of the mission.
-- source:
--   Aïdékon, Convergence in law of the minimum of a branching random walk, arXiv:1101.1810v6 (Ann. Probab. 41 (2013)), p. 4, §2, eq. (2.1); p. 7, §2.2, eq. (2.11)

import Mathlib
import Definitions.Def_BRWMinimum_Law_PointProcess

namespace BRWMinimum.Law

open MeasureTheory

/-- The step law of the many-to-one random walk:
`μ(B) = E[Σ_{|x|=1} e^{-V(x)} 1_B(V(x))]`, i.e. `μ = ∫ Σ_{points v} e^{-v} δ_v dL`.
Under (1.1) it is a probability measure. -/
noncomputable def stepLaw (L : Measure PointConfig) : Measure ℝ :=
  L.bind (fun c => Measure.sum (fun i : ℕ =>
    if (i : ℕ∞) < c.1 then ENNReal.ofReal (Real.exp (-c.2 i)) • Measure.dirac (c.2 i) else 0))

/-- The law of the i.i.d. step sequence `(S_{k+1} − S_k)_{k ≥ 0}` of the random walk:
the infinite product of `stepLaw L` (Mathlib's `infinitePi`; it is the product measure when
`stepLaw L` is a probability measure, which (1.1) guarantees). -/
noncomputable def walkLaw (L : Measure PointConfig) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => stepLaw L)

/-- `S_k = Σ_{i<k} s_i`, the walk started at `0` built from the step sequence `s`. -/
def walk (s : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, s i

/-- The renewal function (2.11) of the strict descending ladder heights of `S` (started at 0):
`R(x) = 0` for `x < 0` and, for `x ≥ 0`,
`R(x) = Σ_{k≥0} P(S_k ≥ −x, S_k < min_{0≤j≤k−1} S_j)`, where the minimum over the empty range
(`k = 0`) is `+∞`, so the `k = 0` term is `1` (in particular `R(0) = 1`). -/
noncomputable def renewalFn (L : Measure PointConfig) (x : ℝ) : ENNReal :=
  if x < 0 then 0 else
    ∑' k : ℕ, walkLaw L {s | -x ≤ walk s k ∧ ∀ j < k, walk s k < walk s j}

end BRWMinimum.Law


