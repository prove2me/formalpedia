-- Prove2me | Definitions.Def_CrowdLastMile_ClosedForms
-- name    : CrowdLastMile_ClosedForms
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:23:35.84359+00:00
-- url     : https://prove2.me/theorems/cb3cfa6e-3137-4f41-8bd0-77d8efa5dce3
-- title:
--   Closed forms of Proposition 1: $E^j_i$, $F^j_i$, $G_j$, $\bar P^N$, $\hat P$, $\tilde P$, $P^*$, $w^*$, $z(N)$
-- statement:
--   The explicit quantities of Proposition 1:
--
--   $$
--   E^j_i=\sum_{\ell=(j-iN)q+1}^{(j-1)q+1}\mu^a_\ell-\gamma^a\sqrt{\sum_{\ell=(j-iN)q+1}^{(j-1)q+1}(\sigma^a_\ell)^2},\qquad
--   G_j=\sum_{\ell=(j-1)q+2}^{jq}\mu^a_\ell+\gamma^a\sqrt{\sum_{\ell=(j-1)q+2}^{jq}(\sigma^a_\ell)^2},
--   $$
--
--   $$
--   F^j_i=\sum_{\ell=0}^{i}\sum_{p=(j-\ell N-1)q+1}^{(j-\ell N)q}\mu^s_p+\gamma^s\sqrt{\sum_{\ell=0}^{i}\sum_{p=(j-\ell N-1)q+1}^{(j-\ell N)q}(\sigma^s_p)^2}+\sum_{\ell=0}^{i}\frac{\beta\sqrt{q+1}}{v_{j-\ell N}},
--   $$
--
--   $s^j_2=\{i=1,\dots,a^j:\alpha-F^j_i<0\}$, and
--
--   $$
--   \bar P^N=\min_{j=N+1,\dots,m}\ \min_{i\in s^j_2}\frac{E^j_i}{F^j_i-\alpha},\quad
--   \hat P=\max_{j=1,\dots,m}\frac{G_j}{\alpha-F^j_{i=0}},\quad
--   \tilde P=\frac{(1-\epsilon)NC_2}{C_1},\quad
--   P^*=\min\{\bar P^N,\tilde P,1\},
--   $$
--
--   $$
--   w^*(P)=\frac{R\,C_2}{P\,C_1},\qquad w^*=w^*(P^*),\qquad z(N)=P^*(w^*C-c_T)+c_T .
--   $$
--
--   The module also names $\max_jF^j_{i=0}$ and the hypothesis $E^j_i\ge0$ for the pairs with $F^j_i\le\alpha$. Here $\hat P$ is a lower bound on the crowd share, $\bar P^N$ and $\tilde P$ are upper bounds, and $w^*(P)$ is the crowd supply function.
--
--   **Formalization Note** $\bar P^N$ lies in `WithTop ℝ`: a minimum over an empty set is $+\infty$. $P^*$ is a real number because $\min\{\bar P^N,\tilde P,1\}\le1$; the default value of `untopD` is never used. The wage $w^*(P)$ is the corrected one: the source prints $(R/N)C_2/(PC_1)$, which violates the participation constraint for $N\ge2$.
-- source:
--   Fatehi–Wagner, Crowdsourcing Last-Mile Deliveries, SSRN 3434625, Proposition 1 and the display before it, p.17; proof of Proposition 1, pp.39–41

import Mathlib
import Definitions.Def_CrowdLastMile_Model

open Finset

namespace CrowdLastMile

namespace Params

variable (p : Params)

/-- `E^j_i = ∑_{ℓ=(j-iN)q+1}^{(j-1)q+1} μ^a_ℓ - γ^a √(∑_{ℓ=(j-iN)q+1}^{(j-1)q+1} (σ^a_ℓ)²)`, the
best-case interarrival time between set `j` and the `i`-th preceding set served by the same
driver. Fatehi–Wagner, Crowdsourcing Last-Mile Deliveries, SSRN 3434625, p.17. -/
noncomputable def E (j i : ℕ) : ℝ :=
  (∑ ℓ ∈ Icc ((j - i * p.N) * p.q + 1) ((j - 1) * p.q + 1), p.μa ℓ)
    - p.γa * Real.sqrt (∑ ℓ ∈ Icc ((j - i * p.N) * p.q + 1) ((j - 1) * p.q + 1), (p.σa ℓ) ^ 2)

/-- `F^j_i = ∑_{ℓ=0}^i ∑_{r=(j-ℓN-1)q+1}^{(j-ℓN)q} μ^s_r
+ γ^s √(∑_{ℓ=0}^i ∑_{r=(j-ℓN-1)q+1}^{(j-ℓN)q} (σ^s_r)²) + ∑_{ℓ=0}^i β√(q+1)/v_{j-ℓN}`, the cumulative
worst-case system time of set `j` and the `i` preceding sets of the same driver. `F^j_{i=0}` is
`F j 0`. Fatehi–Wagner, SSRN 3434625, p.17. -/
noncomputable def F (j i : ℕ) : ℝ :=
  (∑ ℓ ∈ range (i + 1), ∑ r ∈ Icc ((j - ℓ * p.N - 1) * p.q + 1) ((j - ℓ * p.N) * p.q), p.μs r)
    + p.γs * Real.sqrt
        (∑ ℓ ∈ range (i + 1),
          ∑ r ∈ Icc ((j - ℓ * p.N - 1) * p.q + 1) ((j - ℓ * p.N) * p.q), (p.σs r) ^ 2)
    + ∑ ℓ ∈ range (i + 1), p.β * Real.sqrt ((p.q : ℝ) + 1) / p.v (j - ℓ * p.N)

/-- `G_j = ∑_{ℓ=(j-1)q+2}^{jq} μ^a_ℓ + γ^a √(∑_{ℓ=(j-1)q+2}^{jq} (σ^a_ℓ)²)`, the worst-case wait of
the first customer of set `j` until the set forms; both sums are empty when `q = 1`.
Fatehi–Wagner, SSRN 3434625, p.17. -/
noncomputable def G (j : ℕ) : ℝ :=
  (∑ ℓ ∈ Icc ((j - 1) * p.q + 2) (j * p.q), p.μa ℓ)
    + p.γa * Real.sqrt (∑ ℓ ∈ Icc ((j - 1) * p.q + 2) (j * p.q), (p.σa ℓ) ^ 2)

/-- `1 ≤ m`. -/
theorem one_le_m : 1 ≤ p.m := Nat.mul_pos p.hτm p.hN

/-- `{1, …, m}` is non-empty. -/
theorem Icc_one_m_nonempty : (Icc 1 p.m).Nonempty := nonempty_Icc.mpr p.one_le_m

/-- `max_{j=1,…,m} F^j_{i=0}`, the quantity in the hypothesis of Proposition 1.
Fatehi–Wagner, SSRN 3434625, p.17. -/
noncomputable def maxF0 : ℝ := (Icc 1 p.m).sup' p.Icc_one_m_nonempty (fun j => p.F j 0)

open Classical in
/-- `s^j_2 = {i = 1, …, a^j : α - F^j_i < 0}`. Fatehi–Wagner, SSRN 3434625, p.17. -/
noncomputable def s2 (j : ℕ) : Finset ℕ := (Icc 1 (p.a j)).filter (fun i => p.α - p.F j i < 0)

/-- `P̄^N = min_{j=N+1,…,m} min_{i∈s^j_2} E^j_i / (F^j_i - α)`, the upper bound on `P` from the first
constraint family. Fatehi–Wagner, SSRN 3434625, p.17.

**Formalization Note.** The value lies in `WithTop ℝ`: a minimum over an empty set is `⊤`, that is
`P̄^N = +∞` when every `s^j_2` is empty, and in particular when `m = N`. -/
noncomputable def PBar : WithTop ℝ :=
  (Icc (p.N + 1) p.m).inf fun j =>
    (p.s2 j).inf fun i => ((p.E j i / (p.F j i - p.α) : ℝ) : WithTop ℝ)

/-- `P̂ = max_{j=1,…,m} G_j / (α - F^j_{i=0})`, the lower bound on `P`.
Fatehi–Wagner, SSRN 3434625, p.17. -/
noncomputable def PHat : ℝ :=
  (Icc 1 p.m).sup' p.Icc_one_m_nonempty (fun j => p.G j / (p.α - p.F j 0))

/-- `P̃ = (1 - ε) N C2 / C1`, the stability bound on `P`. Fatehi–Wagner, SSRN 3434625, p.17. -/
noncomputable def PTilde : ℝ := (1 - p.ε) * (p.N : ℝ) * p.C2 / p.C1

/-- `min{P̄^N, P̃, 1}`, computed in `WithTop ℝ`. -/
noncomputable def PStarTop : WithTop ℝ :=
  min p.PBar (min ((p.PTilde : ℝ) : WithTop ℝ) ((1 : ℝ) : WithTop ℝ))

/-- `P* = min{P̄^N, P̃, 1}` as a real number. Fatehi–Wagner, SSRN 3434625, Proposition 1, p.17.

**Formalization Note.** `PStarTop` is never `⊤`, since it is at most `1`; the default `1` of
`untopD` is therefore never used. -/
noncomputable def PStar : ℝ := p.PStarTop.untopD 1

/-- The crowd supply function `w*(P) = R C2 / (P C1)`.

**Formalization Note.** This is the least `w` satisfying the participation constraint at `P`. The
source prints `(R/N) C2 / (P C1)` (p.39), which violates that constraint for `N ≥ 2`; the factor
`1/N` is dropped here. -/
noncomputable def wSupply (P : ℝ) : ℝ := p.R * p.C2 / (P * p.C1)

/-- The optimal wage `w* = w*(P*)`, corrected as in `wSupply`. -/
noncomputable def wStar : ℝ := p.wSupply p.PStar

/-- The minimized worst-case delivery cost rate `z(N) = P*(w* C - c_T) + c_T`.
Fatehi–Wagner, SSRN 3434625, Proposition 1, p.17. -/
noncomputable def zN : ℝ := p.PStar * (p.wStar * p.C - p.cT) + p.cT

/-- The hypothesis `E^j_i ≥ 0` at set `j`, for those `i ∈ {1, …, a^j}` with `F^j_i ≤ α`. -/
def HEAt (j : ℕ) : Prop := ∀ i ∈ Icc 1 (p.a j), p.F j i ≤ p.α → 0 ≤ p.E j i

/-- The hypothesis `E^j_i ≥ 0` for every `j ∈ {N+1, …, m}` and `i ∈ {1, …, a^j}` with `F^j_i ≤ α`.
The proof of Proposition 1 (p.40) asserts this as a fact, but it does not follow from the model
and it can fail, in which case Proposition 1 as printed is false. -/
def HE : Prop := ∀ j ∈ Icc (p.N + 1) p.m, p.HEAt j

end Params

end CrowdLastMile


