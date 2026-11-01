-- Prove2me | Definitions.Def_LPResolvingRM_cap
-- name    : LPResolvingRM_cap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:40:00.15237+00:00
-- url     : https://prove2.me/theorems/d00eb0f6-e797-4d4d-844b-45a93f364ae2
-- title:
--   The sample path of Algorithm 1: counts $n_j(t)$, capacities $B_t$, average capacities $b_t$, accepted counts $n^a_j(t)$
-- statement:
--   Fix a horizon $T$, a type sequence $j_1,\dots,j_T$ and acceptance coins $\beta_1,\dots,\beta_T\in\{0,1\}$. Along this path Algorithm 1 keeps:
--
--   1. the counts $n_j(t)$, the number of type-$j$ orders among periods $1,\dots,t$, and the empirical frequencies $n_j(t-1)/(t-1)$;
--   2. the remaining capacity $B_1=B=Tb$ and $B_{t+1}=B_t-a_tx_t$, where $a_t=c_{j_t}$ and the order is accepted ($x_t=1$) iff its coin is $1$ and the constraint permits it, $c_{j_t}\le B_t$ (no shorting); $B_{T+1}$ is the capacity left at the end;
--   3. the average remaining capacity $b_t=B_t/(T-t+1)$;
--   4. the accepted counts $n^a_j(t)$, the number of accepted type-$j$ orders among periods $1,\dots,t$.
--
--   These are the processes the regret analysis is about.
--
--   **Formalization Note** Periods are 0-based in Lean: the paper's $B_t$ is `cap … (t-1)` and $b_t$ is `avgCap … (t-1)`. The law of the coins (accept with probability $y^*_{j,t}$) is in the definition of the regret. The permission rule also applies at $t=1$.
-- source:
--   Chen, Li, Ye, An Improved Analysis of LP-based Control for Revenue Management, arXiv:2101.11092v3, §2.2, p.7; Algorithm 1, p.8; Proposition 1, p.10

import Definitions.Def_LPResolvingRM_Instance

open scoped Classical

namespace LPResolvingRM

/-- **Type counts** `n_j(t)` (arXiv:2101.11092v3, p.7): the number of type-`j` orders among
periods `1, …, t` (inclusive) of the type sequence `ω`.

**Formalization Note.** Periods are 0-based in Lean: the paper's period `t` is the Lean index
`t − 1 : Fin T`, so `n_j(t)` counts the Lean indices `s < t`. For `t ≥ T` this is `n_j(T)` (no
orders arrive after the horizon). -/
noncomputable def count {n T : ℕ} (ω : Fin T → Fin n) (t : ℕ) (j : Fin n) : ℕ :=
  (Finset.univ.filter fun s : Fin T => s.val < t ∧ ω s = j).card

/-- **Empirical frequencies** `n_j(k)/k` used by the sampled LP (5) at the paper's period
`t = k + 1` (arXiv:2101.11092v3, Algorithm 1, line 7, p.8). At `k = 0` the value is `0/0 = 0`
and is never used (Algorithm 1 solves no LP at `t = 1`). -/
noncomputable def freq {n T : ℕ} (ω : Fin T → Fin n) (k : ℕ) (j : Fin n) : ℝ :=
  (count ω k j : ℝ) / k

/-- **Remaining capacity** of Algorithm 1 (arXiv:2101.11092v3, §2.2, p.7, and Algorithm 1,
p.8): `B_1 = B = T b` and `B_t = B_{t−1} − a_{t−1}x_{t−1}`, along the type sequence `ω` and the
acceptance coins `β`.

`cap I T ω β k` is the paper's `B_{k+1}`, the capacity at the beginning of the paper's period
`k + 1`; `cap I T ω β T` is `B_{T+1}`, the capacity left at the end of the horizon. In the
(0-based) Lean period `k < T` the order `ω k` is accepted (`x = 1`) iff its coin `β k` is `true`
**and** the constraint permits it, `c_{ω k} ≤ B` componentwise (Algorithm 1, line 10: "when the
constraint permits; otherwise set x_t = 0"; no shorting, p.7).

**Formalization Note.** The randomization of line 10 is carried by the coins `β`; their law
(`true` with probability `y*_{j,t}`) is in `LPResolvingRM.pathWeight`. The permission rule is
also applied at `t = 1`, where line 3 sets `x₁ = 1` (no shorting is allowed, p.7). -/
noncomputable def cap {n m : ℕ} (I : Instance n m) (T : ℕ) (ω : Fin T → Fin n)
    (β : Fin T → Bool) : ℕ → Fin m → ℝ
  | 0 => fun i => (T : ℝ) * I.b i
  | k + 1 =>
    if h : k < T then
      if β ⟨k, h⟩ = true ∧ ∀ i, I.c (ω ⟨k, h⟩) i ≤ cap I T ω β k i then
        fun i => cap I T ω β k i - I.c (ω ⟨k, h⟩) i
      else cap I T ω β k
    else cap I T ω β k

/-- The constraint **permits** the order of Lean period `k` (the paper's period `k + 1`):
`c_{ω k} ≤ B_{k+1}` componentwise (arXiv:2101.11092v3, Algorithm 1, line 10, p.8). -/
def permitted {n m : ℕ} (I : Instance n m) (T : ℕ) (ω : Fin T → Fin n) (β : Fin T → Bool)
    (k : Fin T) : Prop :=
  ∀ i, I.c (ω k) i ≤ cap I T ω β k.val i

/-- The order of Lean period `k` is **accepted**, `x_{k+1} = 1` (arXiv:2101.11092v3, Algorithm 1,
line 10, p.8): its coin is `true` and the constraint permits it. -/
def accepted {n m : ℕ} (I : Instance n m) (T : ℕ) (ω : Fin T → Fin n) (β : Fin T → Bool)
    (k : Fin T) : Prop :=
  β k = true ∧ permitted I T ω β k

/-- **Average remaining capacity** `b_t = B_t/(T − t + 1)` (arXiv:2101.11092v3, p.7), at the
paper's period `t = k + 1`: `avgCap I T ω β k = cap I T ω β k / (T − k)`. It is used for
`k < T`, where `T − k > 0`. -/
noncomputable def avgCap {n m : ℕ} (I : Instance n m) (T : ℕ) (ω : Fin T → Fin n)
    (β : Fin T → Bool) (k : ℕ) : Fin m → ℝ :=
  fun i => cap I T ω β k i / ((T : ℝ) - k)

/-- **Accepted counts** `n^a_j(t)` (arXiv:2101.11092v3, Proposition 1, p.10): the number of
accepted type-`j` orders among the paper's periods `1, …, t` (inclusive), i.e. among the Lean
periods `k < t`. For `t ≥ T` all periods are counted. -/
noncomputable def acceptedCount {n m : ℕ} (I : Instance n m) (T : ℕ) (ω : Fin T → Fin n)
    (β : Fin T → Bool) (t : ℕ) (j : Fin n) : ℕ :=
  (Finset.univ.filter fun k : Fin T => k.val < t ∧ ω k = j ∧ accepted I T ω β k).card

end LPResolvingRM


