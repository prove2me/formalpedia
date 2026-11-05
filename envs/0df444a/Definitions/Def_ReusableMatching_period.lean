-- Prove2me | Definitions.Def_ReusableMatching_period
-- name    : ReusableMatching_period
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:30:39.280429+00:00
-- url     : https://prove2.me/theorems/55302703-4683-4558-8a9e-45dad6d9abcc
-- title:
--   The period $k(j)$ of an arrival, and the previous period $k(j)-1$
-- statement:
--   Periodic Reranking draws new seeds every $d$ arrivals. The arrivals are split into consecutive **periods** of $d$ arrivals each, starting at the first arrival, and a **dummy period** without arrivals is placed before the first one, so that $k(j)-1$ is a period for every arrival $j$. With arrivals numbered from $0$, arrival $t$ lies in period
--
--   $$
--   k(t)=\lfloor t/d\rfloor+1,
--   $$
--
--   and the period before it is $k(t)-1=\lfloor t/d\rfloor$; period $0$ is the dummy period.
--
--   **Formalization Note** Both values are elements of $\{0,\dots,n\}$, the index set of the seed periods.
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, §3.1 Notations, p.8

import Mathlib
import Definitions.Def_ReusableMatching_OBMRRInstance

namespace ReusableMatching

/-- **The period `k(j)` of an arrival** (arXiv:2110.07084v2, §3.1 "Notations", p.8): "PR reranks
in fixed periods of length `d`. … let `k(j)` denote the period that contains arrival `j ∈ U`. To
ensure that `k(j) − 1` is well defined for every `j ∈ U`, we add a dummy period (of time interval
`d`) prior to the first arrival. This period does not have any arrivals and simply ensures that
`k(j) ≥ 2` for every arrival."

**Formalization Note.** Arrivals are `0`-based (`Fin n`), periods are numbered from `0`, and
period `0` is the dummy period. Arrival `t` lies in period `t / d + 1`, so the real periods are the
blocks `{0, …, d − 1}`, `{d, …, 2d − 1}`, … of `d` consecutive arrivals, starting with the first
arrival (the paper's 1-based arrival `j` lies in its period `⌈j / d⌉ + 1`, counting the dummy
period as period 1). The value lies in `Fin (n + 1)`, the index set of the seed periods. -/
def period {V : Type*} {n : ℕ} (I : OBMRRInstance V n) (t : Fin n) : Fin (n + 1) :=
  ⟨(t : ℕ) / I.d + 1, by have := Nat.div_le_self (t : ℕ) I.d; omega⟩

/-- **The previous period `k(j) − 1`** of an arrival (arXiv:2110.07084v2, p.8): the period just
before the one containing arrival `t`, i.e. `t / d`. It is the dummy period `0` for the arrivals of
the first real period, so `k(j) − 1` never needs truncated subtraction. -/
def prevPeriod {V : Type*} {n : ℕ} (I : OBMRRInstance V n) (t : Fin n) : Fin (n + 1) :=
  ⟨(t : ℕ) / I.d, by have := Nat.div_le_self (t : ℕ) I.d; omega⟩

end ReusableMatching


