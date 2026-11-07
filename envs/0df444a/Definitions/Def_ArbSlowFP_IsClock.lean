-- Prove2me | Definitions.Def_ArbSlowFP_IsClock
-- name    : ArbSlowFP_IsClock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:48:34.737594+00:00
-- url     : https://prove2.me/theorems/118bc0ef-be5e-48e0-bbf6-17c8ed1730fc
-- title:
--   Definition 4.1 — order-$k$ clock
-- statement:
--   An **order-$k$ clock** ($k\ge 2$) consists of a rational skew-symmetric matrix $A\in\mathbb Q^{m\times m}$ with a priority order, a score table $R\in\mathbb Q^{m\times k}$, an integer count table $C\in\mathbb Z^{m\times k}$, an entry action $b$, a rational counter row $v$, an integer threshold $Q_k\ge1$, words $W_k(q)$ for $q\ge Q_k$, rational constants $\delta_0>0$, $A_k\ge0$ and a computable threshold rule $\hat Q_k(\epsilon)$, such that, with $r(q)=Rp_{k-1}(q)$, $c(q)=Cp_{k-1}(q)$ and $\chi=R_{b,:}$:
--
--   1. **Exact trajectory.** For every $q\ge Q_k$, the word $W_k(q)$ is valid from $r(q)$, has action counts $c(q)\ge0$, and ends at $r(q+1)$. Moreover $AC=RN_k$, $\mathrm{rank}(C)=k$ and $\chi_{k-1}>0$.
--   2. **Entry leadership and endpoint detection.** $W_k(q)$ begins with at least two plays of $b$, $v_b=0$, $vC=e_{0,k}^\top$, at every proper prefix
--   $$H_{\mathrm{prefix}}-u_b+vz^{\mathrm{rem}}\ge\delta_0,$$
--   and at every entry $(r(q)+Ae_b-v^\top)_b>(r(q)+Ae_b-v^\top)_i$ for $i\in\mathrm{supp}(v)$.
--   3. **Remaining height.** For every rational $\epsilon>0$ we have $\hat Q_k(\epsilon)\ge Q_k$, and for all $q\ge\hat Q_k(\epsilon)$ and every prefix, including the empty and the complete one,
--   $$\chi(q+1)-H_{\mathrm{prefix}}\le\epsilon|W^{\mathrm{rem}}|+A_k .$$
--
--   The clock is the data passed from one induction step to the next.
--
--   **Formalization Note** The tuple is the structure `ClockData` and the properties are the predicate `IsClock`. The threshold rule is `Qhat a b` at $\epsilon=(a+1)/(b+1)$ with `Computable₂ Qhat`. The count table is rational with an integrality clause. "Explicitly specified words" needs no clause, since (1) determines each word from the other data. The action type is nonempty because it contains $b$.
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), pp.25–26, Definition 4.1

import Mathlib
import Definitions.Def_ArbSlowFP_ValidFrom
import Definitions.Def_ArbSlowFP_binomBasis

open Matrix

namespace ArbSlowFP

/-- The data tuple `(A, ≺, R, C, b, v, Q_k, {W_k(q)}, δ₀, A_k, Q̂_k(·))` of Definition 4.1, p.25.

**Formalization Note.** The priority is `rank` (see `IsPriorityMax`). The phase index is a natural
number and `W q` is only constrained for `q ≥ Q`. The count table `C` has rational entries, and
`IsClock` requires that they are integers. The threshold rule on a positive rational `ϵ` is
`Qhat a b`, at `ϵ = (a+1)/(b+1)`, which reaches every positive rational. -/
structure ClockData (k : ℕ) (ι : Type*) where
  /-- The payoff matrix. -/
  A : Matrix ι ι ℚ
  /-- The priority order, lower rank first. -/
  rank : ι → ℕ
  /-- The score table. -/
  R : Matrix ι (Fin k) ℚ
  /-- The count table. -/
  C : Matrix ι (Fin k) ℚ
  /-- The entry action. -/
  b : ι
  /-- The counter row. -/
  v : ι → ℚ
  /-- The phase threshold. -/
  Q : ℕ
  /-- The phase words. -/
  W : ℕ → List ι
  /-- The prefix margin. -/
  δ0 : ℚ
  /-- The remaining-height constant. -/
  Ak : ℚ
  /-- The threshold rule. -/
  Qhat : ℕ → ℕ → ℕ

namespace ClockData

variable {k : ℕ} {ι : Type*} [Fintype ι]

/-- The entry score vector `r(q) = R p_{k-1}(q)` of (8), p.15. -/
def r (d : ClockData k ι) (q : ℕ) : ι → ℚ := d.R *ᵥ binomBasis k q

/-- The count vector `c(q) = C p_{k-1}(q)` of (8), p.15. -/
def c (d : ClockData k ι) (q : ℕ) : ι → ℚ := d.C *ᵥ binomBasis k q

/-- The scalar height `χ(q) = χ p_{k-1}(q)` of (8), p.15, where `χ = R_{b,:}`. -/
def chiAt (d : ClockData k ι) (q : ℕ) : ℚ := d.R d.b ⬝ᵥ binomBasis k q

end ClockData

/-- Definition 4.1 (order-k clock), pp.25–26: properties (I), (II), (III) of the data tuple, for
`k ≥ 2`. Here `(14)` and `(16)` are stated at the prefix of length `h` of the word `W q`, with
`z^rem` the count vector of the remaining plays.

**Formalization Note.** "Explicitly specified words" needs no clause: (I) determines each `W q` from
`A`, `rank`, `R`, `C`, since the process (6) is deterministic. The computable threshold rule is
`Computable₂ Qhat`. It is non-uniform in the clock's fixed data, which is what p.25 describes:
"obtainable by finite calculations with the rational coefficient data". -/
structure IsClock {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (d : ClockData k ι) : Prop where
  two_le : 2 ≤ k
  skew : d.Aᵀ = -d.A
  rank_inj : Function.Injective d.rank
  C_int : ∀ i j, ∃ z : ℤ, d.C i j = z
  Q_pos : 1 ≤ d.Q
  δ0_pos : 0 < d.δ0
  Ak_nonneg : 0 ≤ d.Ak
  Qhat_computable : Computable₂ d.Qhat
  /-- (I): the word is followed by the process (6) from `r(q)`. -/
  valid : ∀ q, d.Q ≤ q → ValidFrom d.A d.rank (d.r q) (d.W q)
  /-- (I): the word has action counts `c(q)`, and these are nonnegative. -/
  counts : ∀ q, d.Q ≤ q → wordCount (d.W q) = d.c q ∧ ∀ i, 0 ≤ d.c q i
  /-- (I): the word ends at `r(q+1)`. -/
  exit : ∀ q, d.Q ≤ q → scoreAfter d.A (d.r q) (d.W q) = d.r (q + 1)
  /-- (I): `AC = RN_k`. -/
  AC_eq : d.A * d.C = d.R * shiftN k
  /-- (I): `rank(C) = k`. -/
  C_rank : d.C.rank = k
  /-- (I): `χ_{k-1} > 0`. -/
  chi_last : 0 < lastCoef (d.R d.b)
  /-- (II): the word begins with at least two consecutive plays of `b`. -/
  entry : ∀ q, d.Q ≤ q → ∃ w, d.W q = d.b :: d.b :: w
  /-- (II): `v_b = 0`. -/
  v_b : d.v d.b = 0
  /-- (II): `vC = e⊤_{0,k}`. -/
  vC_eq : d.v ᵥ* d.C = e0Row k
  /-- (II), (14): `H_prefix - u_b + v z^rem ≥ δ₀` at every proper prefix. -/
  prefix_margin : ∀ q, d.Q ≤ q → ∀ h, h < (d.W q).length →
    d.δ0 ≤ height (scoreAfter d.A (d.r q) ((d.W q).take h))
      - scoreAfter d.A (d.r q) ((d.W q).take h) d.b
      + d.v ⬝ᵥ wordCount ((d.W q).drop h)
  /-- (II), (15): the entry inequality on `supp(v)`. -/
  entry_ineq : ∀ q, d.Q ≤ q → ∀ i, d.v i ≠ 0 →
    d.r q i + d.A i d.b - d.v i < d.r q d.b + d.A d.b d.b - d.v d.b
  /-- (III): the threshold `Q̂_k(ϵ) ≥ Q_k`. -/
  Qhat_ge : ∀ a b, d.Q ≤ d.Qhat a b
  /-- (III), (16): `H_end - H_prefix ≤ ϵ|W^rem| + A_k` at every prefix, including the empty and the
  complete prefix, at `ϵ = (a+1)/(b+1)`. -/
  remaining : ∀ a b q, d.Qhat a b ≤ q → ∀ h, h ≤ (d.W q).length →
    d.chiAt (q + 1) - height (scoreAfter d.A (d.r q) ((d.W q).take h))
      ≤ ((a : ℚ) + 1) / ((b : ℚ) + 1) * (((d.W q).length : ℚ) - (h : ℚ)) + d.Ak

end ArbSlowFP


