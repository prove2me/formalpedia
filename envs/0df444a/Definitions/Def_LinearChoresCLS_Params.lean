-- Prove2me | Definitions.Def_LinearChoresCLS_Params
-- name    : LinearChoresCLS_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:45:42.44564+00:00
-- url     : https://prove2.me/theorems/9286bd5e-2ee9-45ea-ab15-3f41fcf0ca63
-- title:
--   The parameters of the construction: $\lambda$, $t$, $L$, $\alpha$, $w_{jj'}$, $q_k$, $B_{(j,j'),k}$, $S_{(j,j'),k}$
-- statement:
--   For an instance with quadratic $(A,c)$ and $\varepsilon>0$ set
--   $$
--   \lambda=\frac{1}{2(n+1)\big(1+\sum_{i,j}|A_{ij}|+\sum_i|c_i|\big)},\qquad t=\max\{2^{-\ell}:\ell\in\mathbb Z_{\ge8},\ 2^{-\ell}\le\lambda\varepsilon/64\}=2^{-L},\qquad \alpha=\lambda t^2 .
--   $$
--   With $x_0:=0$, $\bar x=\frac1{n+1}\sum_{j=0}^nx_j$ and $c_0:=-\sum_{i=1}^nc_i$, the **basic prices** are $p_j(x)=(1+tx_j)/(1+t\bar x)$, $j=0,\dots,n$. The **correction weights** are $w_{jj'}=\frac1{n+1}+\lambda A_{jj'}$ for $1\le j<j'\le n$ and $w_{0j}=\frac1{n+1}-\lambda\sum_{j'=1}^nA_{jj'}$. For a chain $(j,j')$ and layer $k$,
--   $$
--   q_k=1+\frac t4\Big(\frac12-4t\Big)^k,\qquad B_{(j,j'),k}=w_{jj'}\,t\Big(\frac12-4t\Big)^k,\qquad S_{(j,j'),k}=(1-4t)B_{(j,j'),k}.
--   $$
--
--   These quantities are shared by every statement about the constructed market.
--
--   **Formalization Note** The pairs $0\le j<j'\le n$ are the subtype `Pair n` of `Fin (n+1) × Fin (n+1)`; index $0$ is the reference chore and $i$`.succ` is coordinate $i$, so $x_0=0$ is `Fin.cons 0 x`. $L$ is the least $\ell\ge8$ with $2^{-\ell}\le\lambda\varepsilon/64$ (`Nat.find`), the value at which the maximum is attained; the fallback $8$ for $\varepsilon\le0$ is never used. $q_k$, $B$, $S$, $\alpha$ are defined for a general real $t$.
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version, sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Eqs. (5.2), (5.4), (5.5), (6.9), (6.13) and (7.1), pp.14–16, 23, 25, 30

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Quadratics

open Finset NetworkEquilibriumCLS.LinearNash

namespace LinearChoresCLS

/-- The pairs `0 ≤ j < j′ ≤ n` of basic chores (arXiv:2611.06589, held version sha256 85d34a9e…,
§5–§7; Section 7.1 (i), p.31). Basic chore `0` is the reference chore, chore `j ≥ 1` carries the
QP coordinate `x_j`. -/
abbrev Pair (n : ℕ) := {jj : Fin (n + 1) × Fin (n + 1) // jj.1 < jj.2}

variable {n : ℕ}

/-- The scale `λ := 1 / (2(n+1)(1 + ∑_{i,j} |A_{ij}| + ∑_i |c_i|))` of Section 7.1
(arXiv:2611.06589, p.30), so that `α = λt²` is (5.5). -/
noncomputable def lam (P : Quadratic n) : ℝ :=
  1 / (2 * (n + 1) * (1 + ∑ i, ∑ j, |(P.Q i j : ℝ)| + ∑ i, |(P.c i : ℝ)|))

open Classical in
/-- The chain length `L` of (7.1) (arXiv:2611.06589, p.30): the least integer `ℓ ≥ 8` with
`2^{−ℓ} ≤ λε/64`, so that `t := max{2^{−ℓ} : ℓ ∈ ℤ_{≥8}, 2^{−ℓ} ≤ λε/64} = 2^{−L}`.

**Formalization Note.** For `ε > 0` such an `ℓ` exists and the maximum of (7.1) is `2^{−L}`; the
fallback value `8` for `ε ≤ 0` is never used (every statement assumes `ε > 0`). -/
noncomputable def chainLength (P : Quadratic n) (ε : ℚ) : ℕ :=
  if h : ∃ ℓ : ℕ, 8 ≤ ℓ ∧ ((1 : ℝ) / 2) ^ ℓ ≤ lam P * (ε : ℝ) / 64 then Nat.find h else 8

/-- The parameter `t := 2^{−L}` of (7.1) (arXiv:2611.06589, p.30). -/
noncomputable def tParam (P : Quadratic n) (ε : ℚ) : ℝ := ((1 : ℝ) / 2) ^ chainLength P ε

/-- The scaling factor `α := t² / (2(n+1)(1 + ∑|A_{ij}| + ∑|c_i|)) = λt²` of (5.5)
(arXiv:2611.06589, p.16), for a general `t`. -/
noncomputable def alpha (P : Quadratic n) (t : ℝ) : ℝ := lam P * t ^ 2

/-- The point `x ∈ ℝⁿ` extended by the reference coordinate `x₀ := 0` (arXiv:2611.06589, §5,
p.13). Index `0` of `Fin (n+1)` is the reference chore; index `i.succ` is coordinate `i`. -/
def xExt (x : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.cons 0 x

/-- The mean `x̄ := (1/(n+1)) ∑_{j=0}^n x_j` (with `x₀ = 0`) (arXiv:2611.06589, (5.2), p.14). -/
noncomputable def xbar (x : Fin n → ℝ) : ℝ := (∑ j, xExt x j) / (n + 1)

/-- The **basic price family** `p_j(x) := (1 + t x_j)/(1 + t x̄)`, `j = 0, …, n`
(arXiv:2611.06589, Eq. (5.2), p.14). -/
noncomputable def basicPrice (t : ℝ) (x : Fin n → ℝ) (j : Fin (n + 1)) : ℝ :=
  (1 + t * xExt x j) / (1 + t * xbar x)

/-- The linear coefficients extended by `c₀ := −∑_{i=1}^n c_i` (arXiv:2611.06589, Eq. (6.13),
p.25). -/
noncomputable def cExt (P : Quadratic n) : Fin (n + 1) → ℝ :=
  Fin.cons (-∑ i, (P.c i : ℝ)) (fun i => (P.c i : ℝ))

/-- The **correction weights** of (5.4) as written in Section 7.1 (arXiv:2611.06589, pp.16, 30):
`w_{jj′} := 1/(n+1) + λA_{jj′}` for `1 ≤ j < j′ ≤ n` and `w_{0j} := 1/(n+1) − λ∑_{j′=1}^n A_{jj′}`.

**Formalization Note.** Only pairs `j < j′` are used (`pairWeight`); the value `0` returned when
the second index is `0` is never used. -/
noncomputable def wgt (P : Quadratic n) (j j' : Fin (n + 1)) : ℝ :=
  if hj : j = 0 then
    (if hj' : j' = 0 then 0 else 1 / (n + 1) - lam P * ∑ k, (P.Q (j'.pred hj') k : ℝ))
  else
    (if hj' : j' = 0 then 0 else 1 / (n + 1) + lam P * (P.Q (j.pred hj) (j'.pred hj') : ℝ))

/-- The weight `w_{jj′}` of a pair `0 ≤ j < j′ ≤ n` (arXiv:2611.06589, (5.4), p.16). -/
noncomputable def pairWeight (P : Quadratic n) (π : Pair n) : ℝ := wgt P π.1.1 π.1.2

/-- The chains incident to basic chore `j`: the pairs `(j, j′)` and `(j′, j)` (used with the
symmetric convention `B_{(j′,j),k} = B_{(j,j′),k}`, arXiv:2611.06589, p.31). -/
def incident (j : Fin (n + 1)) : Finset (Pair n) :=
  Finset.univ.filter (fun π => π.1.1 = j ∨ π.1.2 = j)

/-- The gadget disutility parameter `q_k := 1 + (t/4)(1/2 − 4t)^k` (arXiv:2611.06589, Eq. (6.9),
p.23, and Section 7.1 (ii), p.31). -/
noncomputable def qPar (t : ℝ) (k : ℕ) : ℝ := 1 + t / 4 * (1 / 2 - 4 * t) ^ k

/-- The gadget earning requirement `B_{(j,j′),k} := w_{jj′} t (1/2 − 4t)^k` (arXiv:2611.06589,
Eq. (6.9), p.23). -/
noncomputable def gadgetEarn (P : Quadratic n) (t : ℝ) (π : Pair n) (k : ℕ) : ℝ :=
  pairWeight P π * t * (1 / 2 - 4 * t) ^ k

/-- The gadget output supply `S_{(j,j′),k} := (1 − 4t) B_{(j,j′),k}` (arXiv:2611.06589,
Eq. (6.9), p.23). -/
noncomputable def gadgetSupply (P : Quadratic n) (t : ℝ) (π : Pair n) (k : ℕ) : ℝ :=
  (1 - 4 * t) * gadgetEarn P t π k

end LinearChoresCLS


