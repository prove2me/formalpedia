-- Prove2me | Definitions.Def_TaoFivePrimes_RepresentationCount
-- name    : TaoFivePrimes_RepresentationCount
-- status  : Definition
-- author  : @Patrick
-- created : 2026-09-07T02:17:33.673162+00:00
-- url     : https://prove2.me/theorems/48e5337b-62c2-4e24-8c38-b047da4fe522
-- title:
--   Tao's weighted three-prime representation count (K = 1000)
-- statement:
--   Let $x,H$ be natural numbers. This defines the weighted count in equation (8.10) of Tao's five-primes paper, with the parameter fixed at $K=1000$ as in the proof of Theorem 8.2. Write
--
--   $$\eta_0(t)=4\max(0,\log2-|\log(2t)|)\quad(t>0),\qquad\eta_0(t)=0\quad(t\leq0),$$
--   $$\eta_1(t)=\max(0,1-10\operatorname{dist}(t,[1/5,4/5])).$$
--
--   For a natural bound $N$, set $A_N(n)=\Lambda(n)\mathbf1_{\gcd(n,\prod_{p\leq\sqrt N}p)=1}$. The representation count is
--
--   $$R(x,H)=\sum_{n_1,n_2\leq x}\sum_{n_3\leq\lfloor x/1000\rfloor}\sum_{1\leq h_1,h_2,h_3\leq\lfloor H/3\rfloor} A_x(n_1)\eta_1(n_1/x)A_x(n_2)\eta_1(n_2/x)A_{\lfloor x/1000\rfloor}(n_3)\eta_0(1000n_3/x)\mathbf1_{x=n_1+n_2+n_3+h_1+h_2+h_3}.$$
--
--   The application takes $H=4\cdot10^{14}$. A positive count yields three odd primes with sum in $[x-H,x-2]$; the difficult analytic task is to establish that positivity. The finite natural-number ranges retain their upper endpoints. The zero indices contribute zero because $\Lambda(0)=0$.
--
--   **Formalization Note** Natural division supplies the floor bounds. For nonnegative real $y$, the primes at most $\sqrt y$ are precisely those at most $\operatorname{Nat.sqrt}(\lfloor y\rfloor)$, so the third primorial has the paper's real square-root cutoff.
-- source:
--   Terence Tao, https://arxiv.org/abs/1201.6656, equations (1.7) and (8.10), the definition of eta1 at the start of Section 8, and the choice K=10^3 following (8.11).

import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Primorial
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The weighted representation count in Tao's five-primes proof

Source: Terence Tao, https://arxiv.org/abs/1201.6656, equations (1.7), (8.10),
and the definition of η₁ at the beginning of Section 8. The proof fixes `K = 1000`.
Natural division gives the integer bounds in the finite sums. Primorial cutoffs
are inclusive, as in the paper's Section 2 conventions.
-/

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace TaoFivePrimes

/-- Tao's logarithmic cutoff, extended by zero to nonpositive arguments. -/
noncomputable def eta0 (t : ℝ) : ℝ :=
  if 0 < t then 4 * max 0 (Real.log 2 - |Real.log (2 * t)|) else 0

/-- The trapezoidal cutoff used for the first two primes in Section 8. -/
noncomputable def eta1 (t : ℝ) : ℝ :=
  max 0 (1 - 10 * Metric.infDist t (Set.Icc (1 / 5 : ℝ) (4 / 5)))

/-- Von Mangoldt with all prime factors at most `sqrt N` removed. -/
noncomputable def siftedVonMangoldt (N n : ℕ) : ℝ :=
  if n.Coprime (primorial (Nat.sqrt N)) then Λ n else 0

/-- Equation (8.10), at `K = 1000`, with a general gap budget `H`.
The three positive shifts each have upper bound `H / 3`. -/
noncomputable def representationCount (x H : ℕ) : ℝ :=
  ∑ n₁ ∈ Finset.range (x + 1),
  ∑ n₂ ∈ Finset.range (x + 1),
  ∑ n₃ ∈ Finset.range (x / 1000 + 1),
  ∑ h₁ ∈ Finset.Icc 1 (H / 3),
  ∑ h₂ ∈ Finset.Icc 1 (H / 3),
  ∑ h₃ ∈ Finset.Icc 1 (H / 3),
    if x = n₁ + n₂ + n₃ + h₁ + h₂ + h₃ then
      siftedVonMangoldt x n₁ * eta1 ((n₁ : ℝ) / x) *
      siftedVonMangoldt x n₂ * eta1 ((n₂ : ℝ) / x) *
      siftedVonMangoldt (x / 1000) n₃ * eta0 (1000 * (n₃ : ℝ) / x)
    else 0

end TaoFivePrimes


