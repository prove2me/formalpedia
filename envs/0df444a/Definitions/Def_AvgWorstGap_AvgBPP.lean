-- Prove2me | Definitions.Def_AvgWorstGap_AvgBPP
-- name    : AvgWorstGap_AvgBPP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:46:33.576532+00:00
-- url     : https://prove2.me/theorems/c4cf32a0-3438-45f4-b004-d781fb5f5e1f
-- title:
--   Randomized errorless heuristic schemes and $\mathsf{AvgBPP}$
-- statement:
--   A distributional problem $(L,D)$ **admits a randomized errorless heuristic scheme** if there is a probabilistic polynomial-time algorithm $A$ such that for every $n$ and every $k\ge1$:
--
--   1. for every $x\in\mathrm{Support}(D_n)$, $\ \Pr_A\big[A(x,1^n,1^k)\in\{L(x),\bot\}\big]\ge 4/5$;
--   2. $\Pr_{x\sim D_n}\Big[\Pr_A\big[A(x,1^n,1^k)=\bot\big]<1/5\Big]\ge 1-1/k$.
--
--   $\mathsf{AvgBPP}$ is the class of distributional problems that admit such a scheme. The scheme halts within $p(|u|)$ steps on every input $u$ and random string $r\in\{0,1\}^{p(|u|)}$, for a polynomial $p$.
--
--   **Formalization Note** The paper says "for every $n,k\in\mathbb N$". The scheme is required only for $k\ge1$, since $1-1/k$ is undefined at $k=0$. $L(x)$ is the output bit $1$ or $0$, and $\bot$ is the one-symbol output $\bot$. The input $(x,1^n,1^k)$ uses the tuple encoding.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), §2.5, p.18

import Mathlib
import Definitions.Def_AvgWorstGap_InPrBPP
import Definitions.Def_NKtLB_tupleEnc
import Definitions.Def_AvgWorstGap_pairStr

namespace AvgWorstGap

open NKtLB

/-- The input `(x, 1^n, 1^k)` of a heuristic scheme, as one string. -/
def schemeInput (x : List Bool) (n k : ℕ) : List Bool := tupleEnc [x, unary n, unary k]

/-- **Randomized errorless heuristic scheme** (arXiv:2610.19162, version of October 30, 2026, §2.5,
p.18): "A distributional problem `(L, D)` is said to admit a randomized errorless heuristic scheme if
there exists a probabilistic polynomial-time algorithm `A` such that, for every `n, k ∈ ℕ`,
1. for every `x ∈ Support(Dn)`, `Pr_A [ A(x, 1^n, 1^k) ∈ {L(x), ⊥} ] ≥ 4/5`,
2. and `Pr_{x∼Dn} [ Pr_A [ A(x, 1^n, 1^k) = ⊥ ] < 1/5 ] ≥ 1 − 1/k`."

`IsErrorlessScheme L D A p`: on every input `u` and random string `r ∈ {0,1}^{p(|u|)}` the machine
`A` halts within `p(|u|)` steps, and for all `n` and all `k ≥ 1` the two conditions hold, with `A`
run on `(x, 1^n, 1^k)` and probabilities over its random string.

**Formalization Note.** `k ≥ 1` (at `k = 0` the bound `1 − 1/k` is undefined). `L(x)` is the
one-bit output, `⊥` the one-symbol output `⊥`. -/
def IsErrorlessScheme (L : Set (List Bool)) (D : ℕ → PMF (List Bool)) (A : Machine)
    (p : Polynomial ℕ) : Prop :=
  (∀ u r : List Bool, r.length = p.eval u.length →
      (A.run ∅ ⟨u, [], [], r⟩ (p.eval u.length)).state = A.halt) ∧
  ∀ n k : ℕ, 1 ≤ k →
    (∀ x ∈ (D n).support,
      4 / 5 ≤ prob (p.eval (schemeInput x n k).length) (fun r =>
        HaltsWithBit A ∅ ⟨schemeInput x n k, [], [], r⟩ (p.eval (schemeInput x n k).length) (x ∈ L) ∨
        A.HaltsWith ∅ ⟨schemeInput x n k, [], [], r⟩ (p.eval (schemeInput x n k).length)
          [Sym.bot])) ∧
    ENNReal.ofReal (1 - 1 / (k : ℝ)) ≤ (D n).toOuterMeasure {x | prob
        (p.eval (schemeInput x n k).length) (fun r =>
          A.HaltsWith ∅ ⟨schemeInput x n k, [], [], r⟩ (p.eval (schemeInput x n k).length)
            [Sym.bot]) < 1 / 5}

/-- **`AvgBPP`** (p.18): "We let AvgBPP denote the class of distributional problems that admit
randomized errorless heuristic schemes." -/
def AvgBPP (L : Set (List Bool)) (D : ℕ → PMF (List Bool)) : Prop :=
  ∃ (A : Machine) (p : Polynomial ℕ), IsErrorlessScheme L D A p

end AvgWorstGap


