-- Prove2me | Definitions.Def_AvgWorstGap_Supplement_AvgP
-- name    : AvgWorstGap_Supplement_AvgP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:05:03.829403+00:00
-- url     : https://prove2.me/theorems/84d7ca1b-be52-4674-b52d-0f896c911fbc
-- title:
--   Errorless heuristic schemes, $\mathsf{AvgP}$, and $\mathrm{DistPH}\subseteq\mathsf{AvgP}$
-- statement:
--   Let $L\subseteq\{0,1\}^*$ and let $D=\{D_n\}_{n\in\mathbb N}$ be a family of distributions on binary strings. The distributional problem $(L,D)$ **admits an errorless heuristic scheme** if there are a deterministic machine $A$ and a polynomial $p$ such that $A$ halts within $p(|u|)$ steps on every input $u$, and for every $n$ and every $k\ge1$:
--
--   1. for every $x\in\operatorname{Support}(D_n)$, $A(x,1^n,1^k)\in\{L(x),\bot\}$;
--   2. $$\Pr_{x\sim D_n}\big[A(x,1^n,1^k)\neq\bot\big]\ \ge\ 1-\frac1k.$$
--
--   $\mathsf{AvgP}$ is the class of distributional problems that admit an errorless heuristic scheme. $\mathrm{DistPH}\subseteq\mathsf{AvgP}$ means that $(L,D)\in\mathsf{AvgP}$ for every $L\in\mathsf{PH}$ and every polynomial-time samplable family $D\in\mathsf{PSAMP}$.
--
--   This is the deterministic counterpart of $\mathsf{AvgBPP}$: the algorithm never errs, may answer $\bot$ ("don't know"), and answers $\bot$ on at most a $1/k$ fraction of the $D_n$-mass.
--
--   **Formalization Note** $k\ge1$, since $1-1/k$ is undefined at $k=0$ (the same reading as the published $\mathsf{AvgBPP}$). $L(x)$ is a one-bit output and $\bot$ the one-symbol output $\bot$; the triple $(x,1^n,1^k)$ is the published scheme input. $\mathsf{PSAMP}$ is the published definition, which requires the sampler for every $n\in\mathbb N$.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), §2.5, pp.17–18 (errorless heuristic scheme, AvgP, DistC)

import Mathlib
import Definitions.Def_AvgWorstGap_AvgBPP
import Definitions.Def_AvgWorstGap_InPSAMP
import Definitions.Def_AvgWorstGap_InSigmaPO

namespace AvgWorstGap.Supplement

open NKtLB

/-- **Errorless heuristic scheme** (Goldberg, Hu, Lu, Lyu, Oliveira, *The Gap Between Average-Case
and Worst-Case Complexity*, arXiv:2610.19162, version of October 30, 2026, §2.5, p.17): "A
distributional problem `(L, D)` is said to admit an errorless heuristic scheme if there exists a
deterministic polynomial-time algorithm `A` such that, for every `n, k ∈ ℕ`,
1. for every `x ∈ Support(Dn)`, `A(x, 1^n, 1^k) ∈ {L(x), ⊥}`,
2. and `Pr_{x∼Dn} [ A(x, 1^n, 1^k) ≠ ⊥ ] ≥ 1 − 1/k`."

`IsDetErrorlessScheme L D A p`: on every input `u` (oracle `∅`, auxiliary, guess and randomness
tapes empty) the machine `A` halts within `p(|u|)` steps, and for all `n` and all `k ≥ 1` the two
conditions hold, with `A` run on `(x, 1^n, 1^k)` (the base `schemeInput`).

**Formalization Note.** `k ≥ 1` (at `k = 0` the bound `1 − 1/k` is undefined), as in the base
`IsErrorlessScheme`. `L(x)` is the one-bit output, `⊥` the one-symbol output `⊥`; "`A(x, 1^n, 1^k)
≠ ⊥`" is "`A` does not halt with output `⊥`". -/
def IsDetErrorlessScheme (L : Set (List Bool)) (D : ℕ → PMF (List Bool)) (A : Machine)
    (p : Polynomial ℕ) : Prop :=
  (∀ u : List Bool, (A.run ∅ ⟨u, [], [], []⟩ (p.eval u.length)).state = A.halt) ∧
  ∀ n k : ℕ, 1 ≤ k →
    (∀ x ∈ (D n).support,
      HaltsWithBit A ∅ ⟨schemeInput x n k, [], [], []⟩ (p.eval (schemeInput x n k).length)
          (x ∈ L) ∨
        A.HaltsWith ∅ ⟨schemeInput x n k, [], [], []⟩ (p.eval (schemeInput x n k).length)
          [Sym.bot]) ∧
    ENNReal.ofReal (1 - 1 / (k : ℝ)) ≤ (D n).toOuterMeasure {x |
      ¬ A.HaltsWith ∅ ⟨schemeInput x n k, [], [], []⟩ (p.eval (schemeInput x n k).length)
        [Sym.bot]}

/-- **`AvgP`** (p.18): "We let AvgP denote the class of distributional problems that admit an
errorless heuristic scheme." -/
def AvgP (L : Set (List Bool)) (D : ℕ → PMF (List Bool)) : Prop :=
  ∃ (A : Machine) (p : Polynomial ℕ), IsDetErrorlessScheme L D A p

/-- **`DistPH ⊆ AvgP`** (Theorem 4.1, p.34; §2.5, p.17: `DistC` is the set of `(L, D)` with
`L ∈ C` and `D ∈ PSAMP`): for every `L ∈ PH` and every `D ∈ PSAMP`, `(L, D) ∈ AvgP`. -/
def DistPHSubAvgP : Prop :=
  ∀ L : Set (List Bool), InPH L → ∀ D : ℕ → PMF (List Bool), InPSAMP D → AvgP L D

end AvgWorstGap.Supplement


