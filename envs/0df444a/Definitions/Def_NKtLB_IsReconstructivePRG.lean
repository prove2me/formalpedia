-- Prove2me | Definitions.Def_NKtLB_IsReconstructivePRG
-- name    : NKtLB_IsReconstructivePRG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:02:20.530257+00:00
-- url     : https://prove2.me/theorems/d87acc0c-390b-4e02-80e9-4d34ac886d61
-- title:
--   The reconstructive PRG of Lemma 31
-- statement:
--   A family $F=(d,r,G,A,R)$ is a **reconstructive PRG with constant $c$** if:
--
--   1. $d(n,m,k)\le c\log^3(nk)+c$ and $r(n,m,k)\le cm+c$;
--   2. $G(x,z)$ and $A(x,z)$ have length $m$, and every query of $R$ has length $m$;
--   3. one machine computes $G$ and one computes $A$ on input $(1^n,1^m,1^k,x,z)$, one computes the query list of $R$ and one its output from the answers, each within $c\,((n+m)k)^c+c$ steps;
--   4. for every $n\ge1$, $1\le m\le 2^n$, $k\ge1$, every $x\in\{0,1\}^n$ and every $D:\{0,1\}^m\to\{0,1\}$ with
--   $$
--   \Pr_{z\sim U_d}[D(G(x;z))=1]-\Pr_{w\sim U_m}[D(w)=1]\ \ge\ 1/k,
--   $$
--   the reconstruction succeeds:
--   $$
--   \Pr_{w\sim U_r,\,z\sim U_d}\bigl[R^D(A(x,z),z,w)=x\bigr]\ \ge\ \frac{1}{c\,(mk)^c+c}.
--   $$
--
--   A distinguisher for $G(x;\cdot)$ thus yields a short randomized description of $x$, of $m+O(\log^3(n/\varepsilon))$ bits. This is the tool behind the reconstruction steps of §12.
--
--   **Formalization Note** (i) The security parameter is $\varepsilon=1/k$; Lemma 31 for a real $\varepsilon\in(0,1]$ is the case $k=\lceil1/\varepsilon\rceil$. (ii) The family is uniform, with one machine for all $n,m,k$, because Algorithm 1 runs $G$ inside an algorithm. (iii) Reconstruction is required for every $n\ge1$ and $1\le m\le2^n$, since the downstream lemmas apply Lemma 31 at all output lengths. (iv) The running time is $\mathrm{poly}((n+m)/\varepsilon)$ instead of the printed $\mathrm{poly}(n/\varepsilon)$: the output has $m$ bits and $m$ may be as large as $2^n$. In every application $m=O(n)$, where the two bounds agree. (v) A non-adaptive oracle computation is a query machine followed by an answer machine.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Lemma 31, pp.26–27

import Mathlib
import Definitions.Def_NKtLB_PRGFamily
import Definitions.Def_NKtLB_Machine
import Definitions.Def_NKtLB_tupleEnc
import Definitions.Def_NKtLB_prob

namespace NKtLB

/-- **The reconstructive PRG of Lemma 31, with constant `c`** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Lemma 31, pp.26–27): "there
exists a triple `(G, A, R^{(-)})` such that `G : {0,1}^n × {0,1}^d → {0,1}^m`,
`A : {0,1}^n × {0,1}^d → {0,1}^m`, `R^{(-)} : {0,1}^m × {0,1}^d × {0,1}^r → {0,1}^n`, and for
every `x ∈ {0,1}^n` and any `D : {0,1}^m → {0,1}` such that `Pr_{z∼U_d}[D(G(x; z)) = 1] −
Pr_{w∼U_m}[D(w) = 1] ≥ ε`, it holds that `Pr_{w∼U_r, z∼U_d}[R^D(A(x, z), z, w) = x] ≥ 1/poly(m/ε)`.
Here, we have `d = O(log³(n/ε))` and `r = O(m)`. Moreover, `G` and `A` can be computed in time
`poly(n/ε)`, and `R^D` can be computed in time `poly(n/ε)` with non-adaptive oracle access to `D`."

`IsReconstructivePRG c F` (with `ε = 1/k`):
1. `d(n,m,k) ≤ c·log³(n·k) + c` and `r(n,m,k) ≤ c·m + c`;
2. `G(x, z)` and `A(x, z)` have length `m`, and every query of `R` has length `m`;
3. one machine computes `G` and one computes `A` on input `(1^n, 1^m, 1^k, x, z)`, one computes the
   query list of `R` on `(1^n, 1^m, 1^k, a, z, w)` and one its output from the answers, each within
   `c·((n + m)·k)^c + c` steps;
4. for every `n ≥ 1`, `1 ≤ m ≤ 2^n`, `k ≥ 1`, `x ∈ {0,1}^n` and `D` with advantage at least `1/k`,
   the reconstruction succeeds with probability at least `1/(c·(m·k)^c + c)`.

**Formalization Note.** (i) The security parameter `ε > 0` is `1/k`, `k ∈ ℕ`; Lemma 31 for a real
`ε ∈ (0,1]` is the case `k = ⌈1/ε⌉`. (ii) The family is uniform: one machine for all `n, m, k`
(Algorithm 1 runs `G` inside an algorithm, p.75). (iii) The success guarantee is required for
every `n ≥ 1` and `1 ≤ m ≤ 2^n`, not only for "sufficiently large `n, m`": Lemma 103 and
Algorithm 1 apply Lemma 31 at all output lengths. (iv) The running time is
`poly((n+m)/ε)` rather than the printed `poly(n/ε)`: writing the `m` output bits takes `m` steps and
`m` may be as large as `2^n`, so the printed bound cannot hold. Every application has `m = O(n)`,
where the two bounds agree. (v) A non-adaptive oracle computation is a query machine followed by an
answer machine. -/
def IsReconstructivePRG (c : ℕ) (F : PRGFamily) : Prop :=
  (∀ n m k : ℕ, (F.d n m k : ℝ) ≤ c * (Real.logb 2 ((n : ℝ) * k)) ^ 3 + c) ∧
  (∀ n m k : ℕ, F.r n m k ≤ c * m + c) ∧
  (∀ (n m k : ℕ) (x z : List Bool), x.length = n → z.length = F.d n m k →
    (F.G n m k x z).length = m ∧ (F.A n m k x z).length = m) ∧
  (∀ (n m k : ℕ) (a z w : List Bool), a.length = m → z.length = F.d n m k →
    w.length = F.r n m k → ∀ q ∈ F.Rq n m k a z w, q.length = m) ∧
  (∃ MG MA MQ MR : Machine, ∀ n m k : ℕ, 1 ≤ k →
    (∀ x z : List Bool, x.length = n → z.length = F.d n m k →
      MG.Computes (c * ((n + m) * k) ^ c + c)
        (tupleEnc [List.replicate n true, List.replicate m true, List.replicate k true, x, z])
        (F.G n m k x z) ∧
      MA.Computes (c * ((n + m) * k) ^ c + c)
        (tupleEnc [List.replicate n true, List.replicate m true, List.replicate k true, x, z])
        (F.A n m k x z)) ∧
    (∀ a z w : List Bool, a.length = m → z.length = F.d n m k → w.length = F.r n m k →
      MQ.Computes (c * ((n + m) * k) ^ c + c)
        (tupleEnc [List.replicate n true, List.replicate m true, List.replicate k true, a, z, w])
        (tupleEnc (F.Rq n m k a z w)) ∧
      ∀ ans : List Bool, ans.length = (F.Rq n m k a z w).length →
        MR.Computes (c * ((n + m) * k) ^ c + c)
          (tupleEnc [List.replicate n true, List.replicate m true, List.replicate k true,
            a, z, w, ans])
          (F.Ra n m k a z w ans))) ∧
  (∀ n m k : ℕ, 1 ≤ n → 1 ≤ m → m ≤ 2 ^ n → 1 ≤ k → ∀ x : List Bool, x.length = n →
    ∀ D : List Bool → Bool,
      (1 : ℝ) / k ≤ prob (F.d n m k) (fun z => D (F.G n m k x z) = true) -
        prob m (fun w => D w = true) →
      1 / (c * ((m : ℝ) * k) ^ c + c) ≤
        prob (F.r n m k + F.d n m k) (fun v =>
          F.R n m k D (F.A n m k x (v.drop (F.r n m k))) (v.drop (F.r n m k))
            (v.take (F.r n m k)) = x))

end NKtLB


