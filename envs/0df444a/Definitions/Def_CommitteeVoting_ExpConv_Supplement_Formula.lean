-- Prove2me | Definitions.Def_CommitteeVoting_ExpConv_Supplement_Formula
-- name    : CommitteeVoting_ExpConv_Supplement_Formula
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:20:32.934413+00:00
-- url     : https://prove2.me/theorems/5111d44d-b90d-4c34-826e-8ba97ec69aeb
-- title:
--   Theorem 2, (12), p. 16 — closed-form expression (corrected: first intolerable dishonest rank)
-- statement:
--   Let $m$ be the number of producers, $1\le k\le m$, $p\in[0,1]$, and $f^h,f^m$ probability mass functions on $\{0,\ldots,n\}$. Define
--
--   $$F^h(x)=\sum_{y=0}^x f^h(y),\quad F^m(x)=\sum_{y=0}^x f^m(y),\quad c=\lceil(1-p)k\rceil,\quad d=\lfloor pk\rfloor+1.$$
--
--   For $a$ honest producers and $b=m-a$ dishonest producers, put
--
--   $$H_{a,c}(x)=\sum_{j=0}^{\min(c,a+1)-1}\binom aj\left((1-F^h(x))^jF^h(x)^{a-j}-(1-F^h(x)+f^h(x))^j(F^h(x)-f^h(x))^{a-j}\right),$$
--
--   $$D_{b,d}(x)=\sum_{j=0}^{\min(d,b+1)-1}\binom bj(1-F^m(x)+f^m(x))^j(F^m(x)-f^m(x))^{b-j}.$$
--
--   The corrected right-hand side of (12) is
--
--   $$R=\sum_{\substack{0\le a\le m\\a\ge m-d+1}}\binom ma p^a(1-p)^{m-a}+\sum_{\substack{0\le a\le m\\c\le a\le m-d}}\binom ma p^a(1-p)^{m-a}\sum_{x=0}^n H_{a,c}(x)D_{m-a,d}(x).$$
--
--   This is the explicit expression whose equality with the independent finite success probability is the corrected Theorem 2.
--
--   **Formalization Note** Every sum over an empty range is zero. The inner ranges omit only terms with zero binomial coefficient ($j>a$ or $j>b$), preventing natural subtraction from truncating a negative exponent. Outer bounds are compared in the integers, including when $d=m+1$. Nonnegative ceilings and floors are converted to naturals only under the theorem's probability bounds. In all three positions the printed $\lceil pk\rceil$ is replaced by $d$; these values agree whenever $pk$ is nonintegral. The distinction is essential at integer $pk$, and the counterexample is retained in DISPROOF.md.
-- source:
--   Benhaim, Falk, Tsoukalas, Scaling Blockchains: Can Committee-based Consensus Help?, arXiv:2110.08673v2, p. 16, Theorem 2, (12); pp. 42–43, Claim 1 and (43)–(50), corrected as documented in DISPROOF.md

import Mathlib

namespace CommitteeVoting.ExpConv.Supplement

/-- CDF F(x)=Pr[X≤x] of a vote count on {0,...,n}. -/
noncomputable def voteCDF {n : ℕ} (f : PMF (Fin (n + 1))) (x : Fin (n + 1)) : ℝ :=
  ∑ y ∈ Finset.univ.filter (fun y : Fin (n + 1) => y ≤ x), (f y).toReal

/-- Required honest count. Under 0≤p≤1 the integer ceiling is nonnegative. -/
noncomputable def honestCutoff (k : ℕ) (p : ℝ) : ℕ :=
  (⌈(1 - p) * (k : ℝ)⌉ : ℤ).toNat

/-- First intolerable dishonest rank: the correction to the printed ceil(p*k). -/
noncomputable def dishonestCutoff (k : ℕ) (p : ℝ) : ℕ :=
  (⌊p * (k : ℝ)⌋ : ℤ).toNat + 1

/-- Honest order-statistic mass in (12). Terms with j>a are omitted because choose(a,j)=0;
this ensures a-j is ordinary subtraction on every retained term. -/
noncomputable def honestRankMass {n : ℕ} (a c : ℕ)
    (f : PMF (Fin (n + 1))) (x : Fin (n + 1)) : ℝ :=
  ∑ j ∈ Finset.range (min c (a + 1)), (Nat.choose a j : ℝ) *
    ((1 - voteCDF f x) ^ j * (voteCDF f x) ^ (a - j) -
      (1 - voteCDF f x + (f x).toReal) ^ j *
        (voteCDF f x - (f x).toReal) ^ (a - j))

/-- Strict CDF of the d-th largest dishonest count in (12), with b=m-a. -/
noncomputable def dishonestRankCDF {n : ℕ} (b d : ℕ)
    (f : PMF (Fin (n + 1))) (x : Fin (n + 1)) : ℝ :=
  ∑ j ∈ Finset.range (min d (b + 1)), (Nat.choose b j : ℝ) *
    (1 - voteCDF f x + (f x).toReal) ^ j *
      (voteCDF f x - (f x).toReal) ^ (b - j)

/-- Corrected (12), with c=ceil((1-p)k), d=floor(pk)+1, b=m-a.
Integer comparisons specify the outer ranges without natural subtraction underflow.
The summation variable a is restricted to 0,...,m, and empty ranges give zero. -/
noncomputable def correctedFormula (m k : ℕ) {n : ℕ} (p : ℝ)
    (fh fm : PMF (Fin (n + 1))) : ℝ :=
  let c := honestCutoff k p
  let d := dishonestCutoff k p
  (∑ a ∈ (Finset.range (m + 1)).filter
      (fun a : ℕ => (m : ℤ) - (d : ℤ) + 1 ≤ (a : ℤ)),
    (Nat.choose m a : ℝ) * p ^ a * (1 - p) ^ (m - a)) +
  ∑ a ∈ (Finset.range (m + 1)).filter
      (fun a : ℕ => c ≤ a ∧ (a : ℤ) ≤ (m : ℤ) - (d : ℤ)),
    (Nat.choose m a : ℝ) * p ^ a * (1 - p) ^ (m - a) *
      ∑ x : Fin (n + 1), honestRankMass a c fh x * dishonestRankCDF (m - a) d fm x

end CommitteeVoting.ExpConv.Supplement


