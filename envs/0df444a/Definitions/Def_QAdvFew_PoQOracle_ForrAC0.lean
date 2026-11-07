-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_ForrAC0
-- name    : QAdvFew_PoQOracle_ForrAC0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:51:40.658225+00:00
-- url     : https://prove2.me/theorems/d42cdc8e-f12b-4359-b842-6cfad882c950
-- title:
--   Property (2) of Lemma 3.10
-- statement:
--   A family $\mathcal F_N$ has **property (2)** of Lemma 3.10 if for any $C\in\mathsf{AC}^0(\mathrm{quasipoly}(N),O(1))$,
--   $$
--   \Bigl|\Pr_{x\leftarrow\mathcal F_N}[C(x)\to1]-\Pr_{x\leftarrow\{0,1\}^N}[C(x)\to1]\Bigr|\le\frac{\mathrm{polylog}(N)}{\sqrt N},
--   $$
--   even when $C$ is additionally given as input samples from any distribution independent of $x$.
--
--   **Formalization Note** For every exponent $k$ and depth $d$ there is $c$ such that, for every $N\ge1$, every length $m$, every distribution $\mu$ on $\{0,1\}^m$ and every $C(x,z)$ of size at most $2^{(\log_2N+1)^k}$ and depth at most $d$, the advantage is at most $c(\log_2N+1)^c/\sqrt N$.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Lemma 3.10(2) and the note after it, p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_IsAC0

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- Property (2) of Lemma 3.10 for a family `F_N` of distributions on `{0,1}^N` (Goldin, Lombardi,
Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Lemma 3.10(2) and
the note after it, p. 14 (PDF p. 16)): for any `C ∈ AC0(quasipoly(N), O(1))`,
`|Pr_{x←F_N}[C(x) → 1] − Pr_{x←{0,1}^N}[C(x) → 1]| ≤ polylog(N)/√N`, "even when `C` is additionally
given as input samples from any distribution independent of `x`".

**Formalization Note** Uniform reading: for every exponent `k` and depth `d` there is `c` such that
for every `N ≥ 1`, every extra input length `m`, every distribution `μ` of the extra input `z` and
every `AC0` circuit `C(x, z)` of size `≤ 2^{(log₂ N + 1)^k}` and depth `≤ d`, the advantage is at
most `c (log₂ N + 1)^c / √N`. The extra input generalizes the bare statement (take `m = 0`), as the
note says. -/
def ForrAC0 (F : (N : ℕ) → PMF (Fin N → Bool)) : Prop :=
  ∀ k d : ℕ, ∃ c : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ (m : ℕ) (μ : PMF (Fin m → Bool))
    (C : Circuit (Fin N ⊕ Fin m)), IsAC0 C ((2 : ℝ) ^ ((Real.logb 2 N + 1) ^ k)) d →
    |∑ x : Fin N → Bool, ∑ z : Fin m → Bool, (F N x).toReal * (μ z).toReal *
        (if C.eval1 (fun _ => false) (Sum.elim x z) then 1 else 0) -
      ∑ x : Fin N → Bool, ∑ z : Fin m → Bool, (μ z).toReal / 2 ^ N *
        (if C.eval1 (fun _ => false) (Sum.elim x z) then 1 else 0)| ≤
      c * (Real.logb 2 N + 1) ^ c / Real.sqrt N

end QAdvFew.PoQOracle


