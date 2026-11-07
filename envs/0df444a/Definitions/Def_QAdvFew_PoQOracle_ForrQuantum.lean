-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_ForrQuantum
-- name    : QAdvFew_PoQOracle_ForrQuantum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:52:28.624403+00:00
-- url     : https://prove2.me/theorems/126c06e7-10c2-448d-bf28-4474d4674059
-- title:
--   Property (1) of Lemma 3.10
-- statement:
--   A family $\mathcal F_N$ of distributions on $\{0,1\}^N$ has **property (1)** of Lemma 3.10 if there is a quantum algorithm $\mathcal A$ making $\mathrm{polylog}(N)$ queries to its input and running in time $\mathrm{polylog}(N)$ such that
--   $$
--   \Bigl|\Pr_{x\leftarrow\mathcal F_N}[\mathcal A(x)\to1]-\Pr_{x\leftarrow\{0,1\}^N}[\mathcal A(x)\to1]\Bigr|\ge1-\frac1{N^2}.
--   $$
--
--   **Formalization Note** "Polylog" means one constant $c$ with at most $c(\log_2N+1)^c$ instructions and work qubits, for a family generated in time polynomial in $\log N$. The value $N=0$, where $1/N^2$ is undefined, is excluded.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Lemma 3.10(1), p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OQAlg
import Definitions.Def_QAdvFew_PoQOracle_forrOracle

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- Property (1) of Lemma 3.10 for a family `F_N` of distributions on `{0,1}^N` (Goldin, Lombardi,
Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Lemma 3.10(1),
p. 14 (PDF p. 16)): there is a quantum algorithm making `polylog(N)` queries to its input and running
in time `polylog(N)` with
`|Pr_{x←F_N}[A(x) → 1] − Pr_{x←{0,1}^N}[A(x) → 1]| ≥ 1 − 1/N²`.

**Formalization Note** "Polylog" is uniform: one constant `c` with at most `c (log₂ N + 1)^c`
instructions (queries included) and work qubits, and the family is generated in time polynomial in
`log N` (`OQAlg.Uniform`). The input `x` is the oracle `forrOracle N x`. `N = 0`, where `1/N²` is
undefined, is excluded. -/
def ForrQuantum (F : (N : ℕ) → PMF (Fin N → Bool)) : Prop :=
  ∃ (Q : OQAlg) (c : ℕ), Q.Uniform ∧ ∀ N : ℕ, 1 ≤ N →
    ((Q.circ N).length : ℝ) ≤ c * (Real.logb 2 N + 1) ^ c ∧
    (Q.W N : ℝ) ≤ c * (Real.logb 2 N + 1) ^ c ∧
    1 - 1 / (N : ℝ) ^ 2 ≤
      |∑ x : Fin N → Bool, (F N x).toReal * Q.accept (forrOracle N x) N -
        (∑ x : Fin N → Bool, Q.accept (forrOracle N x) N) / 2 ^ N|

end QAdvFew.PoQOracle


