-- Prove2me | Definitions.Def_SumReLU_cdrOutput
-- name    : SumReLU_cdrOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:25:32.143198+00:00
-- url     : https://prove2.me/theorems/bca852b9-1a4b-43c0-860e-98ee45c10496
-- title:
--   Input, output and sample-bound conventions of the CDR program
-- statement:
--   The coarse direction recovery program of Proposition 4.1 receives $k,\lambda,\delta$ in memory (cells $0,1,2$) and the dimension through the machine dimension $d+1$. When it halts, pointer register $2$ holds the list length $m$ and, with $b$ the cell held in pointer register $1$, the $j$-th raw vector ($j<m$) occupies cells $b+jd,\dots,b+jd+d-1$. The output list consists of the normalized raw vectors $r_j=\mathrm{raw}_j/\|\mathrm{raw}_j\|_2$.
--
--   The sample bound is $N=C\,(d+k+1/\lambda+1/\delta)^C$, the reading of $\mathrm{poly}(d,k,1/\lambda,1/\delta)$.
--
--   **Formalization Note** Exact unit vectors require a square root, which the arithmetic machine does not have; the decoder normalizes, and Proposition 4.1 requires the raw vectors to be nonzero. The formats are conventions.
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), Proposition 4.1, p.24 (PDF p.26); Algorithm 7, p.33 (PDF p.35); §2, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_GaussMixHH_Machine

namespace SumReLU

/-- **The input list of the CDR program** (Proposition 4.1; Algorithm 7, line 1), in memory from
cell `0`: `k, λ, δ`. The machine dimension is `d + 1` (one example per `sample`), held in
pointer `0` by `GaussMixHH.initState`.

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), Proposition 4.1, p.24 (PDF p.26); Algorithm 7, p.33 (PDF p.35): "Input: Sample access to a
Gaussian sum of k ReLUs D, positive parameters λ, δ ∈ (0, 1)."

**Formalization Note.** The page fixes no input or output format; these are conventions. -/
noncomputable def cdrInput (k : ℕ) (lam δ : ℝ) : List ℝ := [(k : ℝ), lam, δ]

/-- The length `m` of the output list of a halted state: pointer register `2`. -/
def listLength (s : GaussMixHH.State) : ℕ := (s.core.ptrs 2).toNat

/-- The `j`-th raw output vector: coordinate `i < d` is memory cell `p[1] + j·d + i`. The
output list is `r_j = rawVec d s j/‖rawVec d s j‖` for `j < listLength s`.

**Formalization Note.** Exact unit vectors need a square root, which the arithmetic machine lacks;
the decoded list consists of the normalizations of the raw vectors, which are required nonzero. -/
noncomputable def rawVec (d : ℕ) (s : GaussMixHH.State) (j : ℕ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i : Fin d => s.core.mem (s.core.ptrs 1 + (j : ℤ) * (d : ℤ) + (i : ℤ))

/-- The sample bound `N = C · (d + k + 1/λ + 1/δ)^C`, the reading of `poly(d, k, 1/λ, 1/δ)`
(§2, p.9, PDF p.11) with one constant `C`. -/
noncomputable def cdrSampleBound (C d k : ℕ) (lam δ : ℝ) : ℝ :=
  (C : ℝ) * ((d : ℝ) + k + 1 / lam + 1 / δ) ^ C

end SumReLU


