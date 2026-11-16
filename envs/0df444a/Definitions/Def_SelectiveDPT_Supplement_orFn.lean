-- Prove2me | Definitions.Def_SelectiveDPT_Supplement_orFn
-- name    : SelectiveDPT_Supplement_orFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:25:29.887293+00:00
-- url     : https://prove2.me/theorems/2d1d42c9-139d-4420-85e5-9d1d6ca1c0cd
-- title:
--   $\mathsf{OR}_n$ and its hard distribution ($\tfrac12$ on $0^n$, $\tfrac1{2n}$ on weight-one strings)
-- statement:
--   For $x \in \{0,1\}^n$ (bits in $\mathbb Z_2$), $\mathsf{OR}_n(x) = 1$ if some $x_i = 1$ and $\mathsf{OR}_n(x) = 0$ otherwise. The domain is all of $\{0,1\}^n$.
--
--   The **hard distribution** of $\mathsf{OR}_n$ puts probability $1/2$ on the all-zeros string and $1/(2n)$ on each of the $n$ strings of Hamming weight one:
--   $$\mu_{\mathrm{OR}}(x) = \begin{cases} 1/2 & x = 0^n,\\ 1/(2n) & |x| = 1,\\ 0 & \text{otherwise.}\end{cases}$$
--
--   These are the function and the input distribution of the direct product theorems for $\mathsf{OR}_n$ (Theorems 1.4, 1.10(ii), 5.7).
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, §1, p.4 (OR_n); §4.1.2, p.30 (hard distribution)

import Mathlib
import Definitions.Def_SelectiveDPT_Supplement_searchDom

namespace SelectiveDPT.Supplement

/-- `OR_n(x) = 1` iff some bit of `x ∈ {0,1}^n` is `1` (arXiv:2609.26678, §1, p.4, the `OR_n`
problem; §4.1.2, p.30). The output bit is in `ZMod 2`; the domain is all of `{0,1}^n`. -/
def orFn (n : ℕ) (x : Fin n → ZMod 2) : ZMod 2 :=
  if ∃ i, x i = 1 then 1 else 0

/-- The hard distribution of `OR_n` (arXiv:2609.26678, §4.1.2, p.30: "The hard distribution `D`
for `OR_n` takes on the all zeroes string with probability `1/2`, and each hamming weight one
string with probability `1/(2n)`"), and `0` on every other string. -/
noncomputable def orDist (n : ℕ) (x : Fin n → ZMod 2) : ℝ :=
  if x = 0 then 1 / 2 else if x ∈ searchDom n then 1 / (2 * (n : ℝ)) else 0

end SelectiveDPT.Supplement


