-- Prove2me | Definitions.Def_NestedLogitNBR_threshold
-- name    : NestedLogitNBR_threshold
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:41:06.565981+00:00
-- url     : https://prove2.me/theorems/9cabceca-2bf9-43e5-b146-de8f2f9b581f
-- title:
--   Threshold vector of Lemma 6
-- statement:
--   For $k\in\{1,\dots,n\}$ and $\rho\in[0,1]$, the threshold vector is
--
--   $$
--   z_1=\dots=z_{k-1}=1,\qquad z_k=\rho,\qquad z_{k+1}=\dots=z_n=0 .
--   $$
--
--   Lemma 6 shows that the fractional nest problem (8) has an optimal solution of this form: a nested-by-revenue assortment up to one fractional product.
--
--   **Formalization Note** Lean $k$ is $0$-based ($k$ stands for the paper's $k+1$); the constraint $\rho\in[0,1]$ is imposed where the vector is used.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256), Lemma 6, p. 21

import Mathlib

namespace NestedLogitNBR

/-- **Threshold vector of Lemma 6.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014,
doi:10.1287/opre.2014.1256), Lemma 6, p. 21: an optimal solution of (8) of the form
"`z*_i1 = 1, z*_i2 = 1, …, z*_i,k−1 = 1, z*_ik ∈ [0, 1], z*_i,k+1 = 0, …, z*_in = 0` for some
`k = 1, …, n`".

`threshold k ρ` is the vector with entries `1` before product `k`, `ρ` at `k` and `0` after.

**Formalization Note.** Products are `Fin n`, 0-based: Lean `k` is the paper's `k.val + 1`.
The value `ρ` is constrained to `[0, 1]` where the vector is used, not here. -/
def threshold {n : ℕ} (k : Fin n) (ρ : ℝ) : Fin n → ℝ :=
  fun j => if j < k then 1 else if j = k then ρ else 0

end NestedLogitNBR


