-- Prove2me | Definitions.Def_PSDPolyApprox_lpNorm
-- name    : PSDPolyApprox_lpNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:50:56.262066+00:00
-- url     : https://prove2.me/theorems/6545c14c-cd70-401d-8dfd-e80b9f1b88aa
-- title:
--   The norm $\|f\|_p=(\mathbb E|f|^p)^{1/p}$ on $H_n$
-- statement:
--   For $f:H_n\to\mathbb R$ and real $p\ge1$,
--   $$
--   \|f\|_p=\Bigl(\mathbb E_{x\sim\mu}\bigl[|f(x)|^p\bigr]\Bigr)^{1/p},
--   $$
--   where $\mu$ is the uniform probability measure on $H_n$.
--
--   **Formalization Note** Powers are real powers; the definition is applied only with $p\ge1$.
-- source:
--   Fawzi, On polyhedral approximations of the positive semidefinite cone, arXiv:1811.09649v1, §2.1, p.3

import Mathlib
import Definitions.Def_PSDPolyApprox_expect

namespace PSDPolyApprox

/-- **The `L^p(µ)` norm on the hypercube.**
Fawzi, arXiv:1811.09649v1, §2.1, p.3: "for f : Hn → R and p ≥ 1, deﬁne
∥f∥p = (E x∼µ[|f(x)|p])1/p."

`lpNorm p f = (E[|f|^p])^{1/p}` with real exponents (`Real.rpow`); the paper uses it for
`p ≥ 1`. -/
noncomputable def lpNorm {n : ℕ} (p : ℝ) (f : Cube n → ℝ) : ℝ :=
  (expect (fun x => |f x| ^ p)) ^ (1 / p)

end PSDPolyApprox


