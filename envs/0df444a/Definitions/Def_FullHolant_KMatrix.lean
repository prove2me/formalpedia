-- Prove2me | Definitions.Def_FullHolant_KMatrix
-- name    : FullHolant_KMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:58:10.522077+00:00
-- url     : https://prove2.me/theorems/71d53edf-41d1-41f8-b144-1b08f54c6c4e
-- title:
--   The K-coordinate matrix $K=\tfrac1{\sqrt2}\begin{pmatrix}1&1\\ i&-i\end{pmatrix}$, its inverse and $X$
-- statement:
--   The **K-coordinate matrix** and its inverse are
--
--   $$
--   K=\frac1{\sqrt2}\begin{pmatrix}1&1\\ i&-i\end{pmatrix},\qquad K^{-1}=\frac1{\sqrt2}\begin{pmatrix}1&-i\\ 1&i\end{pmatrix},
--   $$
--
--   and $X=\begin{pmatrix}0&1\\1&0\end{pmatrix}$ is the binary disequality. Rows are indexed by the output bit and columns by the input bit, so that applying $K$ to an arity-$r$ signature $f$ means $K^{\otimes r}f$ (the column-vector action). One has $K^{\mathsf T}K=X$.
--
--   Passing to K-coordinates, $\hat F=K^{-1}F$, turns the equality edges of ordinary Holant into disequality edges; this is the basis in which charges are defined.
--
--   **Formalization Note** The matrices are indexed by `Bool` (`false` = 0, `true` = 1); `K⁻¹K = I` and `KᵀK = X` are checked in the mission's sanity file.
-- source:
--   Liu–Meng–Wang, A Full Complexity Dichotomy for Complex-Valued Boolean Holant Problems, arXiv:2610.00081 (held version, sha256 d67958c6…), §F.2.6, Eq. (F.1), p.F-8 (PDF p.26); §F.2.2, p.F-6

import Mathlib

set_option autoImplicit false

namespace FullHolant

/-- The **K-coordinate matrix** `K = (1/√2) [[1, 1], [i, −i]]` (F.1), with rows indexed by the
output bit and columns by the input bit (`false = 0`, `true = 1`), so that `Sig.transform matK f`
is `K^{⊗r} f`. Liu–Meng–Wang, arXiv:2610.00081 (held version, sha256 d67958c6…), §F.2.6, Eq. (F.1),
p.F-8 (PDF p.26). -/
noncomputable def matK : Matrix Bool Bool ℂ :=
  fun a b => (1 / (Real.sqrt 2 : ℂ)) * (if a then (if b then -Complex.I else Complex.I) else 1)

/-- The inverse `K⁻¹ = (1/√2) [[1, −i], [1, i]]` of (F.1), same indexing. Liu–Meng–Wang, §F.2.6,
Eq. (F.1), p.F-8 (PDF p.26). -/
noncomputable def matKinv : Matrix Bool Bool ℂ :=
  fun a b => (1 / (Real.sqrt 2 : ℂ)) * (if b then (if a then Complex.I else -Complex.I) else 1)

/-- The binary disequality `X = (≠₂) = [[0, 1], [1, 0]]`. Liu–Meng–Wang, §F.2.2, p.F-6 (PDF p.24). -/
def matX : Matrix Bool Bool ℂ := fun a b => if a = b then 0 else 1

end FullHolant


