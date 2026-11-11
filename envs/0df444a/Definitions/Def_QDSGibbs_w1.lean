-- Prove2me | Definitions.Def_QDSGibbs_w1
-- name    : QDSGibbs_w1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:34:20.639234+00:00
-- url     : https://prove2.me/theorems/95b21540-e18f-4478-8d0d-878d11a21363
-- title:
--   Transport norm $\|X\|_{W_1}$ and influence coefficient $D_\Psi(j)$
-- statement:
--   For a traceless Hermitian operator $X$, the **transport (Wasserstein-1) norm** is
--
--   $$
--   \|X\|_{W_1}=\frac12\inf\Big\{\sum_{j\in\Lambda}\|X_j\|_1:\ X=\sum_jX_j,\ X_j=X_j^*,\ \mathrm{Tr}_jX_j=0\Big\}.
--   $$
--
--   For a map $\Psi$ and a site $j$, the **influence coefficient** is
--
--   $$
--   D_\Psi(j)=\sup_{X=X^*\ne0,\ \mathrm{Tr}_jX=0}\frac{\|\Psi(X)\|_{W_1}}{\|X\|_1/2}.
--   $$
--
--   The quantum Dobrushin–Shlosman condition is a condition on sums of these coefficients.
--
--   **Formalization Note** Both take values in $[0,\infty]$. The infimum is over all decompositions; an operator with no admissible decomposition (non-Hermitian or not traceless) gets $\infty$ rather than the junk value $0$ of a real infimum.
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), (2.9), (2.11), p.13

import Mathlib
import Definitions.Def_QDSGibbs_traceNorm

open scoped Matrix ENNReal

namespace QDSGibbs

/-- The **transport (Wasserstein-1) norm** (arXiv:2610.03578, held file sha256 ede55815…, (2.9),
p.13): `‖X‖_{W1} = ½ inf { Σ_j ‖X_j‖₁ : X = Σ_j X_j, X_j = X_j^*, Tr_j X_j = 0 }`.

**Formalization Note** Valued in `ℝ≥0∞`. The infimum ranges over all decompositions indexed by the
sites; if there is none (`X` not Hermitian or not traceless) the value is `⊤`, never the junk `0` of
a real infimum of the empty set. On traceless Hermitian `X` it is the paper's value. -/
noncomputable def w1 {N : ℕ} {d : Fin N → ℕ} (X : Op d) : ℝ≥0∞ :=
  ⨅ (Xs : Fin N → Op d) (_ : X = ∑ j, Xs j ∧ ∀ j, (Xs j).IsHermitian ∧ ptr {j} (Xs j) = 0),
    ENNReal.ofReal (1 / 2 * ∑ j, traceNorm (Xs j))

/-- The **influence coefficient** of a map `Ψ` at site `j` (arXiv:2610.03578, (2.11), p.13):
`D_Ψ(j) = sup_{X = X^* ≠ 0, Tr_j X = 0} ‖Ψ(X)‖_{W1} / (‖X‖₁/2)`, the supremum over operators on the
full system.

**Formalization Note** Valued in `ℝ≥0∞` (an unbounded set gives `⊤`, not a real `sSup` junk `0`). -/
noncomputable def influence {N : ℕ} {d : Fin N → ℕ} (Ψ : Op d → Op d) (j : Fin N) : ℝ≥0∞ :=
  ⨆ (X : Op d) (_ : X.IsHermitian ∧ X ≠ 0 ∧ ptr {j} X = 0),
    w1 (Ψ X) / ENNReal.ofReal (traceNorm X / 2)

end QDSGibbs


