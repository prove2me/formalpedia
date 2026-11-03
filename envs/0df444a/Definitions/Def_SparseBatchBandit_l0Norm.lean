-- Prove2me | Definitions.Def_SparseBatchBandit_l0Norm
-- name    : SparseBatchBandit_l0Norm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:42.05205+00:00
-- url     : https://prove2.me/theorems/9c0d1078-a25e-4016-a7a6-a62144b39920
-- title:
--   The sparsity $\|v\|_0$
-- statement:
--   The **$\ell_0$ norm** of $v\in\mathbb R^d$ counts its nonzero coordinates:
--
--   $$
--   \|v\|_0=|\mathrm{supp}(v)|.
--   $$
--
--   It measures the sparsity of the parameter $\theta^\star$ and of the test vectors in the restricted eigenvalues.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, §2.1, p.5; Assumption 3, p.6

import Mathlib
import Definitions.Def_SparseBatchBandit_supp

namespace SparseBatchBandit

/-- The `ℓ₀` "norm" `‖v‖₀ = |supp(v)|`, Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, §2.1, p.5 (PDF 5) (`q = 0` in `‖v‖_q`) and
Assumption 3, p.6 (PDF 6). -/
noncomputable def l0Norm {d : ℕ} (v : Fin d → ℝ) : ℕ :=
  (supp v).card

end SparseBatchBandit


