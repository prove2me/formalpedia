-- Prove2me | Definitions.Def_MaxCompForest_Supplement_expResid
-- name    : MaxCompForest_Supplement_expResid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:09:44.925331+00:00
-- url     : https://prove2.me/theorems/9c4bd12e-2c75-4162-88e7-50f4fd2db996
-- title:
--   Expected block residual $\mathbb E_{Q\sim\mu}S_Q$
-- statement:
--   For a probability law $\mu$ on the (finitely many) partitions of $V$, the **expected block residual** is the matrix
--
--   $$\mathbb E_{Q\sim\mu}S_Q=\sum_{Q}\mu(Q)\,S_Q .$$
--
--   Loewner bounds $\mathbb E_\mu S_Q\preceq aL$ by a multiple of the Laplacian express that one fixed law controls the expected squared bias $f^{\top}\mathbb E_\mu S_Q f\le a\,f^{\top}Lf$ of every signal simultaneously.
--
--   **Formalization Note** A partition law is a probability mass function on the finite type of partitions.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), (5.3)–(5.4), p.29 (PDF p.31); (J.2), p.59 (PDF p.61)

import Mathlib
import Definitions.Def_MaxCompForest_Supplement_blockResid
set_option autoImplicit false

namespace MaxCompForest.Supplement

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The expected block residual** `E_{Q∼μ} S_Q = ∑_Q μ(Q) S_Q` of a partition law `μ`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), (5.3) p.29, (5.4) p.29, (J.2) p.59.

**Formalization Note.** A partition law is a probability mass function on the finite type of partitions of
`V`, so the expectation is a finite sum. -/
noncomputable def expResid (W : V → ℝ) (μ : PMF (Finpartition (Finset.univ : Finset V))) : Matrix V V ℝ :=
  ∑ Q, (μ Q).toReal • blockResid W Q

end MaxCompForest.Supplement


