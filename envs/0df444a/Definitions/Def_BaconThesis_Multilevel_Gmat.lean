-- Prove2me | Definitions.Def_BaconThesis_Multilevel_Gmat
-- name    : BaconThesis_Multilevel_Gmat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:36:39.287543+00:00
-- url     : https://prove2.me/theorems/c818c4af-bcf1-496c-99bc-d4a908112ee8
-- title:
--   Transition matrix $G$ of an $N$-level atom, eq. (12.4)
-- statement:
--   Given coupling coefficients $g_{ij}\in\mathbb C$ for $i>j$ of an $N$-level atom, the **transition matrix** $G$ is the $N\times N$ complex matrix with entries
--
--   $$
--   G_{ij} = \begin{cases} g_{ij}, & i>j,\\ 0, & i=j,\\ g_{ji}, & i<j. \end{cases}
--   $$
--
--   This is the matrix of eq. (12.4) of the thesis. It is symmetric ($G_{ij}=G_{ji}$) but in general not Hermitian, has zero diagonal, and $G_{ij}\neq 0$ means that the coupling drives a transition between levels $i$ and $j$. It is the matrix of the operator $\sum_{i>j} g_{ij}\sigma_{ij}$ in the level basis.
--
--   **Formalization Note** Levels are indexed by `Fin N` (0-based); only the values $g_{ij}$ with $j<i$ are used.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §12.1, eq. (12.4), p.156 (PDF p.173)

import Mathlib

namespace BaconThesis.Multilevel

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§12.1, eq. (12.4), p.156 (PDF p.173): the symmetric transition matrix `G` of an `N`-level atom with
coupling coefficients `g_ij` (`i > j`): `G_ij = g_ij` for `i > j`, `G_ii = 0`, and `G_ij = g_ji`
for `i < j`.

**Formalization Note.** Levels are `Fin N` (0-based in Lean, 1-based in the book). Only the
values `g i j` with `j < i` are used. `G` is symmetric, not Hermitian. -/
def Gmat {N : ℕ} (g : Fin N → Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => if j < i then g i j else if i < j then g j i else 0

end BaconThesis.Multilevel


