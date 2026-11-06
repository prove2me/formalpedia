-- Prove2me | Definitions.Def_DRSub4633_qLarge
-- name    : DRSub4633_qLarge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:57:33.675407+00:00
-- url     : https://prove2.me/theorems/0dce23df-90c8-4d05-8903-d377bd4c4c6b
-- title:
--   The large weight $q_i=\max\{v_i,1-v_i\}$
-- statement:
--   For the state $x$ and a large coordinate $i$,
--   $$q_i=\max\{v_i,1-v_i\}.$$
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, Eq. (12), p.10

import Mathlib

namespace DRSub4633

/-- **The large-coordinate weight `qᵢ = max{vᵢ, 1 − vᵢ}`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, Eq. (12),
p.10, with `v = x_L`.

**Formalization Note.** Defined for every coordinate, used only for large ones. -/
noncomputable def qLarge {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) : ℝ :=
  max (x j) (1 - x j)

end DRSub4633


