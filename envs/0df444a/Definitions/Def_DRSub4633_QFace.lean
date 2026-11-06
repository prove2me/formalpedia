-- Prove2me | Definitions.Def_DRSub4633_QFace
-- name    : DRSub4633_QFace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:06:21.772699+00:00
-- url     : https://prove2.me/theorems/1be0b740-87ea-4065-8644-bd8c86570db9
-- title:
--   The function $Q_t(r)=e(a(t)+(1-a(t))r)$
-- statement:
--   $$Q_t(r)=e\big(a(t)+(1-a(t))r\big),\qquad r\in[0,1]^S,$$
--   with coordinatewise products.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, p.11

import Mathlib
import Definitions.Def_DRSub4633_eFace
import Definitions.Def_DRSub4633_aPath

namespace DRSub4633

/-- **The function `Q_t(r) = e(a(t) + (1 − a(t))r)`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, p.11 (products
coordinatewise).

**Formalization Note.** `r` is a function on `Fin n`; only its small coordinates are read. -/
noncomputable def QFace {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (t : ℝ) (r : Fin n → ℝ) : ℝ :=
  eFace f x (fun j => aPath x t j + (1 - aPath x t j) * r j)

end DRSub4633


