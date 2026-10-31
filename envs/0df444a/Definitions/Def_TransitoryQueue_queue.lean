-- Prove2me | Definitions.Def_TransitoryQueue_queue
-- name    : TransitoryQueue_queue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:03:30.901897+00:00
-- url     : https://prove2.me/theorems/fb9ce272-1ae3-44fb-bef8-9994766e9f5d
-- title:
--   The queue length $Q_n(t)=A_n(t)-M_n(D_n(t))$
-- statement:
--   The **queue length** (6), counting the customer in service and all waiting customers, is
--
--   $$Q_n(t)=A_n(t)-M_n\bigl(D_n(t)\bigr),$$
--
--   the number of arrivals minus the number of job completions by time $t$.
--
--   **Formalization Note** $Q_n$ is defined by (6) literally. Since $M_n$ is truncated at $n$, $Q_n(t)$ can be negative when some service requirements are zero, exactly as with (6) on the page.
-- source:
--   Chakraborty and Honnappa, Strong Embeddings for Transitory Queueing Models, arXiv:1906.06740v1, eq. (6), p.8

import Mathlib
import Definitions.Def_TransitoryQueue_arrivals
import Definitions.Def_TransitoryQueue_completed
import Definitions.Def_TransitoryQueue_busy

namespace TransitoryQueue

/-- The queue length (6): `Q_n(t) = A_n(t) - M_n(D_n(t))`, the number of arrivals minus the
number of job completions, counting the customer in service and all waiting customers.
Chakraborty and Honnappa, *Strong Embeddings for Transitory Queueing Models*, arXiv:1906.06740v1, eq. (6), p.8.

**Formalization Note** `Q_n` is defined by (6) literally, as a real number. Because `M_n` is
truncated at `n` and not at `A_n(t)`, it may be negative when zero service requirements occur
(`V_i = 0`), exactly as (6) on the page. -/
noncomputable def queue {n : ℕ} (c : ℝ) (T : Fin n → ℝ) (ζ : Fin n → ℕ) (V : Fin n → ℝ)
    (t : ℝ) : ℝ :=
  (arrivals T ζ t : ℝ) - (completed c V (busy c T ζ V t) : ℝ)

end TransitoryQueue


