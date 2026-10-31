-- Prove2me | Definitions.Def_TransitoryQueue_completed
-- name    : TransitoryQueue_completed
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:44.559184+00:00
-- url     : https://prove2.me/theorems/f12bd3d3-cb58-4d42-a994-4e1800e03e87
-- title:
--   The truncated renewal process $M_n(t)=\sup\{0\le m\le n:\sum_{i\le m}V_i\le c_nt\}$
-- statement:
--   For a server of efficiency $c>0$ and service requirements $V_1,\dots,V_n\ge0$, the **truncated renewal process** (5) is
--
--   $$M_n(t)=\sup\Bigl\{0\le m\le n:\ \sum_{i=1}^{m}V_i\le c\,t\Bigr\},$$
--
--   the number of jobs the server can complete by time $t$ when working continuously.
--
--   **Formalization Note** For $t\ge0$ the index $m=0$ always qualifies, so this is a maximum. As on the page, $M_n$ is truncated at $n$ and not at the number of arrivals, so it also counts zero-length jobs of customers who have not yet arrived.
-- source:
--   Chakraborty and Honnappa, Strong Embeddings for Transitory Queueing Models, arXiv:1906.06740v1, eq. (5), p.6

import Mathlib

namespace TransitoryQueue

/-- The truncated renewal process (5): `M_n(t) = sup{0 ≤ m ≤ n : Σ_{i=1}^{m} V_i ≤ c_n t}`, the
number of jobs a server of efficiency `c` completes by time `t` when working continuously.
Chakraborty and Honnappa, *Strong Embeddings for Transitory Queueing Models*, arXiv:1906.06740v1, eq. (5), p.6.

**Formalization Note** The supremum of a finite set of natural numbers is `Finset.sup`. For
`t ≥ 0` and `c > 0`, `m = 0` qualifies, so it is the largest qualifying `m`; for `c t < 0`
the set is empty and the value is `0` (this case is never used). As on the page, `M_n` is
truncated at `n` and reads every `V_i`, `i ≤ n`, whether or not that customer has arrived. -/
noncomputable def completed {n : ℕ} (c : ℝ) (V : Fin n → ℝ) (t : ℝ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun m => ∑ i : Fin n with i.val < m, V i ≤ c * t)).sup id

end TransitoryQueue


