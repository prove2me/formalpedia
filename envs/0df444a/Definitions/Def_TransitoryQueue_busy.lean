-- Prove2me | Definitions.Def_TransitoryQueue_busy
-- name    : TransitoryQueue_busy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:02:26.920215+00:00
-- url     : https://prove2.me/theorems/76cc9a75-168d-47f1-81d5-48bc256ff88c
-- title:
--   The busy time $D_n(t)$ of the non-idling server
-- statement:
--   For the RS$(G,p)/G/1$ queue with efficiency $c$, the remaining workload at time $s$ is $\phi(W_n-c\cdot\mathrm{id})(s)$. The **busy time** up to $t$ is the time the queue is busy:
--
--   $$D_n(t)=\mathrm{Leb}\bigl\{s\in[0,t]:\ \phi(W_n-c\cdot\mathrm{id})(s)>0\bigr\}.$$
--
--   The idle time (7) is $I_n(t)=t-D_n(t)$.
--
--   **Formalization Note** The paper defines $D_n(t)$ only in words ("the amount of time the queue stays busy till time $t$") for a non-preemptive, non-idling server; this is its formal version. The measure is converted to a real number; the set is bounded.
-- source:
--   Chakraborty and Honnappa, Strong Embeddings for Transitory Queueing Models, arXiv:1906.06740v1, §2.1, p.4; Theorem 2.10, p.7; p.8 before eq. (6)

import Mathlib
import Definitions.Def_TransitoryQueue_load
import Definitions.Def_TransitoryQueue_reflect
open MeasureTheory

namespace TransitoryQueue

/-- The busy time `D_n(t)`: the amount of time in `[0, t]` during which the queue is busy,
i.e. the remaining workload `φ(W_n - c_n · id)` is positive.
Chakraborty and Honnappa, *Strong Embeddings for Transitory Queueing Models*, arXiv:1906.06740v1, §2.1, p.4 (the server is "non-preemptive, non-idling"), Theorem 2.10, p.7 ("the total
remaining workload at time t can be expressed as φ(W_n − c_n · id)(t)"), and p.8 ("Denoting by
D_n(t) the amount of time the queue stays busy till time t").

**Formalization Note** The page defines `D_n` only in words. It is the Lebesgue measure of
`{s ∈ [0, t] : φ(W_n - c·id)(s) > 0}`, converted to a real number (the set is bounded). The
idle time (7) is `I_n(t) = t - D_n(t)`. -/
noncomputable def busy {n : ℕ} (c : ℝ) (T : Fin n → ℝ) (ζ : Fin n → ℕ) (V : Fin n → ℝ)
    (t : ℝ) : ℝ :=
  (volume {s : ℝ | s ∈ Set.Icc 0 t ∧ 0 < reflect (fun u => load T ζ V u - c * u) s}).toReal

end TransitoryQueue


