-- Prove2me | Definitions.Def_ParamSDPTraj_Assumption33
-- name    : ParamSDPTraj_Assumption33
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:44.618504+00:00
-- url     : https://prove2.me/theorems/1c9e81f0-b8ef-4fd4-ab58-72db88fd1b59
-- title:
--   Assumption 3.3 (data continuity)
-- statement:
--   **Assumption 3.3** on $T$: the data $A_i(t)$, $b(t)$ and $C(t)$ depend continuously on $t$.
--
--   **Formalization Note** Matrices carry the entrywise topology, and continuity is required on $T$ only.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Assumption 3.3, p.12

import Mathlib

namespace ParamSDPTraj

/-- **Assumption 3.3 (data continuity).**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, Assumption 3.3, p.12: "Data A(t), b(t) and C(t) depend continuously on the time parameter
t".

**Formalization Note** `Matrix` carries the entrywise topology. Continuity is on T only. -/
def Assumption33 {n m : ℕ} (T : Set ℝ) (A : Fin m → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ → Fin m → ℝ) (C : ℝ → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i, ContinuousOn (A i) T) ∧ ContinuousOn b T ∧ ContinuousOn C T

end ParamSDPTraj


