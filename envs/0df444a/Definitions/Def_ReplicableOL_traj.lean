-- Prove2me | Definitions.Def_ReplicableOL_traj
-- name    : ReplicableOL_traj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:44:16.798746+00:00
-- url     : https://prove2.me/theorems/33121b2c-c56d-44a2-bd63-6bd8c5237d60
-- title:
--   Trajectory $\tau(S,r)$
-- statement:
--   The **trajectory** of a learner on a loss sequence $S$ at seed $r$ is its action sequence $\tau(S,r)=(a_1,\dots,a_T)$. Replicability asks that two independent samples produce the same trajectory.
--
--   **Formalization Note** `traj 𝓛 S r t` is the action of round `t` (0-based) on the prefix of `S` at the seed `r`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.1, p.6

import Mathlib
import Definitions.Def_ReplicableOL_Learner
import Definitions.Def_NondualOpt_histPrefix

namespace ReplicableOL

/-- **Trajectory $\tau(S,r)$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.1, p.6. `τ := τ_{≤T} = (a_1, …, a_T)`.

**Formalization Note.** `traj 𝓛 S r t` is the action of round `t` (0-based) on the prefix `S_{<t}` of `S` at the seed `r`; the prefix is the published `NondualOpt.histPrefix` (the restriction of `S` to the rounds before `t`). -/
def traj {n T : ℕ} {R : Type*} [MeasurableSpace R] (𝓛 : Learner n T R)
    (S : Fin T → Fin n → ℝ) (r : R) : Fin T → Fin n :=
  fun t => 𝓛.act t (NondualOpt.histPrefix S t) r

end ReplicableOL


