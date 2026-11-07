-- Prove2me | Definitions.Def_ReplicableOL_trajPrefix
-- name    : ReplicableOL_trajPrefix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:45:15.698357+00:00
-- url     : https://prove2.me/theorems/4c45f37e-753d-44f2-addc-a79618bf61b1
-- title:
--   Trajectory prefix $\tau_{\le t}(S,r)$
-- statement:
--   The **trajectory prefix** $\tau_{\le t}(S,r)=(a_1,\dots,a_t)$ collects the first $t$ actions. It is used by the canonical-trajectory lemma, which is stated for every prefix.
--
--   **Formalization Note** `t : Fin (T+1)` runs over `0, …, T`, and `trajPrefix 𝓛 t S r` is indexed by `Fin t`: its entries are the first `t` actions.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.1, p.6

import Mathlib
import Definitions.Def_ReplicableOL_traj

namespace ReplicableOL

/-- **Trajectory prefix $\tau_{\le t}(S,r)$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.1, p.6. `τ_{≤t}(S, R) := (a_1, …, a_t)`, a function of `(S_{<t}, R)`.

**Formalization Note.** `t : Fin (T+1)` runs over `0, …, T`, and `trajPrefix 𝓛 t S r` is indexed by `Fin t`: its entries are the first `t` actions. -/
def trajPrefix {n T : ℕ} {R : Type*} [MeasurableSpace R] (𝓛 : Learner n T R)
    (t : Fin (T + 1)) (S : Fin T → Fin n → ℝ) (r : R) : Fin t → Fin n :=
  fun i => traj 𝓛 S r ⟨i, by omega⟩

end ReplicableOL


