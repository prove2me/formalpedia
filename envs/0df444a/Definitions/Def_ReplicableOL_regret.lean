-- Prove2me | Definitions.Def_ReplicableOL_regret
-- name    : ReplicableOL_regret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:45:24.93749+00:00
-- url     : https://prove2.me/theorems/de707891-6260-4757-849b-4ab5be9af1ec
-- title:
--   Realized regret $\mathrm{Reg}_T(S,r)$
-- statement:
--   Regret is measured against the best fixed expert on the realized losses:
--   $$
--   \mathrm{Reg}_T(S,r)=\sum_{t\le T}\ell_t(a_t)-\min_{i\in[n]}\sum_{t\le T}\ell_t(i).
--   $$
--   This is realized regret, not pseudo-regret. The main theorem is a lower bound on its upper tail.
--
--   **Formalization Note** All rounds count, trailing rounds of Construction C included. `[NeZero n]` makes the minimum over experts well defined.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.1, p.6

import Mathlib
import Definitions.Def_ReplicableOL_traj

namespace ReplicableOL

/-- **Realized regret $\mathrm{Reg}_T(S,r)$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.1, p.6. `Reg_T(S, R) := Σ_{t≤T} ℓ_t(a_t) − min_{i∈[n]} Σ_{t≤T} ℓ_t(i)`.

**Formalization Note.** All rounds count, trailing rounds of Construction C included. `[NeZero n]` makes the minimum over experts well defined. -/
noncomputable def regret {n T : ℕ} [NeZero n] {R : Type*} [MeasurableSpace R] (𝓛 : Learner n T R)
    (S : Fin T → Fin n → ℝ) (r : R) : ℝ :=
  ∑ t, S t (traj 𝓛 S r t) - Finset.univ.inf' Finset.univ_nonempty (fun i => ∑ t, S t i)

end ReplicableOL


