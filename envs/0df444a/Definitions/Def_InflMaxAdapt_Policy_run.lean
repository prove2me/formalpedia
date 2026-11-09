-- Prove2me | Definitions.Def_InflMaxAdapt_Policy_run
-- name    : InflMaxAdapt_Policy_run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:33:19.478198+00:00
-- url     : https://prove2.me/theorems/62fff89a-be70-483c-81e1-625c82e04621
-- title:
--   Seed sequence $(v_1,\dots,v_k)$ of a policy
-- statement:
--   Given the external randomness $\omega$ and the cascade map $v \mapsto C(v)$ of the realization of the live edges or arcs, a policy probes the seeds
--   $$
--   v_i \;=\; \mathrm{rule}_i\big(\omega,\ C(v_1), \dots, C(v_{i-1})\big), \qquad i = 1, \dots, k ,
--   $$
--   defined recursively: every seed is chosen after the cascades of all earlier seeds have been observed.
--
--   **Formalization Note** Indices are 0-based; the defining equation is recorded as a lemma of the definition.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Section 1.1, printed p.2 (PDF p.3)

import Mathlib
import Definitions.Def_InflMaxAdapt_Policy

namespace InflMaxAdapt

/-- The seed sequence `(v_1, …, v_k)` of a policy (Section 1.1, printed p.2 = PDF p.3, of
de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)), given the external randomness `ω` and the cascade map `C : V → Finset V` of the realization
(`C v = C(v)`): `v_i = rule i ω (C(v_0), …, C(v_{i−1}))` (0-based), defined by recursion on `i`. -/
def Policy.run {V : Type} {k : ℕ} {Ω : Type} (π : Policy V k Ω) (ω : Ω) (C : V → Finset V) :
    Fin k → V
  | i => π.rule i ω (fun j => C (π.run ω C ⟨j.val, lt_trans j.isLt i.isLt⟩))
termination_by i => i.val
decreasing_by exact j.isLt

/-- The defining equation of `Policy.run`. -/
theorem Policy.run_eq {V : Type} {k : ℕ} {Ω : Type} (π : Policy V k Ω) (ω : Ω) (C : V → Finset V)
    (i : Fin k) :
    π.run ω C i = π.rule i ω (fun j => C (π.run ω C ⟨j.val, lt_trans j.isLt i.isLt⟩)) := by
  rw [Policy.run]

end InflMaxAdapt


