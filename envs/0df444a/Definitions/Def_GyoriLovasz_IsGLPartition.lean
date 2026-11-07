-- Prove2me | Definitions.Def_GyoriLovasz_IsGLPartition
-- name    : GyoriLovasz_IsGLPartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:51:26.675844+00:00
-- url     : https://prove2.me/theorems/b1c571d4-4554-43e9-8425-83680ad67e2e
-- title:
--   Valid partition for an instance
-- statement:
--   For a graph $G$, terminals $T$ and capacities $c$, a **valid partition** $\langle V_t\rangle_{t\in T}$ consists of pairwise disjoint sets covering $V$ such that, for every $t\in T$,
--   $$t\in V_t,\qquad |V_t|=c_t+1,\qquad G[V_t]\text{ is connected to } t.$$
--
--   **Formalization Note** Parts are indexed by the terminal itself; $t\in V_t$ is part of "connected to".
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Theorem 1, p.5; Theorem 6, p.25

import Mathlib
import Definitions.Def_GyoriLovasz_ConnectedTo

namespace GyoriLovasz

/-- **A valid partition `⟨V_1, …, V_k⟩`.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Theorem 1, p.5, Theorem 6, p.25: "a partition ⟨V_1, ..., V_k⟩
such that, for every i ∈ [k], t_i ∈ V_i, |V_i| = c_i + 1, and G[V_i] is connected to t_i."

**Formalization Note.** Parts are indexed by the terminal itself, and only `parts t` for `t ∈ T` is
read. `t_i ∈ V_i` is part of `ConnectedTo`. -/
def IsGLPartition {V : Type*} [DecidableEq V] (G : DG V) (T : Finset V) (c : V → ℕ)
    (parts : V → Finset V) : Prop :=
  (∀ s ∈ T, ∀ t ∈ T, s ≠ t → Disjoint (parts s) (parts t)) ∧
    T.biUnion parts = G.verts ∧
    ∀ t ∈ T, (parts t).card = c t + 1 ∧ ConnectedTo G (parts t) t

end GyoriLovasz


