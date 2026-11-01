-- Prove2me | Definitions.Def_ProcessingNetworks_EntropyIneq_IsConvergent
-- name    : ProcessingNetworks_EntropyIneq_IsConvergent
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:48.227534+00:00
-- url     : https://prove2.me/theorems/7c8f1261-4377-4ac9-9328-10afebb86695
-- title:
--   Appendix F, p.309 — convergent square matrix ($Q^k\to0$)
-- statement:
--   A $d\times d$ real matrix $Q$ is **convergent** if
--
--   $$
--   Q^k\to0\qquad (k\to\infty).
--   $$
--
--   This is statement (a) of Theorem F.1; for a substochastic $Q$ it is the Guide's alternative description of a *transient* matrix.
--
--   **Formalization Note** The limit is taken entrywise (the product topology on matrices), which agrees with convergence in any matrix norm.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Appendix F, p.309 (PDF 325)

import Mathlib

open Filter Topology

namespace ProcessingNetworks.EntropyIneq

/-- **Convergent matrix** (Dai & Harrison, *Processing Networks*, pre-publication draft 2020-4-2,
spnbook.org, Appendix F, p.309 (PDF 325)): a `d × d` real matrix `Q` is *convergent* if
`Qᵏ → 0` as `k → ∞`.

**Formalization Note** Convergence is in the entrywise (product) topology of
`Matrix (Fin d) (Fin d) ℝ`, which is the topology of every matrix norm. -/
def IsConvergent {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  Tendsto (fun k : ℕ => Q ^ k) atTop (𝓝 0)

end ProcessingNetworks.EntropyIneq


