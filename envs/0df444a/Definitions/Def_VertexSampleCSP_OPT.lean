-- Prove2me | Definitions.Def_VertexSampleCSP_OPT
-- name    : VertexSampleCSP_OPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:54:26.448396+00:00
-- url     : https://prove2.me/theorems/5330a30e-6d27-48e7-882e-61f48bd8ceac
-- title:
--   Optimum $\mathrm{OPT}(\mathcal I)$ of an instance
-- statement:
--   For an instance $\mathcal I$ on $V$, the **optimum** is
--
--   $$\mathrm{OPT}(\mathcal I)=\max_{\sigma\in[q]^V}F_{\mathcal I}(\sigma).$$
--
--   It is the quantity the sampling estimator is meant to recover.
--
--   **Formalization Note** The maximum over the finite set of assignments is written as a real supremum. For $q\ge1$ (or $V$ empty) the index is finite and nonempty, so the supremum is attained. For $q=0$ and $V\neq\emptyset$ there is no assignment and the real supremum is the default value $0$; every statement of the mission assumes $q\ge1$.
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), §1.1, p.2 (PDF p.4); Appendix A, "Instances", p.13 (PDF p.15)

import Mathlib
import Definitions.Def_VertexSampleCSP_Instance

namespace VertexSampleCSP

/-- **Optimum `OPT(I)`.** Chang, *Optimal Vertex Sampling for Constraint Satisfaction Problems*,
STOC 2027 submission (manuscript sha256 1e0edd23…), §1.1, p.2 (PDF p.4), and Appendix A,
"Instances", p.13 (PDF p.15): `OPT(I) = max_{σ ∈ [q]^V} F_I(σ)`.

**Formalization Note.** The maximum over the finite set of assignments `V → Fin q` is written as a
real `⨆`. When `q ≥ 1` (or `V` is empty) the index type is finite and nonempty, so the supremum is
attained and is the printed maximum. When `q = 0` and `V` is nonempty there is no assignment and the
real `⨆` returns the junk value `0`; every statement of this mission therefore assumes `0 < q`. -/
noncomputable def OPT {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ} (I : Instance V r q) : ℝ :=
  ⨆ σ : V → Fin q, I.value σ

end VertexSampleCSP


