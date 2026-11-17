-- Prove2me | Definitions.Def_ReplicableOL_Supplement_IsThm3Chain
-- name    : ReplicableOL_Supplement_IsThm3Chain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:22:02.407696+00:00
-- url     : https://prove2.me/theorems/d0d02bdf-9af4-41f9-858d-b0ca8abe81e0
-- title:
--   The chain of Theorem 3
-- statement:
--   A DALR chain $(A_0,\dots,A_K)$ is **Theorem 3's chain** for $\rho$ and $T$ if it follows the recursion $A_0=T$, $A_i=2^{\lceil\log_2(\sqrt{A_{i-1}}/\kappa)\rceil}$ and stops at the first $K$ with $A_K\le 8/\kappa^2$, that is,
--
--   $$
--   A_K\le \frac{8}{\kappa^2}\quad\text{and}\quad A_i>\frac{8}{\kappa^2}\ \text{ for all } i<K .
--   $$
--
--   These conditions determine $K$ and $A_0,\dots,A_K$, which is all DALR reads.
--
--   **Formalization Note** That such a chain exists (the recursion produces strictly decreasing powers of $2$, each dividing the previous, and stops) is a conclusion of the theorems that use this predicate, not a hypothesis.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Theorem 3 (with parameters), p.20

import Mathlib
import Definitions.Def_ReplicableOL_Supplement_Chain
import Definitions.Def_ReplicableOL_Supplement_thm3A

namespace ReplicableOL.Supplement

/-- **The chain of Theorem 3.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Theorem 3 (with parameters), p.20. The DALR chain `A_0 = T, A_i = 2^{⌈log₂(√A_{i−1}/κ)⌉}`, "stopping at the first K with A_K ≤ 8/κ²".

**Formalization Note.** `C` agrees with the recursion `thm3A` on `0, …, K`, and `K` is the first index with `A_K ≤ 8/κ²`. This determines `C.K` and `C.A` on `0, …, K`, which is all DALR reads, so at most one DALR is described. That such a `C` exists (the recursion gives a valid chain: strictly decreasing powers of 2, each dividing the previous) is part of the theorems' conclusions, not a hypothesis. -/
def IsThm3Chain (ρ : ℝ) {T : ℕ} (C : Chain T) : Prop :=
  (∀ i ≤ C.K, C.A i = thm3A ρ T i) ∧
    (C.A C.K : ℝ) ≤ 8 / thm3kappa ρ T ^ 2 ∧
    ∀ i < C.K, 8 / thm3kappa ρ T ^ 2 < (C.A i : ℝ)

end ReplicableOL.Supplement


