-- Prove2me | Definitions.Def_MeanBudgetXC_Supplement_IsSparseFamily
-- name    : MeanBudgetXC_Supplement_IsSparseFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:11:28.234507+00:00
-- url     : https://prove2.me/theorems/8933b68a-6646-40c2-8ab5-939048e812b1
-- title:
--   The nonempty sparse-support family of Theorem 7.2
-- statement:
--   Fix $\theta$ and constants $D,E$. A graph $F$ on $[N]$ belongs to the **sparse-support family** if
--   1. $F$ has at least one edge;
--   2. $F$ is triangle-free;
--   3. $\Delta(F)\le D$;
--   4. $|E(F)|\le E\cdot N$;
--   5. $\Delta(F)\le d-1$ for the density $d=\lfloor\theta N\rfloor$.
--
--   These are the binary-cap instances of Theorem 7.2.
--
--   **Formalization Note** Condition 5 is written $\Delta(F)+1\le d$, the same condition for a graph with an edge. It is the reduction's family in the proof idea ("constructs a nonempty triangle-free support $F$ at density $d=\lfloor\theta N\rfloor$, with $\Delta(F)\le d-1$", p.36), and identity (60) of Appendix F.2 requires it; the theorem's sentence names only triangle-freeness, maximum degree $D_\theta$ and $O_\theta(N)$ edges.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c712270634eb9c25e965df506f4fd2cfa5c228f4bb13f3ca9ddc9859e76), Section 7.2, p.36 and its proof idea; Appendix F.2, pp.49–50

import Mathlib

namespace MeanBudgetXC.Supplement

/-- The **sparse-support family** of Theorem 7.2 (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 7.2, p.36, and its
proof idea, p.36; Appendix F.2, pp.49–50): a graph `F` on `[N]` that is nonempty (has an
edge), triangle-free, of maximum degree at most `D`, with at most `E·N` edges, and with maximum
degree at most `d − 1` for the density `d = ⌊θN⌋` ("constructs a nonempty triangle-free support
F at density d = ⌊θN⌋, with ∆(F) ≤ d − 1").

**Formalization Note** `Δ(F) ≤ d − 1` is written `Δ(F) + 1 ≤ d`, which is the same condition for a
nonempty graph. The condition comes from the proof idea and Appendix F.2, where identity (60)
requires it; the theorem's sentence names only triangle-freeness, degree `D_θ` and `O_θ(N)`
edges. -/
def IsSparseFamily (θ : ℝ) (D E : ℕ) {N : ℕ} (F : SimpleGraph (Fin N)) [DecidableRel F.Adj] :
    Prop :=
  F.edgeFinset.Nonempty ∧ F.CliqueFree 3 ∧ F.maxDegree ≤ D ∧ F.edgeFinset.card ≤ E * N ∧
    F.maxDegree + 1 ≤ ⌊θ * N⌋₊

end MeanBudgetXC.Supplement


