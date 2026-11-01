-- Prove2me | Definitions.Def_AndOrSched_Instance
-- name    : AndOrSched_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:26:06.55862+00:00
-- url     : https://prove2.me/theorems/5a7f2709-f4f3-4f5e-8f75-d71e6b978c9a
-- title:
--   Instances of $1\,|\,\text{ao-prec}=A\dot\vee B\,|\,\sum w_jC_j$
-- statement:
--   An **instance** consists of finite disjoint job sets $A$ and $B$, with job set $N=A\,\dot\cup\,B$, processing times $p_j\ge0$ and weights $w_j\ge0$ for $j\in N$, AND-precedence arcs $E_\wedge\subseteq(A\times A)\cup(B\times B)$ and OR-precedence arcs $E_\vee\subseteq A\times B$. An AND-arc $(i,j)$ means that $j$ may start only after $i$ completes; a job $b\in B$ with OR-predecessors may start only after at least one of them completes.
--
--   The problem contains min-sum set cover ($p_a=1$, $w_a=0$ on $A$; $p_b=0$, $w_b=1$ on $B$) and many of its generalizations.
--
--   **Formalization Note** $A$ and $B$ are finite types and the jobs are $A\oplus B$. Processing times are nonnegative rationals (part 1 of Theorem 1 restricts them to $\{0,1\}$), weights nonnegative reals. Acyclicity of $E_\wedge$ is the separate predicate `Acyclic`.
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §1, pp.1–2, "Let N = A ∪̇ B be the set of n jobs"

import Mathlib
open scoped NNReal

namespace AndOrSched

/-- An instance of `1 | ao-prec = A ∨̇ B | Σ wⱼCⱼ` (Happach, Schulz, arXiv:2001.07011v1, §1, pp.1–2): the job set
`N = A ∪̇ B`, processing times `pⱼ ≥ 0`, weights `wⱼ ≥ 0`, AND-arcs `E∧ ⊆ (A × A) ∪ (B × B)`
(`andA` inside `A`, `andB` inside `B`) and OR-arcs `E∨ ⊆ A × B` (`orArc a b` means `(a, b) ∈ E∨`).

**Formalization Note** `A` and `B` are finite types and the job set is their sum `A ⊕ B`
(`Instance.N`). Processing times are nonnegative rationals `ℚ≥0` (the input of an algorithm;
part 1 of Theorem 1 restricts them to `{0, 1}`), weights are nonnegative reals `ℝ≥0`. The arcs
are arbitrary relations; acyclicity of `E∧` is the separate predicate `Acyclic`. -/
structure Instance where
  /-- the jobs of `A` -/
  A : Type
  /-- the jobs of `B` -/
  B : Type
  [fintypeA : Fintype A]
  [fintypeB : Fintype B]
  /-- processing times `pⱼ ≥ 0` -/
  p : A ⊕ B → ℚ≥0
  /-- weights `wⱼ ≥ 0` -/
  w : A ⊕ B → ℝ≥0
  /-- AND-arcs inside `A` -/
  andA : A → A → Prop
  /-- AND-arcs inside `B` -/
  andB : B → B → Prop
  /-- OR-arcs `E∨ ⊆ A × B` -/
  orArc : A → B → Prop

attribute [instance] Instance.fintypeA Instance.fintypeB

/-- The job set `N = A ∪̇ B` of an instance. -/
abbrev Instance.N (I : Instance) : Type := I.A ⊕ I.B

end AndOrSched


