-- Prove2me | Definitions.Def_AndOrSched_normalize
-- name    : AndOrSched_normalize
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:29:50.641013+00:00
-- url     : https://prove2.me/theorems/e8363852-3d3a-4951-8f1e-d311f48d4a7a
-- title:
--   The normalized instance $I'$
-- statement:
--   The instance $I'$ on which Algorithms 1 and 2 run, obtained from $I$ by the paper's w.l.o.g. steps:
--   1. the jobs of $Z$ are removed (they complete at time $0$);
--   2. redundant OR-arcs are removed, and every $b$ with an OR-predecessor in $Z$ loses its OR-constraint;
--   3. every remaining $a\in A$ receives a dummy successor $\hat a\in B$ with $p_{\hat a}=0$, $\mathcal P(\hat a)=\{a\}$ and $w_{\hat a}=w_a$, and $w_a$ is set to $0$ ("we can shift a positive weight of a job in $A$ to an additional successor in $B$ with zero processing time");
--   4. all processing times are multiplied by $D$.
--
--   The jobs of $I'$ are $A'=A\setminus Z$ and $B'=(B\setminus Z)\,\dot\cup\,\{\hat a: a\in A'\}$.
--
--   **Formalization Note** A dummy is added for every remaining $a$, also when $w_a=0$; it then has weight $0$ and changes no cost.
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §1, p.4 and §2, p.6, "W.l.o.g., we may assume that wa = 0 for all a ∈ A. Otherwise, we can shift a positive weight …"

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_orPred
import Definitions.Def_AndOrSched_nonRedPred
import Definitions.Def_AndOrSched_zeroSet
import Definitions.Def_AndOrSched_scaleD
open scoped Classical NNReal

namespace AndOrSched

/-- The normalized instance `I'` of `I` (Happach, Schulz, arXiv:2001.07011v1, §1, p.4 and §2, p.6), on which Algorithms 1 and 2
run:
1. the jobs of `Z = zeroSet I` are removed ("such a job can be disregarded"); they complete at
   time `0`;
2. redundant OR-arcs are removed, and a job `b` with an OR-predecessor in `Z` loses its
   OR-constraint (it is met at time `0`);
3. "we can shift a positive weight of a job in A to an additional successor in B with zero
   processing time": every remaining `a ∈ A` gets a dummy job `â ∈ B` with `p_â = 0`,
   `𝒫(â) = {a}` and `w_â = w_a`, and `w_a` becomes `0`;
4. "all data is integer": every processing time is multiplied by `D = scaleD I`.

The jobs of `I'` are `A' = A ∖ Z` and `B' = (B ∖ Z) ⊕ A'`, where the second summand holds the
dummies. AND-arcs are those of `I` between remaining jobs.

**Formalization Note** A dummy is added for every remaining `a ∈ A`, also when `w_a = 0`; such a
dummy has weight `0` and does not change any schedule's cost. The processing time `⌊pⱼ · D⌋₊` equals
`pⱼ · D`, since `D` is a common multiple of the denominators. -/
noncomputable def normalize (I : Instance) : Instance where
  A := {a : I.A // Sum.inl a ∉ zeroSet I}
  B := {b : I.B // Sum.inr b ∉ zeroSet I} ⊕ {a : I.A // Sum.inl a ∉ zeroSet I}
  fintypeA := Fintype.ofFinite _
  fintypeB := Fintype.ofFinite _
  p := fun j => match j with
    | Sum.inl a => (Nat.floor (I.p (Sum.inl a.1) * (scaleD I : ℚ≥0)) : ℚ≥0)
    | Sum.inr (Sum.inl b) => (Nat.floor (I.p (Sum.inr b.1) * (scaleD I : ℚ≥0)) : ℚ≥0)
    | Sum.inr (Sum.inr _) => 0
  w := fun j => match j with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl b) => I.w (Sum.inr b.1)
    | Sum.inr (Sum.inr a) => I.w (Sum.inl a.1)
  andA := fun a a' => I.andA a.1 a'.1
  andB := fun b b' => match b, b' with
    | Sum.inl b, Sum.inl b' => I.andB b.1 b'.1
    | _, _ => False
  orArc := fun a b => match b with
    | Sum.inl b => a.1 ∈ nonRedPred I b.1 ∧ ¬ ∃ a' ∈ orPred I b.1, Sum.inl a' ∈ zeroSet I
    | Sum.inr a₀ => a = a₀

end AndOrSched


