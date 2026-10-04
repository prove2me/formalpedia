-- Prove2me | Definitions.Def_MulticutLShaped_SimpleRecourse_Algorithm
-- name    : MulticutLShaped_SimpleRecourse_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:03:05.519962+00:00
-- url     : https://prove2.me/theorems/429b256c-1eab-4501-acfe-869701eb2398
-- title:
--   The multicut algorithm for simple recourse problems (Section 5, Steps 0-2, Eqs. (26)-(27))
-- statement:
--   This file formalizes the **multicut algorithm for simple recourse problems** of Birge and Louveaux (1988), p. 389, on the model of the simple recourse problem (3), (19)–(20).
--
--   The algorithm keeps the set $I\subseteq\{1,\dots,m_2\}\times\{1,\dots,J\}$ of pairs $l=(i,j)$ identified so far; for each such pair it carries a variable $u_l$ and the cut data
--   $$
--   E_l=p_{ij}q_{ij}T_i,\qquad e_l=p_{ij}q_{ij}h_{ij}.
--   $$
--
--   1. *Step 0.* Set $\nu=t=0$ (no pair identified, $I=\emptyset$).
--   2. *Step 1.* Set $\nu=\nu+1$ and solve the master program (26)
--   $$
--   \min\ cx+\sum_{i=1}^{m_2}\sum_{j=1}^J p_{ij}q^-_{ij}(T_ix)+\sum_{l\in I}u_l\quad\text{s.t. } Ax=b,\ x\ge0,\ u_l\ge e_l-E_lx,\ u_l\ge 0\ (l\in I),
--   $$
--   with an optimal solution $(x^\nu,u^\nu)$ (if $I=\emptyset$, $u$ is ignored).
--   3. *Step 2.* For each pair $(i,j)\notin I$ for which the constraint
--   $$
--   0\ge p_{ij}q_{ij}(h_{ij}-T_ix^\nu)\qquad(27)
--   $$
--   is violated, add $(i,j)$ to $I$. If some pair was added, return to Step 1; otherwise stop.
--
--   The file defines the master's feasible set, objective and optimal solutions; the set of unidentified pairs violating (27) at $x$; one pass $I\to I'$ (some optimal solution of (26) violates (27) for at least one unidentified pair, and $I'$ is $I$ together with all of them); the stopping condition at $x$ (some $(x,u)$ is optimal for (26) and no unidentified pair violates (27)); and the reachability relation $\mathrm{Reach}(\nu,I)$: in some run, the $\nu$-th solve of Step 1 takes place with identified pairs $I$, starting from $\mathrm{Reach}(1,\emptyset)$.
--
--   **Formalization Note.** The paper's Step 2 reads "for each $i$ and $j$"; we range over the pairs not yet identified, as the text's explanation says (27) "identifies any constraints in (25) that are not met" — an identified constraint already sits in (26) through $u_l$. The paper's stopping rule is implicit: the algorithm stops when (27) is violated for no pair. The objective of (26) omits the constant $-\sum_{i,j}p_{ij}q^-_{ij}h_{ij}$ of (25), as printed; it does not change the minimizers. The constraint $x\ge0$ of (3), omitted in the display of (26), is kept. Every optimal solution of (26) may be the one the algorithm uses. The order in which pairs are identified, and so the index $t$, is immaterial, so the state is the set $I$ rather than the list $(E_l,e_l)_{l\le t}$. Values of $u$ at pairs outside $I$ are unconstrained and do not enter (26).
-- source:
--   Birge and Louveaux, A multicut algorithm for two-stage stochastic linear programs, Eur. J. Oper. Res. 34 (1988), p. 389, Section 5, Multicut algorithm for simple recourse problems, Eqs. (26), (27)

import Mathlib
import Definitions.Def_MulticutLShaped_SimpleRecourse_Model

namespace MulticutLShaped.SimpleRecourse

variable {n1 m1 m2 J : ℕ}

/-- The cut row `E_l = p_ij q_ij T_i` of Step 2 (p. 389), for the pair `l = (i, j)`;
`T_i` is row `i` of `T`. -/
def cutE (inst : Instance n1 m1 m2 J) (l : Fin m2 × Fin J) : Fin n1 → ℝ :=
  (inst.p l.1 l.2 * inst.q l.1 l.2) • inst.T l.1

/-- The cut right-hand side `e_l = p_ij q_ij h_ij` of Step 2 (p. 389), for `l = (i, j)`. -/
def cute (inst : Instance n1 m1 m2 J) (l : Fin m2 × Fin J) : ℝ :=
  inst.p l.1 l.2 * inst.q l.1 l.2 * inst.h l.1 l.2

/-- Feasibility for the master LP (26) when the set of pairs identified so far in Step 2 is `I`:
`Ax = b`, `x ≥ 0` (from (3); omitted in the display of (26)), and `u_l ≥ e_l − E_l x`, `u_l ≥ 0`
for every `l ∈ I`. The values of `u` outside `I` are not constrained and do not enter (26). -/
def MasterFeasible (inst : Instance n1 m1 m2 J) (I : Finset (Fin m2 × Fin J))
    (x : Fin n1 → ℝ) (u : Fin m2 × Fin J → ℝ) : Prop :=
  inst.A.mulVec x = inst.b ∧ (∀ k, 0 ≤ x k) ∧
    ∀ l ∈ I, cute inst l - cutE inst l ⬝ᵥ x ≤ u l ∧ 0 ≤ u l

/-- The objective of the master LP (26): `cx + Σ_i Σ_j p_ij q⁻_ij (T_i x) + Σ_{l ∈ I} u_l`. -/
def masterObj (inst : Instance n1 m1 m2 J) (I : Finset (Fin m2 × Fin J))
    (x : Fin n1 → ℝ) (u : Fin m2 × Fin J → ℝ) : ℝ :=
  inst.c ⬝ᵥ x + ∑ i, ∑ j, inst.p i j * inst.qminus i j * (inst.T i ⬝ᵥ x) + ∑ l ∈ I, u l

/-- `(x, u)` is an optimal solution of the master LP (26) with identified pairs `I` (Step 1). -/
def MasterOptimal (inst : Instance n1 m1 m2 J) (I : Finset (Fin m2 × Fin J))
    (x : Fin n1 → ℝ) (u : Fin m2 × Fin J → ℝ) : Prop :=
  MasterFeasible inst I x u ∧
    ∀ x' u', MasterFeasible inst I x' u' → masterObj inst I x u ≤ masterObj inst I x' u'

open Classical in
/-- The pairs `(i, j)` not yet identified (`∉ I`) for which the constraint (27),
`0 ≥ p_ij q_ij (h_ij − T_i x)`, is violated at `x` (Step 2, p. 389). -/
noncomputable def violated (inst : Instance n1 m1 m2 J) (I : Finset (Fin m2 × Fin J))
    (x : Fin n1 → ℝ) : Finset (Fin m2 × Fin J) :=
  Finset.univ.filter fun l =>
    l ∉ I ∧ 0 < inst.p l.1 l.2 * inst.q l.1 l.2 * (inst.h l.1 l.2 - inst.T l.1 ⬝ᵥ x)

/-- One pass Step 1 → Step 2 → Step 1 of the multicut algorithm for simple recourse problems:
some optimal solution `(x, u)` of (26) with identified pairs `I` violates (27) for at least one
unidentified pair, and every such pair is added: `I' = I ∪ violated I x`. -/
def Step (inst : Instance n1 m1 m2 J) (I I' : Finset (Fin m2 × Fin J)) : Prop :=
  ∃ x u, MasterOptimal inst I x u ∧ (violated inst I x).Nonempty ∧ I' = I ∪ violated inst I x

/-- The algorithm stops at `x` with identified pairs `I`: `(x, u)` is optimal for (26) for some
`u`, and (27) is violated for no unidentified pair. -/
def StopsAt (inst : Instance n1 m1 m2 J) (I : Finset (Fin m2 × Fin J)) (x : Fin n1 → ℝ) : Prop :=
  ∃ u, MasterOptimal inst I x u ∧ violated inst I x = ∅

/-- `Reach inst ν I`: in some run of the algorithm, the `ν`-th solve of Step 1 (iteration `ν`)
takes place with identified pairs `I`. Step 0 sets `ν = t = 0`, so the first solve is `ν = 1`
with no cuts (`I = ∅`). -/
inductive Reach (inst : Instance n1 m1 m2 J) : ℕ → Finset (Fin m2 × Fin J) → Prop
  | start : Reach inst 1 ∅
  | step {ν : ℕ} {I I' : Finset (Fin m2 × Fin J)} :
      Reach inst ν I → Step inst I I' → Reach inst (ν + 1) I'

end MulticutLShaped.SimpleRecourse


