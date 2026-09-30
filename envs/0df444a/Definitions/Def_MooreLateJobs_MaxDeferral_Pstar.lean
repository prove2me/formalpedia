-- Prove2me | Definitions.Def_MooreLateJobs_MaxDeferral_Pstar
-- name    : MooreLateJobs_MaxDeferral_Pstar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:33:17.184284+00:00
-- url     : https://prove2.me/theorems/9980db97-c53e-48e0-8516-fa160327dad9
-- title:
--   The generalized inverse $P_i^*$ of a deferral cost
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ be a deferral cost: $f(s)$ is the cost of completing a job at time $s$. Times are measured from $0$, so all times below range over $s\ge 0$. For a cost level $y\in\mathbb R$ define $P^*(y)\in\mathbb R\cup\{+\infty\}$ by cases (Moore 1968, p. 108, Definition):
--
--   1. if $f^{-1}(y)$ exists, $P^*(y)=f^{-1}(y)$;
--   2. otherwise
--      - (a) $P^*(y)=\max\{s\ge0 \mid f(s)=y\}$ if some $s\ge 0$ has $f(s)=y$;
--      - (b) $P^*(y)=0$ if $f(s)>y$ for all $s\ge 0$;
--      - (c) $P^*(y)=+\infty$ if $f(s)<y$ for all $s\ge 0$.
--
--   In short,
--   $$
--   P^*(y)=\begin{cases}\max\{s\ge 0: f(s)=y\} & \text{if } f(s)=y \text{ for some } s\ge 0,\\ 0 & \text{if } f(s)>y \text{ for all } s\ge 0,\\ +\infty & \text{otherwise.}\end{cases}
--   $$
--
--   $P^*(y)$ is the latest time at which the job can be completed at cost at most $y$; it serves as the job's "due-date" at cost level $y$.
--
--   **Formalization Note** Case 1 is subsumed by case 2(a): when the inverse exists the level set is the singleton $\{f^{-1}(y)\}$, whose maximum is $f^{-1}(y)$; the file proves this as the structural lemma `Pstar_of_level_singleton`. Two conventions are fixed where the page is silent: (i) all times range over $s\ge0$ (with times over all of $\mathbb R$ the paper's later claim that $P^*$ is non-decreasing fails); (ii) if the level set $\{s\ge0: f(s)=y\}$ is unbounded above (the cost stays at $y$ forever), its "max" does not exist and $P^*(y)=+\infty$, since every completion time then costs at most $y$. The last case is stated as "otherwise"; for a continuous non-decreasing $f$ it coincides with the paper's case (c), $f(s)<y$ for all $s\ge0$, by the intermediate value theorem. Values are in `EReal`.
-- source:
--   Moore, An n Job, One Machine Sequencing Algorithm for Minimizing the Number of Late Jobs, Management Science 15(1), 1968, p. 108, "Minimizing the Maximum Deferral Cost", Definition of P_i* (cases 1, 2a, 2b, 2c)

import Mathlib

namespace MooreLateJobs.MaxDeferral

open Classical in
/-- The function `P*` attached to a deferral cost `f` (Moore 1968, p. 108, Definition), with all
times ranging over `s ≥ 0` (completion times are measured from `t = 0`, p. 102):

* case 2a: if some `s ≥ 0` has `f s = y`, then `P*(y) = max {s ≥ 0 | f s = y}`; when this level
  set is unbounded above (the page is silent; "max" does not exist) the value is `+∞`;
* case 2b: if `f s > y` for every `s ≥ 0`, then `P*(y) = 0`;
* case 2c: otherwise `P*(y) = +∞` (for continuous monotone `f` this is exactly the case
  `f s < y` for every `s ≥ 0`).

Case 1 of the page (`P*(y) = f⁻¹(y)` when the inverse exists) is subsumed by case 2a: then the
level set is the singleton `{f⁻¹(y)}`, whose maximum is `f⁻¹(y)` (see `Pstar_of_level_singleton`).
Values live in `EReal` because case 2c gives `+∞`. -/
noncomputable def Pstar (f : ℝ → ℝ) (y : ℝ) : EReal :=
  if ∃ s, 0 ≤ s ∧ f s = y then
    (if BddAbove {s | 0 ≤ s ∧ f s = y} then ((sSup {s | 0 ≤ s ∧ f s = y} : ℝ) : EReal) else ⊤)
  else if ∀ s, 0 ≤ s → y < f s then 0
  else ⊤

/-- Case 1 of the definition (p. 108): if `s₀` is the unique time `s ≥ 0` with `f s = y`
(the inverse `f⁻¹(y)` exists), then `P*(y) = s₀`. -/
theorem Pstar_of_level_singleton (f : ℝ → ℝ) (y s₀ : ℝ)
    (h : {s | 0 ≤ s ∧ f s = y} = {s₀}) : Pstar f y = (s₀ : EReal) := by
  have hmem : s₀ ∈ {s | 0 ≤ s ∧ f s = y} := by rw [h]; rfl
  have hex : ∃ s, 0 ≤ s ∧ f s = y := ⟨s₀, hmem⟩
  have hb : BddAbove {s | 0 ≤ s ∧ f s = y} := by rw [h]; exact bddAbove_singleton
  unfold Pstar
  rw [if_pos hex, if_pos hb, h, csSup_singleton]

end MooreLateJobs.MaxDeferral


