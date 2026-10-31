-- Prove2me | Definitions.Def_SeqExpDiffusion_NonDominated
-- name    : SeqExpDiffusion_NonDominated
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:38.851277+00:00
-- url     : https://prove2.me/theorems/e5a488a0-d7f0-418d-a7cd-154b1b8def32
-- title:
--   No action is uniformly dominated
-- statement:
--   Let $\mathscr A$ be a finite action set with expected rewards $\tilde R_a$. The rewards are **non-dominated** if every action is optimal at some interior belief: for every $a\in\mathscr A$ there is $\delta\in(0,1)$ with
--
--   $$\tilde R_a(\delta)\ \ge\ \tilde R_b(\delta)\qquad\text{for all } b\in\mathscr A.$$
--
--   The paper assumes this throughout, since a dominated action can be removed from $\mathscr A$ without loss of optimality. For two actions with different slopes it guarantees that their rewards cross at a belief $\hat\delta\in(0,1)$.
-- source:
--   Araman & Caldentey, Diffusion Approximations for a Class of Sequential Testing Problems, arXiv:2102.07030v3, §3, p.8

import Mathlib
import Definitions.Def_SeqExpDiffusion_reward

namespace SeqExpDiffusion

/-- No action is uniformly dominated: every action `a` is optimal at some belief `δ ∈ (0, 1)`,
Araman & Caldentey, *Diffusion Approximations for a Class of Sequential Testing Problems*, arXiv:2102.07030v3, p.8: "for every `a ∈ 𝒜`, there exists a `δ ∈ (0, 1)` such that `a ∈ 𝒜*(δ)`". -/
def NonDominated {ι : Type*} (α β : ι → ℝ) : Prop :=
  ∀ a, ∃ δ ∈ Set.Ioo (0 : ℝ) 1, ∀ b, reward α β b δ ≤ reward α β a δ

end SeqExpDiffusion


