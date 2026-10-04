-- Prove2me | Definitions.Def_OnlineRandomization_Simulation_Game
-- name    : OnlineRandomization_Simulation_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T06:38:40.754704+00:00
-- url     : https://prove2.me/theorems/e7d2d735-f715-4cc3-a075-9e2c2e45ea77
-- title:
--   Request-answer game, optimum, and affine cost transformations
-- statement:
--   A **request-answer game** has a request set $R$, a finite nonempty answer set $A$, and a cost $f_n(r,a)$ for each equally long pair of request and answer strings. The off-line optimum for a request string $r$ is
--
--   $$c(r)=\min_{a\in A^{|r|}} f_{|r|}(r,a).$$
--
--   A cost transformation is called linear in the paper when it has the affine form $\alpha(x)=cx+d$. This game interface can be reused for other online problems.
--
--   **Formalization Note** Costs are real rather than the paper's $\mathbb R\cup\{\infty\}$ (P1). Nonempty $A$ makes the minimum defined (P2). Requests and answers are oldest-first lists; cost values for unequal-length lists are unused (P5).
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript pp. 7–8, §2

import Mathlib

namespace OnlineRandomization.Simulation

/-- A real-valued request-answer game. For equal-length lists, `cost r a` is the
paper's `f_n(r,a)`; unequal-length values are unused. -/
structure Game (R A : Type*) where
  cost : List R → List A → ℝ

/-- The best answer string to a fixed request string. -/
noncomputable def Game.opt {R A : Type*} [Fintype A] [Nonempty A]
    (F : Game R A) (r : List R) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun a : Fin r.length → A => F.cost r (List.ofFn a))

/-- The paper calls affine cost transformations "linear". -/
def IsLinear (α : ℝ → ℝ) : Prop :=
  ∃ c d : ℝ, ∀ x : ℝ, α x = c * x + d

end OnlineRandomization.Simulation


