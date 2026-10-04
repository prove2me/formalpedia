-- Prove2me | Definitions.Def_OnlineRandomization_Restart_Model
-- name    : OnlineRandomization_Restart_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T07:53:35.728985+00:00
-- url     : https://prove2.me/theorems/95a177f4-4d50-4a90-9a5b-8443e947826a
-- title:
--   Request-answer games, deterministic online algorithms and α-competitiveness
-- statement:
--   A **request-answer game** consists of a request set $R$, a finite nonempty answer set $A$, and cost functions $f_n : R^n \times A^n \to \mathbb{R}$ for $n = 0, 1, 2, \dots$; we write $f$ for their union and $f_0$ for the cost of the empty play. For a request sequence $r = (r_1,\dots,r_n)$ the **off-line optimum** is
--
--   $$c(r) = \min\{ f_n(r, a) : a \in A^n \}.$$
--
--   A **deterministic online algorithm** $G$ is a sequence of functions $g_i : R^i \to A$, $i \ge 1$. On $r$ it answers $G(r) = (a_1,\dots,a_n)$ with $a_i = g_i(r_1,\dots,r_i)$, and its cost is $c_G(r) = f_n(r, G(r))$. For $\alpha : \mathbb{R} \to \mathbb{R}$, $G$ is **$\alpha$-competitive** if
--
--   $$c_G(r) \le \alpha(c(r)) \quad \text{for every request sequence } r.$$
--
--   For a deterministic algorithm this is the same as $\alpha$-competitiveness against every adaptive off-line adversary, since the adversary can foresee the algorithm's moves. These are the objects in terms of which the restart construction of §4 and Theorem 4.1 are stated.
--
--   **Formalization Note** Requests and answers are Lean lists, oldest first, and $f_n(r,a)$ is `F.cost r a` with `r.length = a.length = n`; values on lists of different lengths are never used. Costs are real (the paper allows $+\infty$; real costs are a special case, and a finite diameter forces finite costs anyway). The answer set is a `Fintype` and `Nonempty`, so $c(r)$ is a minimum over a nonempty finite set. A deterministic algorithm is a single function on request lists, whose value on $(r_1,\dots,r_i)$ is $g_i$; its value on the empty list is never used. Only the deterministic part of the model of §2 is needed in this mission.
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 7, §2

import Mathlib

namespace OnlineRandomization.Restart

/-- p. 7: a request-answer game with real costs. For `r.length = a.length = n`,
`cost r a` is the paper's `f_n(r, a)`; `cost [] []` is `f_0`. Values on lists of
different lengths are never used. -/
structure Game (R A : Type*) where
  cost : List R → List A → ℝ

/-- p. 7: the off-line optimum `c(r) = min { f_n(r, a) | a ∈ A^n }`, a minimum over the
finite nonempty set `A^n`. -/
noncomputable def Game.opt {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A)
    (r : List R) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun a : Fin r.length → A => F.cost r (List.ofFn a))

/-- p. 7: a deterministic online algorithm `(g_i)_{i ≥ 1}`, `g_i : R^i → A`, as one function
on request lists: `G (r_1, …, r_i) = g_i(r_1, …, r_i)`. Only its values on nonempty lists
are used. -/
abbrev DetAlg (R A : Type*) := List R → A

/-- p. 7: `G(r) = (a_1, …, a_n)` with `a_i = g_i(r_1, …, r_i)`. -/
def DetAlg.answers {R A : Type*} (G : DetAlg R A) (r : List R) : List A :=
  (List.range r.length).map fun i => G (r.take (i + 1))

/-- p. 7: the cost of `G` on `r`, `c_G(r) = f_n(r, G(r))`. -/
def DetAlg.costOn {R A : Type*} (F : Game R A) (G : DetAlg R A) (r : List R) : ℝ :=
  F.cost r (G.answers r)

/-- p. 7: a deterministic algorithm is `α`-competitive if `c_G(r) ≤ α(c(r))` for every
request sequence `r`. -/
def IsCompetitive {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (α : ℝ → ℝ)
    (G : DetAlg R A) : Prop :=
  ∀ r : List R, G.costOn F r ≤ α (F.opt r)

end OnlineRandomization.Restart


