-- Prove2me | Definitions.Def_RandomStreamCI_CodeIntersection_Separation
-- name    : RandomStreamCI_CodeIntersection_Separation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:30:43.687787+00:00
-- url     : https://prove2.me/theorems/e74e2809-47e1-48fa-9dbb-e0cba4010edd
-- title:
--   Full classical and quantum space-separation predicates
-- statement:
--   For a specified code family, classical hardness means one set of positive constants $c_1,c_2,a$ and a threshold $N$ works for every $n\ge N$, memory allowance $S\le2^{c_1n^{c_2}}$, and independent randomized classical program, with success at most $2^{-an}$. Quantum easiness means one family of legal programs, a polynomial memory bound and a nonnegative sequence $\varepsilon_n\to0$ satisfy
--
--   $$\forall n\ge N\ \forall\pi,\quad\Pr[\text{quantum success}\mid\pi]\ge1-\varepsilon_n.$$
--
--   These predicates abbreviate complete operational conclusions. Their definitions assert neither predicate of any family; their existence and validity remain theorems.
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Theorem 18, p. 16; Theorem 28, p. 28; Theorem 1, p. 2

import Definitions.Def_RandomStreamCI_CodeIntersection_Codes
import Definitions.Def_RandomStreamCI_CodeIntersection_Branching
import Definitions.Def_RandomStreamCI_CodeIntersection_Quantum

noncomputable section

namespace RandomStreamCI.CodeIntersection

open scoped BigOperators

/-- Full Theorem 18, including independent mixtures of deterministic machines.
Uniform constants precede blocklength, space budget, coin law and machine. -/
def ClassicalHard (F : CodeFamily) : Prop :=
  ∃ c₁ c₂ a : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < a ∧ ∃ N : ℕ, ∀ n ≥ N,
    ∀ S : ℕ, (S : ℝ) ≤ (2 : ℝ)^(c₁ * (n : ℝ)^c₂) →
    ∀ {Ω : Type} [Fintype Ω] (p : PMF Ω)
      (B : Ω → BranchingProgram n (F n).Alphabet (2 ^ S)),
      BranchingProgram.randomizedSuccess p B (F n).code ≤ (2 : ℝ)^(-a * n)

/-- Full Theorem 28. The family and vanishing error are chosen BEFORE all
stream orderings. There is no post-pass oracle input to any operation. -/
def QuantumEasy (F : CodeFamily) : Prop :=
  ∃ (Q : (n : ℕ) → QuantumProgram n (F n).Alphabet) (ε : ℕ → ℝ)
      (K : ℝ) (d : ℕ),
    (∀ n, 0 ≤ ε n) ∧ Filter.Tendsto ε Filter.atTop (nhds 0) ∧ 0 < K ∧
    ∃ N : ℕ, ∀ n ≥ N,
      ((Q n).memoryBits : ℝ) ≤ K * (n : ℝ)^d ∧
      ∀ π : Order n (F n).Alphabet,
        1 - ε n ≤ (Q n).successAtOrder (F n).code π

end RandomStreamCI.CodeIntersection


