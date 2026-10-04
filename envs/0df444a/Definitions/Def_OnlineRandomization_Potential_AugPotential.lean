-- Prove2me | Definitions.Def_OnlineRandomization_Potential_AugPotential
-- name    : OnlineRandomization_Potential_AugPotential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T08:06:04.616979+00:00
-- url     : https://prove2.me/theorems/fd413180-9907-4785-9a39-c64e16652986
-- title:
--   Definition 3.1 — augmented potential functions; the potential rule of Theorem 3.1
-- statement:
--   Let $G$ be a randomized online algorithm given by its next-answer distributions $g_{n+1}(r r_{n+1}, a)$ on $A$, let $f_n$ be the cost functions of the game and let $\alpha : \mathbb R \to \mathbb R$. A configuration after $n$ steps is a triple $(r, a, b) \in R^n \times A^n \times A^n$: the requests so far, the algorithm's answers and an adversary's answers.
--
--   A family $\Phi = \{\Phi_n : R^n \times A^n \times A^n \to \mathbb R\}_{n \ge 0}$ is an **augmented potential function** for $\alpha$ and $G$ if
--
--   1. $\Phi_0 = 0$;
--   2. for every $n$ and every configuration $(r, a, b)$, $\;\Phi_n(r, a, b) \le \alpha(f_n(r, b)) - f_n(r, a)$;
--   3. for every $n$, every configuration $(r, a, b)$, every $r_{n+1} \in R$ and every $b_{n+1} \in A$,
--   $$
--   \mathbb E_{a_{n+1} \sim g_{n+1}(r r_{n+1}, a)}\big[\Phi_{n+1}(r r_{n+1}, a a_{n+1}, b b_{n+1})\big] \ge \Phi_n(r, a, b).
--   $$
--
--   In property 3 the expectation is over the algorithm's answer $a_{n+1}$ only; the request $r_{n+1}$ and the adversary's answer $b_{n+1}$ are arbitrary.
--
--   The same file defines the selection rule of Theorem 3.1. Let $H$ be a randomized online algorithm given as a distribution over deterministic algorithms $H_y$. A deterministic online algorithm $M = \{m_n\}$ **obeys the potential rule** for $\Phi$ and $H$ if for every $r \in R^n$ and every $r' = r t \in R^{n+1}$,
--   $$
--   \mathbb E_y\big[\Phi_{n+1}(r', M(r)\, m_{n+1}(r'), H_y(r'))\big] \ge \mathbb E_y\big[\Phi_n(r, M(r), H_y(r))\big].
--   $$
--
--   The augmented potential function is the paper's certificate of competitiveness against adaptive on-line adversaries (Lemma 3.1); the rule turns such a certificate into an explicit deterministic algorithm (Theorem 3.1).
--
--   **Formalization Note** $\Phi$ is one real function on triples of lists; $\Phi_n(r, a, b)$ is its value on lists of common length $n$, and properties 2 and 3 are required only for such triples. The expectation in property 3 is the finite sum $\sum_{a'} g_{n+1}(r r_{n+1}, a)(a')\,\Phi_{n+1}(\dots)$. The rule is a predicate on $M$, not a construction; $m_{n+1}(r')$ is `M (r ++ [t])`, and $M(r')$ is $M(r)$ followed by it. The expectations over $y$ are Bochner integrals under $H$'s probability measure.
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 14, Definition 3.1, and p. 15, Theorem 3.1 (the rule for m_{n+1})

import Mathlib
import Definitions.Def_OnlineRandomization_Potential_Behavioural

namespace OnlineRandomization.Potential

open MeasureTheory

/-- Manuscript p. 14, Definition 3.1: `Φ` is an augmented potential function for `α` and the
behavioural randomized algorithm `g`. `Φ r a b` is `Φ_n(r, a, b)` on lists of common length `n`
(requests, algorithm's answers, adversary's answers); other values are never used.
1. `Φ_0 = 0`;
2. `Φ_n(r, a, b) ≤ α(f_n(r, b)) − f_n(r, a)` for every configuration;
3. for every configuration, every `r_{n+1} = x ∈ R` and `b_{n+1} = b' ∈ A`,
   `E[Φ_{n+1}(r x, a a_{n+1}, b b')] ≥ Φ_n(r, a, b)` with `a_{n+1} ∼ g_{n+1}(r x, a)`. -/
structure IsAugPotential {R A : Type*} [Fintype A] (F : Game R A) (α : ℝ → ℝ)
    (g : BehAlg R A) (Φ : List R → List A → List A → ℝ) : Prop where
  zero : Φ [] [] [] = 0
  le_residue : ∀ (r : List R) (a b : List A), a.length = r.length → b.length = r.length →
    Φ r a b ≤ α (F.cost r b) - F.cost r a
  le_step : ∀ (r : List R) (a b : List A), a.length = r.length → b.length = r.length →
    ∀ (x : R) (b' : A),
      Φ r a b ≤ ∑ a' : A, (g (r ++ [x]) a a').toReal * Φ (r ++ [x]) (a ++ [a']) (b ++ [b'])

/-- Manuscript p. 15, Theorem 3.1: the deterministic algorithm `M = (m_n)` obeys the potential
rule for `Φ` and the randomized algorithm `H` (coins `y`) if, for every `r ∈ R^n` and every
`r' = r x`, its answer `m_{n+1}(r') = M (r ++ [x])` satisfies
`E_y[Φ_{n+1}(r', M(r) m_{n+1}(r'), H_y(r'))] ≥ E_y[Φ_n(r, M(r), H_y(r))]`. -/
def ObeysPotentialRule {R A Ω : Type*} [MeasurableSpace Ω]
    (Φ : List R → List A → List A → ℝ) (H : RandAlg R A Ω) (M : DetAlg R A) : Prop :=
  ∀ (r : List R) (x : R),
    (∫ y, Φ r (M.answers r) ((H.alg y).answers r) ∂H.μ) ≤
      ∫ y, Φ (r ++ [x]) (M.answers r ++ [M (r ++ [x])]) ((H.alg y).answers (r ++ [x])) ∂H.μ

end OnlineRandomization.Potential


