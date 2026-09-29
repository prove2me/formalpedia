-- Prove2me | Definitions.Def_FoundationsML_PAC_IsPACLearnable
-- name    : FoundationsML_PAC_IsPACLearnable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:07:49.348991+00:00
-- url     : https://prove2.me/theorems/e846b466-584e-42ea-86b4-0cf01b4165db
-- title:
--   PAC-learnability of a concept class (Definition 2.3)
-- statement:
--   **Definition 2.3 (PAC-learning), p. 11, PDF p. 28.** A concept class $C \subseteq (X \to
--   \mathrm{Bool})$ is PAC-learnable if there exist an algorithm $A$ and a polynomial function
--   $\mathrm{poly}(\cdot,\cdot,\cdot,\cdot)$ such that for any $\epsilon,\delta>0$, any
--   distribution $D$ on $X$, and any target concept $c\in C$, for any sample size $m \ge
--   \mathrm{poly}(1/\epsilon,1/\delta,n,\mathrm{size}(c))$,
--   $$\Pr_{S\sim D^m}[R(h_S)\le\epsilon] \ge 1-\delta,$$
--   where $h_S = A(S)$ is the hypothesis $A$ returns on the labeled sample $S$. This is the
--   object Theorems 2.5 and 2.13's generalization bounds are stated relative to; $n$ bounds the
--   representation cost of a point of $X$ and $\mathrm{size}(c)$ the representation cost of a
--   concept.
--
--   **Formalization Note.** `IsPACLearnable n size C` existentially quantifies the algorithm
--   `A : ∀ m, (Fin m → X × Bool) → (X → Bool)` (a labeled sample of any size to a hypothesis)
--   and a function `poly : ℝ → ℝ → ℕ → ℕ → ℝ` constrained to polynomial growth (bounded by
--   `K · (a+b+n+s+1)^k` for some `K > 0`, `k : ℕ`, uniformly in its arguments — the standard
--   reading of "polynomial in its arguments" absent a ready-made multivariate
--   polynomial-growth predicate in Mathlib), then states the displayed probability bound for
--   every `ε, δ > 0`, `D`, `c ∈ C` and `m` past the threshold, using `GeneralizationError` on
--   the hypothesis `A` returns given the sample `S` labeled by `c`.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 11, Definition 2.3 (PDF p. 28)

import Mathlib
import Definitions.Def_FoundationsML_PAC_GeneralizationError

open MeasureTheory

namespace FoundationsML.PAC

/-- A concept class `C ⊆ (X → Bool)` is PAC-learnable (Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Definition 2.3, p. 11, PDF p. 28):
there is an algorithm `A` (mapping a labeled sample of any size `m` to a hypothesis) and a
function `poly` of polynomial growth in its four arguments such that for every `ε, δ > 0`,
every distribution `D` on `X`, every target concept `c ∈ C`, and every sample size
`m ≥ poly(1/ε, 1/δ, n, size(c))`, the hypothesis `A` returns on an i.i.d. `D`-sample of size
`m` labeled by `c` has generalization error at most `ε` with probability at least `1 − δ`.
`n` bounds the representation cost of an element of `X`; `size` is the representation-cost
function on concepts.

**Formalization note.** "Polynomial function `poly(·,·,·,·)`" is made precise as: `poly` is
bounded above by `K · (a+b+n+s+1)^k` for some constants `K > 0`, `k : ℕ`, uniformly in its
(nonnegative) arguments — the standard reading of "polynomial in its arguments" absent a
ready-made multivariate polynomial-growth predicate in Mathlib. Also carries the book's
standing measurability hypothesis (Definition 2.1, footnote 2, p. 11) on `c` and on the
algorithm's output `A m S`. -/
def IsPACLearnable {X : Type*} [MeasurableSpace X] (n : ℕ) (size : (X → Bool) → ℕ)
    (C : Set (X → Bool)) : Prop :=
  ∃ (A : ∀ m : ℕ, (Fin m → X × Bool) → (X → Bool)) (poly : ℝ → ℝ → ℕ → ℕ → ℝ),
    (∃ K : ℝ, ∃ k : ℕ, 0 < K ∧ ∀ a b : ℝ, ∀ nn ss : ℕ, 0 ≤ a → 0 ≤ b →
        poly a b nn ss ≤ K * (a + b + (nn : ℝ) + (ss : ℝ) + 1) ^ k) ∧
    (∀ m : ℕ, ∀ S : Fin m → X × Bool, Measurable (A m S)) ∧
    ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∀ D : Measure X, IsProbabilityMeasure D →
        ∀ c ∈ C, Measurable c →
          ∀ m : ℕ, poly (1 / ε) (1 / δ) n (size c) ≤ (m : ℝ) →
            (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
              {S : Fin m → X |
                GeneralizationError D c (A m (fun i => (S i, c (S i)))) ≤ ε}).toReal

end FoundationsML.PAC


