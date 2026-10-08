-- Prove2me | Definitions.Def_DoubleGreedyUSM_Randomized_Algorithm2
-- name    : DoubleGreedyUSM_Randomized_Algorithm2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T00:46:17.98487+00:00
-- url     : https://prove2.me/theorems/ee5b87db-b9c5-4538-8e9e-76f6dd6614c1
-- title:
--   Algorithm 2 — randomized double greedy and its finite law
-- statement:
--   Let $f:2^{\mathcal N}\to\mathbb R$ be a set function on a finite ground set, and let $u_1,\ldots,u_n$ be an order of its elements. **Algorithm 2** begins with $X_0=\varnothing$ and $Y_0=\mathcal N$. At step $i$, put
--
--   $$a_i=f(X_{i-1}\cup\{u_i\})-f(X_{i-1}),\qquad b_i=f(Y_{i-1}\setminus\{u_i\})-f(Y_{i-1}),\qquad a'_i=\max(a_i,0),\quad b'_i=\max(b_i,0).$$
--
--   With probability $a'_i/(a'_i+b'_i)$ it adds $u_i$ to $X$; otherwise it removes $u_i$ from $Y$. When $a'_i=b'_i=0$, the add probability is defined to be $1$. The definitions give the resulting finite law of $(X_i,Y_i)$ after every prefix of the order, its exact finite expectation, and $OPT_i=(OPT\cup X_i)\cap Y_i$ for a comparison set $OPT$.
--
--   This is the process analyzed in §III; retaining the intermediate laws makes the expected one-step inequalities precise.
--
--   **Formalization Note** The law is represented by an explicit real-valued finite mass function and updated by summing the two transition branches. It is not a product law. The zero-denominator case follows the printed footnote exactly.
-- source:
--   Buchbinder, Feldman, Naor, Schwartz, A Tight Linear Time (1/2)-Approximation for Unconstrained Submodular Maximization, FOCS 2012 version, Algorithm 2 (PDF p. 5) and §III notation (PDF pp. 4–5)

import Mathlib
import Definitions.Def_DoubleGreedyUSM_Deterministic_Algorithm1

namespace DoubleGreedyUSM.Randomized

variable {X : Type} [Fintype X] [DecidableEq X]

/-- Algorithm 2, lines 3–6: probability of adding `u` to the first set. -/
noncomputable def addProb (f : Finset X → ℝ) (s : Finset X × Finset X) (u : X) : ℝ :=
  let a := max (f (insert u s.1) - f s.1) 0
  let b := max (f (s.2.erase u) - f s.2) 0
  if a + b = 0 then 1 else a / (a + b)

/-- Probability mass of the next state after Algorithm 2 processes `u`. The two branches
are added, so the definition also covers states on which the branches happen to coincide. -/
noncomputable def nextMass (f : Finset X → ℝ) (s : Finset X × Finset X)
    (u : X) (t : Finset X × Finset X) : ℝ :=
  (if t = (insert u s.1, s.2) then addProb f s u else 0) +
  (if t = (s.1, s.2.erase u) then 1 - addProb f s u else 0)

/-- Advance a finite mass function by one adaptive Algorithm 2 step. -/
noncomputable def advance (f : Finset X → ℝ)
    (μ : (Finset X × Finset X) → ℝ) (u : X) : (Finset X × Finset X) → ℝ :=
  fun t => ∑ s : Finset X × Finset X, μ s * nextMass f s u t

/-- The exact mass of the pair `(Xᵢ,Yᵢ)` after processing the first `i` entries of `l`.
At time zero all mass is on `(∅, univ)`. -/
noncomputable def state (f : Finset X → ℝ) (l : List X) (i : ℕ) :
    (Finset X × Finset X) → ℝ :=
  (l.take i).foldl (advance f)
    (fun s => if s = (∅, Finset.univ) then 1 else 0)

/-- Exact finite expectation with respect to a mass function on pairs of subsets. -/
noncomputable def expect (μ : (Finset X × Finset X) → ℝ)
    (g : Finset X × Finset X → ℝ) : ℝ :=
  ∑ s : Finset X × Finset X, μ s * g s

end DoubleGreedyUSM.Randomized


