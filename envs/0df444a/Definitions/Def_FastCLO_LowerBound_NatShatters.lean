-- Prove2me | Definitions.Def_FastCLO_LowerBound_NatShatters
-- name    : FastCLO_LowerBound_NatShatters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:21:15.135137+00:00
-- url     : https://prove2.me/theorems/4e583e1a-fded-4d3a-b6c4-ee6ad034ef2f
-- title:
--   Natarajan shattering of k points by a class of policies (Definition 2)
-- statement:
--   Let $\Pi$ be a class of functions $\mathbb R^p \to \mathbb R^d$. The class $\Pi$ **Natarajan-shatters** $k$ points if there exist $x_1,\dots,x_k \in \mathbb R^p$ and values $s_1 \ne s_1', \dots, s_k \ne s_k'$ such that every pattern $b \in \{0,1\}^k$ is realised by a member of the class:
--   $$\forall b \in \{0,1\}^k\ \exists \pi \in \Pi\ \forall i:\quad \pi(x_i) = \begin{cases} s_i & b_i = 1,\\ s_i' & b_i = 0.\end{cases}$$
--   The Natarajan dimension of $\Pi$ is the largest $k$ for which this holds.
--
--   Natarajan dimension is the multiclass analogue of VC dimension; for policy classes with values in the finitely many extreme points of a polytope it is the complexity measure in which both the upper and the lower regret bounds of the paper are expressed.
--
--   **Formalization Note** "Natarajan dimension at least $\eta$" is expressed as `NatShatters Π η`, and "at most $\eta$" as `¬ NatShatters Π (η + 1)`; since shattering passes to subsets, these agree with the "largest integer" definition. The dimension itself is not defined as a supremum in $\mathbb N$, which would be $0$ for a class shattering arbitrarily large sets.
-- source:
--   Hu, Kallus, Mao, Fast Rates for Contextual Linear Optimization, arXiv:2011.03030v3, Definition 2, p. 6

import Mathlib
import Definitions.Def_FastCLO_LowerBound_Model

namespace FastCLO.LowerBound

variable {p d : ℕ}

/-- Natarajan shattering (Definition 2, Hu, Kallus, Mao, arXiv:2011.03030v3, p. 6): the class
`Π` shatters `k` points if there are `x_1, …, x_k ∈ ℝ^p` and values `s_i ≠ s'_i` such that every
pattern `b ∈ {0,1}^k` is realised by some `π ∈ Π` with `π(x_i) = s_i` if `b_i = 1` and
`π(x_i) = s'_i` if `b_i = 0`.

Formalization Note: "Natarajan dimension at least `η`" is `NatShatters Π η`; "at most `η`" is
`¬ NatShatters Π (η + 1)`. Shattering is hereditary, so these agree with "the largest integer `η`
for which …". The dimension is deliberately not an `sSup` in `ℕ`, which would be `0` for a class
shattering arbitrarily large sets. -/
def NatShatters (Pi : Set (Vec p → Vec d)) (k : ℕ) : Prop :=
  ∃ (x : Fin k → Vec p) (s s' : Fin k → Vec d), (∀ i, s i ≠ s' i) ∧
    ∀ b : Fin k → Bool, ∃ π ∈ Pi, ∀ i, π (x i) = if b i then s i else s' i

end FastCLO.LowerBound


