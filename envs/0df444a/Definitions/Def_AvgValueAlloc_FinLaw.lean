-- Prove2me | Definitions.Def_AvgValueAlloc_FinLaw
-- name    : AvgValueAlloc_FinLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:02.410917+00:00
-- url     : https://prove2.me/theorems/f9b80fc5-6f3f-4434-8901-a160ad79834a
-- title:
--   Finite-support law of items, listed by atoms
-- statement:
--   A **finite law** of items is a finite list of atoms $i$, each with a probability $p_i$ and an item $v^{(i)}\in\mathbb Q^n_{\ge0}$. It is a **law** when
--   $$
--   p_i>0\ \text{for every atom},\qquad \sum_i p_i=1,
--   $$
--   so its support is exactly the set of listed items; it is **rational** when every $p_i$ is rational.
--
--   These are the unknown laws $D$ of the i.i.d. model and the "finite rational laws" of the lower bounds. No lower bound on the probabilities and no bound on the values is imposed.
--
--   **Formalization Note** Repeated items are allowed (their probabilities add up). Positivity of each listed weight keeps a zero-probability atom out of the support, and hence out of the ambiguity $\sigma(D,\rho)$.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §1.1, p.2; Theorem 1.2(i), p.3

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec

namespace AvgValueAlloc

/-- **A finite-support law of items, listed by atoms.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §1.1, p.2: "an unknown finite-support law D on
Q^n_+ … probabilities of the unknown law have no precision or positivity-floor assumption";
Theorem 1.2(i), p.3: "a finite rational law".

A `FinLaw n` is a finite type `ι` of atoms, a weight `p i` and a value vector `val i` for each
atom. `IsLaw` says every weight is strictly positive and the weights sum to one, so the support
of the law is exactly the set of listed vectors. `IsRational` says every weight is rational.

**Formalization Note.** Repeated vectors are allowed (their weights add up). Positivity of every
listed weight keeps a zero-weight atom from entering the support and hence the ambiguity
`σ(D, ρ)`; no lower bound on the weights is imposed. -/
structure FinLaw (n : ℕ) where
  /-- the atoms -/
  ι : Type
  [fin : Fintype ι]
  [dec : DecidableEq ι]
  /-- the probability of each atom -/
  p : ι → ℝ
  /-- the item of each atom -/
  val : ι → Vec n

attribute [instance] FinLaw.fin FinLaw.dec

/-- Every weight is positive and the weights sum to one. -/
def FinLaw.IsLaw {n : ℕ} (D : FinLaw n) : Prop :=
  (∀ i, 0 < D.p i) ∧ ∑ i, D.p i = 1

/-- Every weight is a rational number. -/
def FinLaw.IsRational {n : ℕ} (D : FinLaw n) : Prop :=
  ∀ i, ∃ q : ℚ, D.p i = q

end AvgValueAlloc


