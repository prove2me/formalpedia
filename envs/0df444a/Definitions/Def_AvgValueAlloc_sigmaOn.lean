-- Prove2me | Definitions.Def_AvgValueAlloc_sigmaOn
-- name    : AvgValueAlloc_sigmaOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:52.366358+00:00
-- url     : https://prove2.me/theorems/b4236060-6bff-47ba-a0c9-cc8f9ecb4f18
-- title:
--   Local positive ambiguity $\sigma(D,\rho)$, $\sigma_Q$, $\sigma_P$
-- statement:
--   For a finite set $A$ of items,
--   $$
--   \sigma_A=\max\Bigl\{1,\ \max_{v\in A,\ a>0}\bigl|\{j:\ a\le\rho_j<2a,\ v_j\ge\rho_j\}\bigr|\Bigr\}.\tag{2}
--   $$
--   $\sigma(D,\rho)$ takes $A=\operatorname{supp}D$, and $\sigma_Q,\sigma_P$ take the items of a live multiset or population. One has $1\le\sigma\le\kappa\le n$.
--
--   The upper bounds of Table 1 are stated in terms of this ambiguity, which the learner does not know.
--
--   **Formalization Note** The inner maximum is $0$ for an empty set, so $\sigma=1$ there.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §1.2, p.2, eq. (2)

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_FinLaw

namespace AvgValueAlloc

open scoped Classical in
/-- **Local positive ambiguity `σ` of a finite set of items.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §1.2, p.2, (2):
"σ(D, ρ) = max{1, max_{v∈supp(D), a>0} |{j : a ≤ ρ_j < 2a, v_j ≥ ρ_j}|}. Define σ_Q, σ_P
similarly".

`sigmaOn ρ A` is the maximum, over items `v ∈ A` and `a > 0`, of the number of buyers `j` with
`a ≤ ρ_j < 2a` and `v_j ≥ ρ_j`, and at least `1`. `sigmaLaw ρ D` is `σ(D, ρ)`, with `A` the
support of `D`; `σ_Q`, `σ_P` are `sigmaOn ρ (image of Q)`, `sigmaOn ρ (image of P)`.

**Formalization Note.** The inner maximum is a `sSup` in `ℕ` (bounded by `n`); it is `0` for an
empty set, so `σ = 1` there, as `max{1, ·}` requires. -/
noncomputable def sigmaOn {n : ℕ} (ρ : Fin n → ℚ) (A : Finset (Vec n)) : ℕ :=
  max 1 (sSup {c : ℕ | ∃ v ∈ A, ∃ a : ℝ, 0 < a ∧
    c = (Finset.univ.filter fun j =>
      a ≤ (ρ j : ℝ) ∧ (ρ j : ℝ) < 2 * a ∧ ρ j ≤ (v j : ℚ)).card})

/-- `σ(D, ρ)`: the ambiguity of the support of a finite law. -/
noncomputable def sigmaLaw {n : ℕ} (ρ : Fin n → ℚ) (D : FinLaw n) : ℕ :=
  sigmaOn ρ (Finset.univ.image D.val)

end AvgValueAlloc


