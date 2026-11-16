-- Prove2me | Definitions.Def_AlgoPFR_Supplement_IsRUniform
-- name    : AlgoPFR_Supplement_IsRUniform
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:35:42.610292+00:00
-- url     : https://prove2.me/theorems/e1ae3208-1916-4a3a-8a19-0027ad6e14d1
-- title:
--   $R$-uniform distributions on a finite set $A$
-- statement:
--   Let $A\subseteq\mathbb F_2^n$ be finite and nonempty and $R$ a real number. A distribution $\mu$ supported on $A$ is **$R$-uniform** if
--
--   $$\frac{1}{R|A|}\le\mu(x)\le\frac{R}{|A|}\qquad\text{for every }x\in A.$$
--
--   The definition forces $R\ge1$, and $R=1$ is exactly the uniform distribution on $A$. Approximate algorithmic PFR (Theorem 8.2) replaces uniform samples from $A$ by samples from an $R$-uniform distribution.
--
--   **Formalization Note** Nonemptiness of $A$ is a hypothesis of the theorem that uses the definition.
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), Definition 8.1, p.52

import Mathlib
import Definitions.Def_AlgoPFR_rd

set_option autoImplicit false

open scoped ENNReal

namespace AlgoPFR

namespace Supplement

noncomputable section

/-- **`R`-uniform distribution**, Definition 8.1, p.52 of Arunachalam, Dutt, Grewal, Gupte,
*Marton's conjecture in polynomial time*, arXiv:2609.20771 (sha256 60e45066…): a distribution `μ`
supported on the finite nonempty set `A` is `R`-uniform if `1/(R|A|) ≤ μ(x) ≤ R/|A|` for every
`x ∈ A`.

**Formalization Note.** `R` is real; the definition forces `R ≥ 1` when `A` is nonempty, and
`R = 1` is exactly the uniform law `U_A`. Nonemptiness of `A` is a hypothesis of the theorems
that use the definition. -/
def IsRUniform {n : ℕ} (μ : PMF (Vec n)) (A : Finset (Vec n)) (R : ℝ) : Prop :=
  μ.support ⊆ (A : Set (Vec n)) ∧
    ∀ x ∈ A, 1 / (R * A.card) ≤ (μ x).toReal ∧ (μ x).toReal ≤ R / A.card

end

end Supplement

end AlgoPFR


