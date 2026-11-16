-- Prove2me | Definitions.Def_ROLDescent_Supplement_condLaw
-- name    : ROLDescent_Supplement_condLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:53:43.191079+00:00
-- url     : https://prove2.me/theorems/61242ffd-dea6-43c4-9a09-c3f5d503bfdc
-- title:
--   Conditional law $\mu_{S,s}=\mu(\,\cdot\mid X_S=s)$ on binary spin configurations
-- statement:
--   Let $V$ be a finite set of sites and $\mu$ a probability law on the binary configurations $\{0,1\}^V$, with spins $X_i(x)=x_i$. For $S\subseteq V$ and an assignment $s\in\{0,1\}^S$, the **conditional law** is
--
--   $$\mu_{S,s}(x)=\mu(x\mid X_S=s)=\frac{\mu(x)\,\mathbf 1\{x_S=s\}}{\mu(X_S=s)} .$$
--
--   All conditional covariances, influences and Gram matrices of Section 6.2.2 are computed under this law.
--
--   **Formalization Note** Configurations are functions `V → Bool` (`true` is the spin value $1$) and $s$ is a function on the sites of $S$. The division is real division; under the full-support assumption of Section 6.2 the denominator is positive.
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 6.2.2, p.50 (PDF 50)

import Mathlib

namespace ROLDescent.Supplement

/-- **Conditional law** `μ_{S,s} = μ( · | X_S = s)` of a law on binary spin configurations.
Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 6.2.2, p.50 (PDF 50): "Write µ_{S,s} := µ( · | X_S = s)."

Here `μ` is a probability law on `{0,1}^V` (configurations `x : V → Bool`, the spin
`X_i(x) = x_i`), `S ⊆ V` and `s ∈ {0,1}^S` an assignment of the sites of `S`. The value at `x` is
`μ(x) 1{x_S = s} / μ(X_S = s)`.

**Formalization Note** Spins `{0,1}` are `Bool` (`true` = 1). Real division: under the paper's
standing full-support assumption (Section 6.2.1, p.46) the denominator `μ(X_S = s)` is positive;
on a zero-probability assignment the value is the junk `0`, which no statement of this mission
reads. -/
noncomputable def condLaw {V : Type*} [Fintype V] [DecidableEq V] (μ : (V → Bool) → ℝ) (S : Finset V)
    (s : S → Bool) (x : V → Bool) : ℝ :=
  (if ∀ i : S, x i = s i then μ x else 0) / ∑ y, (if ∀ i : S, y i = s i then μ y else 0)

end ROLDescent.Supplement


