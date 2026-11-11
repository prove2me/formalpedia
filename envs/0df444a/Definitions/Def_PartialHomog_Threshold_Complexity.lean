-- Prove2me | Definitions.Def_PartialHomog_Threshold_Complexity
-- name    : PartialHomog_Threshold_Complexity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:27:25.864304+00:00
-- url     : https://prove2.me/theorems/3742f167-6361-4148-98d5-4e038c765138
-- title:
--   Quadratic algorithms, $C_2(\phi)$ and $C_\infty(\phi)$
-- statement:
--   Let $\phi=(\phi_0,\dots,\phi_{K-1})$ be a tuple of polynomials over a commutative ring $R$ in $z=(z_0,\dots,z_{N-1})$.
--
--   1. A **quadratic algorithm** for $\phi$ with $r$ products is a list of products $\ell_0m_0,\dots,\ell_{r-1}m_{r-1}$ of linear forms in all the variables $z$ such that
--   $$\phi_s\in\operatorname{span}_R\{\ell_0m_0,\dots,\ell_{r-1}m_{r-1}\}\quad\text{for every } s .$$
--   2. $C_2(\phi)$ is the least number of products in a quadratic algorithm for $\phi$.
--   3. $C_\infty(\phi)$ is the least number of product gates in a division-free circuit over $R$ with product gates of unbounded fan-in (any fan-in $\ge 2$, nesting and constants allowed) that computes $\phi$.
--
--   For a quadratic map both minima are over nonempty sets: $\phi_s=\sum_a z_a\,\lambda_{s,a}$ with linear forms $\lambda_{s,a}$ gives a quadratic algorithm, and every polynomial is computed by some circuit.
--
--   **Formalization Note** Both are `sInf` of subsets of `ℕ`. `C2 ϕ` would be `0` for a tuple with no quadratic algorithm (not a quadratic map); every theorem using it assumes a quadratic map, where the set is nonempty. `Cinf` ranges over the mission's `Circuit R N K`, which has no division gates.
-- source:
--   Spiizer, Partial Homogenization and the Structure of Optimal Algebraic Algorithms, STOC 2027 submission (manuscript sha256 33096d05…), p. 27 (PDF 29), §E.2 (definitions of C2, C∞); p. 4 (PDF 6), §1.3

import Mathlib
import Definitions.Def_PartialHomog_Threshold_Components
import Definitions.Def_PartialHomog_Threshold_Circuit

/-!
# Quadratic algorithms, `C₂(ϕ)` and `C∞(ϕ)`

Spiizer, *Partial Homogenization and the Structure of Optimal Algebraic Algorithms*,
STOC 2027 submission, §1.3 (p. 4) and §E.2 (p. 27).

* A **quadratic algorithm** for `ϕ = (ϕ_0, …, ϕ_{K-1})` with `r` products is a list of `r`
  products `ℓ_i m_i` of linear forms in all the variables `z` whose span contains every
  coordinate `ϕ_s`.
* `C₂(ϕ)` is the least number of products in a quadratic algorithm for `ϕ`.
* `C∞(ϕ)` is the least number of product gates in a division-free circuit over `R` with product
  gates of unbounded fan-in (any fan-in at least two) computing `ϕ`.

Both are least elements (`sInf`) of subsets of `ℕ`. For a quadratic map both sets are nonempty
(`ϕ_s = ∑_a z_a · ℓ_{s,a}` gives a quadratic algorithm, and every polynomial map is computed by
some circuit), so these are genuine minima there.
-/

namespace PartialHomog.Threshold

open MvPolynomial

variable {R : Type*} [CommRing R] {N K : ℕ}

/-- `ϕ` has a quadratic algorithm with `r` products: there are linear forms `ℓ_i, m_i`
(`i < r`) in all the variables such that every `ϕ_s ∈ span_R {ℓ_0 m_0, …, ℓ_{r-1} m_{r-1}}`. -/
def HasQuadAlg (ϕ : Fin K → MvPolynomial (Fin N) R) (r : ℕ) : Prop :=
  ∃ ℓ m : Fin r → MvPolynomial (Fin N) R,
    (∀ i, IsLinearForm (ℓ i)) ∧ (∀ i, IsLinearForm (m i)) ∧
    ∀ s, ϕ s ∈ Submodule.span R (Set.range fun i => ℓ i * m i)

/-- `C₂(ϕ)`: the least number of products of linear forms in a quadratic algorithm for `ϕ`. -/
noncomputable def C2 (ϕ : Fin K → MvPolynomial (Fin N) R) : ℕ :=
  sInf {r : ℕ | HasQuadAlg ϕ r}

/-- `C∞(ϕ)`: the least number of product gates in a division-free circuit over `R` with product
gates of unbounded fan-in that computes `ϕ`. -/
noncomputable def Cinf (ϕ : Fin K → MvPolynomial (Fin N) R) : ℕ :=
  sInf {m : ℕ | ∃ Φ : Circuit R N K, Φ.Computes ϕ ∧ Φ.numProd = m}

end PartialHomog.Threshold


