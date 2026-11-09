-- Prove2me | Definitions.Def_SelectiveDPT_IsMultAdvWitness
-- name    : SelectiveDPT_IsMultAdvWitness
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:06.112668+00:00
-- url     : https://prove2.me/theorems/fa55271c-b5d0-46fa-af63-582be8423b3c
-- title:
--   Witness $(\Gamma,\lambda,\eta)$ to the relational multiplicative adversary bound
-- statement:
--   Let $R \subseteq D \times Y$ be a relation and $\mu$ a distribution on $D$ with purification $|\mathcal D\rangle$. A $|D|\times|D|$ matrix $\Gamma$ with parameters $\lambda, \eta \in \mathbb R$ is a **valid witness** for Proposition 2.14 if
--
--   1. $\Gamma$ is positive definite with smallest eigenvalue $1$: $\Gamma$ is Hermitian and $\Gamma - I \succeq 0$;
--   2. $\Gamma |\mathcal D\rangle = |\mathcal D\rangle$;
--   3. $1 < \lambda \le \|\Gamma\|$ and $\eta > 0$;
--   4. $\|\Pi_{R^{-1}(y)}\,\Pi_{\Gamma,\le\lambda}\|^2 \le \eta$ for every $y \in Y$.
--
--   Norms are spectral norms. Since $|\mathcal D\rangle$ is a unit eigenvector with eigenvalue $1$, conditions 1–2 say exactly that $\Gamma$ is positive definite with smallest eigenvalue $1$ and fixes $|\mathcal D\rangle$. By footnote 8 of the paper, the strict projection $\Pi_{\Gamma,<\lambda}$ of [JZ26] gives an interchangeable condition.
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Proposition 2.14, p.17; Proposition 2.12 and footnote 8, p.16

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_SelectiveDPT_IsDistOn
import Definitions.Def_SelectiveDPT_projLe
import Definitions.Def_SelectiveDPT_rangeProj

open Matrix
open scoped ComplexOrder

namespace SelectiveDPT

open QAlgorithms

/-- `(Γ, λ, η)` is a valid witness for the relational multiplicative adversary bound for `R` under
the distribution `μ` on `D` (arXiv:2609.26678, Proposition 2.14, p.17, and Proposition 2.12,
p.16): `Γ` is a `|D| × |D|` positive-definite matrix with smallest eigenvalue `1` such that
`Γ |D⟩ = |D⟩`; `λ ∈ (1, ‖Γ‖]`; `η > 0`; and `‖Π_{R⁻¹(y)} Π_{Γ,≤λ}‖² ≤ η` for all `y ∈ Y`.

**Formalization Note.** "Positive-definite with smallest eigenvalue 1" is `Γ` Hermitian with
`Γ − I ⪰ 0`; together with `Γ |D⟩ = |D⟩` for the unit vector `|D⟩` this is exactly the paper's
condition. Norms are spectral norms. Footnote 8 (p.16): `Π_{Γ,<λ}` and `Π_{Γ,≤λ}` give
interchangeable conditions; the `≤` form of Proposition 2.14 is used. -/
def IsMultAdvWitness {α Y : Type*} [DecidableEq α] (μ : α → ℝ) (D : Finset α) (R : α → Y → Prop)
    (Γ : Matrix D D ℂ) (lam η : ℝ) : Prop :=
  Γ.IsHermitian ∧ (Γ - 1).PosSemidef ∧ Γ *ᵥ sqrtDist μ D = sqrtDist μ D ∧ 1 < lam ∧
    lam ≤ specNorm Γ ∧ 0 < η ∧ ∀ y, specNorm (rangeProj D R y * projLe Γ lam) ^ 2 ≤ η

end SelectiveDPT


