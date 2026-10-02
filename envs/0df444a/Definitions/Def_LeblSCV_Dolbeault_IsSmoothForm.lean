-- Prove2me | Definitions.Def_LeblSCV_Dolbeault_IsSmoothForm
-- name    : LeblSCV_Dolbeault_IsSmoothForm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T19:58:13.910995+00:00
-- url     : https://prove2.me/theorems/08f9abb8-f0c6-4ff9-b0c2-dac8e1b89a59
-- title:
--   Definition 4.4.1 — smooth (p,q)-form on an open set
-- statement:
--   Let $U \subset \mathbb{C}^n$ be open and $p, q \ge 0$. A **differential form of bidegree $(p,q)$**, or $(p,q)$-form, on $U$ is
--   $$\eta = \sum_{\alpha,\beta} \eta_{\alpha\beta}\, dz_\alpha \wedge d\bar z_\beta,$$
--   where $\alpha$ and $\beta$ run over all strictly increasing $p$- and $q$-tuples in $\{1,\dots,n\}$ and each $\eta_{\alpha\beta}$ is a smooth ($C^\infty$) function on $U$. The $(0,0)$-forms are the smooth functions on $U$.
--
--   **Formalization Note.** For a coefficient family `η : FormCoeffs n`, `IsSmoothForm U p q η` says that every coefficient is $C^\infty$ on $U$ in the real sense (`ContDiffOn ℝ ∞`) and that the coefficients of $dz_A \wedge d\bar z_B$ with $|A| \neq p$ or $|B| \ne q$ vanish on $U$. Values off $U$ are irrelevant. The book restricts to $p, q \le n$; for larger $p$ or $q$ the only such form is $0$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 138, Definition 4.4.1

import Mathlib
import Definitions.Def_LeblSCV_Dolbeault_dbar

open scoped ContDiff

namespace LeblSCV.Dolbeault

/-- Definition 4.4.1 (Lebl, p. 138): `η` is a (smooth) differential form of bidegree `(p, q)` on
`U ⊆ ℂⁿ`, i.e. `η = ∑_{α,β} η_{αβ} dz_α ∧ dz̄_β` with `α`, `β` running over the strictly increasing
`p`- and `q`-tuples and every coefficient `η_{αβ}` smooth (`C^∞` in the real sense) on `U`.
In the encoding `FormCoeffs n`, every coefficient is smooth on `U` and the coefficients with
`|A| ≠ p` or `|B| ≠ q` vanish on `U`. Only values on `U` matter. -/
def IsSmoothForm {n : ℕ} (U : Set (Fin n → ℂ)) (p q : ℕ) (η : FormCoeffs n) : Prop :=
  (∀ A B : Finset (Fin n), ContDiffOn ℝ ∞ (η A B) U) ∧
    ∀ A B : Finset (Fin n), (A.card ≠ p ∨ B.card ≠ q) → ∀ z ∈ U, η A B z = 0

end LeblSCV.Dolbeault


