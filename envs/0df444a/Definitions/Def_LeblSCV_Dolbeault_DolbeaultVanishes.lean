-- Prove2me | Definitions.Def_LeblSCV_Dolbeault_DolbeaultVanishes
-- name    : LeblSCV_Dolbeault_DolbeaultVanishes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T20:04:48.063127+00:00
-- url     : https://prove2.me/theorems/aa677621-47f0-4de3-8e1a-9e69499a7015
-- title:
--   Vanishing of the Dolbeault cohomology group H^(p,q)(U)
-- statement:
--   Let $U\subset\mathbb{C}^n$ be open. A form $\eta$ is **$\bar\partial$-closed** if $\bar\partial\eta = 0$ and **$\bar\partial$-exact** if $\eta = \bar\partial\omega$ for some form $\omega$. The **Dolbeault cohomology group** is the quotient of complex vector spaces
--   $$H^{(p,q)}(U) = \frac{\{\bar\partial\text{-closed forms of bidegree }(p,q)\text{ on }U\}}{\{\bar\partial\text{-exact forms of bidegree }(p,q)\text{ on }U\}},$$
--   where, by convention, the only exact form of bidegree $(p,0)$ is $0$. The statement $H^{(p,q)}(U) = 0$ means that this quotient is the trivial vector space: every smooth $\bar\partial$-closed $(p,q)$-form on $U$ is $\bar\partial$-exact. For $q\ge1$ this is the solvability of the $\bar\partial$-problem $\bar\partial\omega = \eta$ for all $\eta$ satisfying the compatibility condition $\bar\partial\eta=0$.
--
--   **Formalization Note.** The quotient is not constructed; `DolbeaultVanishes U p q` is the statement "every smooth $\bar\partial$-closed $(p,q)$-form on $U$ is $\bar\partial$-exact", which is equivalent to $H^{(p,q)}(U) = 0$. Exactness in bidegree $(p, q+1)$ asks for a smooth $(p,q)$-form $\omega$ with $\bar\partial\omega = \eta$ on $U$; in bidegree $(p,0)$ it asks $\eta = 0$ on $U$ (the book's convention). The file also defines `IsDbarClosed` and `IsDbarExact`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), pp. 138–139 (Dolbeault cohomology groups)

import Mathlib
import Definitions.Def_LeblSCV_Dolbeault_IsSmoothForm

namespace LeblSCV.Dolbeault

/-- A form `η` is `∂̄`-closed on `U` if `∂̄η = 0` on `U` (Lebl, p. 138). -/
def IsDbarClosed {n : ℕ} (U : Set (Fin n → ℂ)) (η : FormCoeffs n) : Prop :=
  ∀ A B : Finset (Fin n), ∀ z ∈ U, dbar η A B z = 0

/-- A form `η` of bidegree `(p, q + 1)` is `∂̄`-exact on `U` (Lebl, p. 138) if `η = ∂̄ω` on `U` for a
smooth form `ω` of bidegree `(p, q)` on `U`. In bidegree `(p, 0)` the book's convention applies: the
only exact form is the zero form. -/
def IsDbarExact {n : ℕ} (U : Set (Fin n → ℂ)) (p : ℕ) : ℕ → FormCoeffs n → Prop
  | 0, η => ∀ A B : Finset (Fin n), ∀ z ∈ U, η A B z = 0
  | q + 1, η => ∃ ω : FormCoeffs n, IsSmoothForm U p q ω ∧
      ∀ A B : Finset (Fin n), ∀ z ∈ U, dbar ω A B z = η A B z

/-- `H^{(p,q)}(U) = 0` (Lebl, pp. 138–139): the Dolbeault cohomology group
`{∂̄-closed (p,q)-forms on U} / {∂̄-exact (p,q)-forms on U}` is the trivial vector space, i.e. every
smooth `∂̄`-closed form of bidegree `(p, q)` on `U` is `∂̄`-exact. -/
def DolbeaultVanishes {n : ℕ} (U : Set (Fin n → ℂ)) (p q : ℕ) : Prop :=
  ∀ η : FormCoeffs n, IsSmoothForm U p q η → IsDbarClosed U η → IsDbarExact U p q η

end LeblSCV.Dolbeault


