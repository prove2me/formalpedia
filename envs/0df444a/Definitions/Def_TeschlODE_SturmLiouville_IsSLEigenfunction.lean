-- Prove2me | Definitions.Def_TeschlODE_SturmLiouville_IsSLEigenfunction
-- name    : TeschlODE_SturmLiouville_IsSLEigenfunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T11:22:28.904062+00:00
-- url     : https://prove2.me/theorems/2219344e-1d0e-4579-8ac8-4fc9098ad6ff
-- title:
--   Eigenfunction of the Sturm–Liouville operator L on D(L)
-- statement:
--   A number $z \in \mathbb{C}$ is an **eigenvalue** of $L$ (on the domain $D(L)$ determined by $\alpha, \beta$) if there is a nonzero $f \in D(L)$ with
--   $$L f = z f, \qquad (5.37)$$
--   and $f$ is then a corresponding **eigenfunction**. "Nonzero" is meant in $H_0 = C([a,b],\mathbb{C})$: $f$ does not vanish identically on $[a,b]$.
--
--   **Formalization Note.** `IsSLEigenfunction p q r a b α β z f` means `SLDomain p a b α β f`, $f(x) \ne 0$ for some $x \in [a,b]$, and $(Lf)(x) = z f(x)$ for all $x \in [a,b]$. Eigenvalues are a priori complex; that they are real is part of the theorems.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 149, §5.2, Eq. (5.37), applied to L of §5.4

import Mathlib
import Definitions.Def_TeschlODE_SturmLiouville_SLOp
import Definitions.Def_TeschlODE_SturmLiouville_SLDomain

namespace TeschlODE.SturmLiouville

/-- Teschl §5.2, p. 149, (5.37), applied to the Sturm–Liouville operator `L` on `D(L)` (§5.4,
(5.53)–(5.55)): `f` is an eigenfunction of `L` for the eigenvalue `z ∈ ℂ` if `f ∈ D(L)`, `f` is a
nonzero element of `H₀ = C([a, b], ℂ)` (it does not vanish identically on `[a, b]`), and
`L f = z f` on `[a, b]`. -/
def IsSLEigenfunction (p q r : ℝ → ℝ) (a b α β : ℝ) (z : ℂ) (f : ℝ → ℂ) : Prop :=
  SLDomain p a b α β f ∧ (∃ x ∈ Set.Icc a b, f x ≠ 0) ∧
    ∀ x ∈ Set.Icc a b, SLOp p q r a b f x = z * f x

end TeschlODE.SturmLiouville


