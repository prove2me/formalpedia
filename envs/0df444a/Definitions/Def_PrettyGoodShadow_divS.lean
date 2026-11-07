-- Prove2me | Definitions.Def_PrettyGoodShadow_divS
-- name    : PrettyGoodShadow_divS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:21:39.965983+00:00
-- url     : https://prove2.me/theorems/17180794-e319-40cf-ac52-0c5380ff22b9
-- title:
--   The map $D_S(X)=\int_0^\infty(S+t\Pi)^{-1}X(S+t\Pi)^{-1}\,dt$
-- statement:
--   Let $S$ be positive semidefinite and let $\Pi$ be the projector onto $\operatorname{supp}(S)$. The map underlying the integral pretty good measurement is
--
--   $$
--   D_S(X)=\int_0^\infty (S+t\Pi)^{-1}\,X\,(S+t\Pi)^{-1}\,dt,
--   $$
--
--   where the inverses are taken on $\operatorname{supp}(S)$. It is the derivative of the matrix logarithm at $S$, which is what relates the outcome probabilities of the measurement to relative entropies.
--
--   **Formalization Note** $\Pi$ and $(S+t\Pi)^{-1}$ are defined by functional calculus with the scalar functions $u\mapsto\mathbf 1[u\ne0]$ and $u\mapsto\mathbf 1[u\ne0](u+t)^{-1}$; the second operator vanishes off $\operatorname{supp}(S)$. The integral is entrywise over $(0,\infty)$. For positive semidefinite $S$ every entry of the integrand is integrable, as the milestone on Definition 3.1 states, so no junk value of the Bochner integral occurs.
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), Definition 3.1, p.16

import Mathlib

namespace PrettyGoodShadow

/-- The projector `Π` onto `supp(S)` (arXiv:2610.06781, sha256 bd055b7d…, Definition 3.1, p.16).

**Formalization Note** Functional calculus with `u ↦ 1` for `u ≠ 0` and `0 ↦ 0`. For a Hermitian `S` the
nonzero eigenvalues span `supp(S)`, §3, p.15. On a non-Hermitian argument `cfc` returns `0`; `S` is
positive semidefinite at every use. -/
noncomputable def suppProj {ι : Type} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  cfc (fun u : ℝ => if u = 0 then 0 else 1) S

/-- The operator `(S + tΠ)⁻¹`, inverse on `supp(S)` (arXiv:2610.06781, sha256 bd055b7d…, Definition 3.1
and "inverses are taken on supp(S)", p.16).

**Formalization Note** Functional calculus with `u ↦ (u + t)⁻¹` for `u ≠ 0` and `0 ↦ 0`, so it vanishes on
the orthogonal complement of `supp(S)`. This is not `(S + t • 1)⁻¹`, which differs off the support and would
not satisfy `D_S(S) = Π`. At `t = 0` it is the pseudoinverse of `S`. -/
noncomputable def shiftInv {ι : Type} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℂ) (t : ℝ) :
    Matrix ι ι ℂ :=
  cfc (fun u : ℝ => if u = 0 then 0 else (u + t)⁻¹) S

/-- **The map `D_S`** of the integral pretty good measurement (arXiv:2610.06781, sha256 bd055b7d…,
Definition 3.1, p.16): `D_S(X) = ∫_0^∞ (S + tΠ)⁻¹ · X · (S + tΠ)⁻¹ dt`.

**Formalization Note** The integral is entrywise, over `(0, ∞)`, as a Bochner integral in `ℂ`. For a
positive semidefinite `S` every entry of the integrand is integrable, since the nonzero eigenvalues `u` of
`S` are positive and the integrand is a combination of `(u + t)⁻¹ (v + t)⁻¹`, so the junk value `0` of a
non-integrable integrand does not occur. The milestone `definition_3_1_validity` states this integrability. -/
noncomputable def divS {ι : Type} [Fintype ι] [DecidableEq ι] (S X : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  fun a b => ∫ t in Set.Ioi (0 : ℝ), (shiftInv S t * X * shiftInv S t) a b

end PrettyGoodShadow


