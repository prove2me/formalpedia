-- Prove2me | Definitions.Def_RSCapacity_LocalConstraints
-- name    : RSCapacity_LocalConstraints
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:28:41.883588+00:00
-- url     : https://prove2.me/theorems/950f8395-8554-474e-9f74-31c20c75e219
-- title:
--   The hidden-derivative substitution (22), the local constraints (24) and $\Phi_{\alpha,y}$
-- statement:
--   Fix a point–symbol pair $(\alpha,y)\in F^2$. In $Q\in F[X,Y_0,\dots,Y_r]$ make the formal substitution
--   $$X=\alpha+T,\qquad Y_0=y+\sum_{j=1}^r(-1)^{j+1}T^jY_j+TE,$$
--   and write the result as $Q_{\alpha,y}(T,E,Y_1,\dots,Y_r)=\sum_{b,\mathbf e}q_{b,\mathbf e}(T)E^bY_1^{e_1}\cdots Y_r^{e_r}$. $Q$ **obeys the local constraints** at $(\alpha,y)$ when, for every $b$ with $rb<m$,
--   $$q_{b,\mathbf e}(T)\equiv 0\pmod{T^{m-rb}}\quad\text{for every }\mathbf e,$$
--   that is, every coefficient of $T^iE^bY^{\mathbf e}$ in $Q_{\alpha,y}$ with $i+rb<m$ vanishes. The linear map $\Phi_{\alpha,y}$ on $\mathcal Q$ records exactly these coefficients, and $\operatorname{rank}\Phi_{\alpha,y}$ is the dimension of its image.
--
--   A polynomial obeying the constraints at $(\alpha,P(\alpha))$ vanishes to order $m$ after the differential substitution of $P$ at $\alpha$; this is how one agreement is turned into multiplicity.
--
--   **Formalization Note** $Q_{\alpha,y}$ lives in `MvPolynomial (Fin (r + 2)) F` with variable $0$ for $T$, $1$ for $E$ and $j+1$ for $Y_j$ ($1\le j\le r$). The rank is `Module.rank` (a cardinal), so an infinite-dimensional image could not collapse to $0$.
-- source:
--   Jeronimo, Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon Codes, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), §4.2, p.14 (PDF 16), Equations (22)–(24); §4.5, p.16 (PDF 18)

import Mathlib
import Definitions.Def_RSCapacity_InterpSpace

set_option autoImplicit false

namespace RSCapacity

/-!
# The hidden-derivative substitution (22), the local constraints (24) and Φ_{α,y}

Jeronimo, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…): §4.2, p.14
(PDF 16), Equations (22)–(24); §4.5, p.16 (PDF 18).

"Fix a point–symbol pair (α, y) ∈ F². In Q, make the formal substitution X = α + T,
Y_0 = y + ∑_{j=1}^{r} (−1)^{j+1} T^j Y_j + T E. (22) Write the result uniquely as
Q_{α,y}(T, E, Y_1, …, Y_r) = ∑_{b,e} q_{b,e}(T) E^b Y_1^{e_1} ⋯ Y_r^{e_r}. (23) For every b with
rb < m, impose q_{b,e}(T) ≡ 0 (mod T^{m−rb}) for every e. (24)" (p.14). "Fix (α, y), and let
Φ_{α,y} be the linear map that records the coefficients of T^i E^b Y_1^{e_1} Y^{v′} with
i + rb < m after Equation (22)." (p.16).

**Formalization Note.**
* Q_{α,y} lives in `MvPolynomial (Fin (r + 2)) F` with variable `0` = T, `1` = E and `j + 1` = Y_j
  for 1 ≤ j ≤ r. The substitution sends X (variable 0 of Q) to α + T, Y_0 (variable 1) to
  y + ∑_{j=1}^r (−1)^{j+1} T^j Y_j + T E, and Y_j (variable j + 1, j ≥ 1) to Y_j.
* (24) says the coefficient of T^i E^b Y^e vanishes whenever i < m − rb, i.e. i + r b < m:
  `ObeysLocal r m α y Q`.
* Φ_{α,y} is defined on the interpolation space 𝒬 (the constraints are "linear constraints on
  the coefficients of Q" ∈ 𝒬) and records all coefficients with i + r b < m; its rank is the
  dimension of its range, taken as a cardinal (`Module.rank`).
-/

open MvPolynomial

/-- The images of the variables X, Y_0, Y_1, …, Y_r under the substitution (22). -/
noncomputable def localSubstMap {F : Type*} [Field F] (r : ℕ) (α y : F) :
    Fin (r + 2) → MvPolynomial (Fin (r + 2)) F :=
  fun i =>
    if (i : ℕ) = 0 then C α + X 0
    else if (i : ℕ) = 1 then
      C y + (∑ j : Fin r, (-1 : MvPolynomial (Fin (r + 2)) F) ^ ((j : ℕ) + 2) *
          X 0 ^ ((j : ℕ) + 1) * X j.succ.succ) + X 0 * X 1
    else X i

/-- Q ↦ Q_{α,y}(T, E, Y_1, …, Y_r), the substitution (22)–(23). -/
noncomputable def localSubst {F : Type*} [Field F] (r : ℕ) (α y : F) :
    MvPolynomial (Fin (r + 2)) F →ₐ[F] MvPolynomial (Fin (r + 2)) F :=
  bind₁ (localSubstMap r α y)

/-- Q obeys the local constraints (24) at (α, y): every coefficient of T^i E^b Y^e of Q_{α,y}
with i + r b < m vanishes. -/
def ObeysLocal {F : Type*} [Field F] (r m : ℕ) (α y : F)
    (Q : MvPolynomial (Fin (r + 2)) F) : Prop :=
  ∀ e : Fin (r + 2) →₀ ℕ, e 0 + r * e 1 < m → (localSubst r α y Q).coeff e = 0

/-- The recorded monomials T^i E^b Y^e with i + r b < m. -/
def LocIdx (r m : ℕ) : Type := {e : Fin (r + 2) →₀ ℕ // e 0 + r * e 1 < m}

/-- Φ_{α,y} : 𝒬 → F^{LocIdx}: the coefficients of Q_{α,y} with i + r b < m. -/
noncomputable def Phi (F : Type*) [Field F] (A K r m : ℕ) (c s : ℝ) (α y : F) :
    interpSpace F A K r m c s →ₗ[F] (LocIdx r m → F) :=
  (LinearMap.pi fun e : LocIdx r m =>
      (lcoeff F e.1).comp (localSubst r α y).toLinearMap).comp
    (interpSpace F A K r m c s).subtype

/-- rank Φ_{α,y} = the dimension of the range of Φ_{α,y}, as a cardinal (`Module.rank`, so an
infinite-dimensional range would not collapse to `0`). -/
noncomputable def rankPhi (F : Type*) [Field F] (A K r m : ℕ) (c s : ℝ) (α y : F) : Cardinal :=
  Module.rank F (LinearMap.range (Phi F A K r m c s α y))

end RSCapacity


