-- Prove2me | Definitions.Def_SU2Eposic_Extreme_Setup
-- name    : SU2Eposic_Extreme_Setup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T09:27:53.833717+00:00
-- url     : https://prove2.me/theorems/b3a89e6a-00c4-4e22-aca3-6696d1bf4edb
-- title:
--   SU(2), the irreducible representations ρ_m on homogeneous polynomials (2.1), the operators Γ, Δ, Ω, the coefficients c_{m,n,h}, the isometries α_{m,n,h}, EPOSIC channels and QC(ρ_r, ρ_m)
-- statement:
--   This file sets up the objects of Al Nuwairan's construction of SU(2)-covariant quantum channels.
--
--   1. **The representations $\rho_m$.** For $m\in\mathbb N$, $P_m$ is the space of homogeneous polynomials of degree $m$ in $x_1,x_2$. The group $SU(2)=\{\begin{pmatrix}a&b\\-\bar b&\bar a\end{pmatrix}: |a|^2+|b|^2=1\}$ acts on $P_m$ by
--   $$(\rho_m(g)f)(x_1,x_2)=f\big((x_1,x_2)g\big)=f(ax_1-\bar bx_2,\;bx_1+\bar ax_2).$$
--   With the inner product $\langle x_1^lx_2^{m-l},x_1^kx_2^{m-k}\rangle=l!(m-l)!\,\delta_{lk}$ the canonical basis $f^m_l=x_1^lx_2^{m-l}/\sqrt{l!(m-l)!}$ is orthonormal, and $\rho_m(g)$ is recorded as its matrix in this basis.
--
--   2. **Bi-degree polynomials and the operators.** $P_m\otimes P_n$ is identified with the polynomials in $x=(x_1,x_2)$, $y=(y_1,y_2)$ of bi-degree $(m,n)$, with orthonormal basis $f^m_l\otimes f^n_j$. On $\mathbb C[x,y]$:
--   $$\Delta_{xy}=x_1\tfrac{\partial}{\partial y_1}+x_2\tfrac{\partial}{\partial y_2},\quad \Delta_{yx}=y_1\tfrac{\partial}{\partial x_1}+y_2\tfrac{\partial}{\partial x_2},\quad \Gamma_{xy}f=(x_1y_2-y_1x_2)f,\quad \Omega_{xy}=\tfrac{\partial}{\partial x_1}\tfrac{\partial}{\partial y_2}-\tfrac{\partial}{\partial x_2}\tfrac{\partial}{\partial y_1}.$$
--
--   3. **The coefficients $c_{m,n,h}$** are defined by the recursion of Theorem 2.7: $c_{m,0,0}=1$ and, for $n\ge1$,
--   $$c_{m,n,h}=\frac{1}{(m+1)n}\begin{cases}c_{m+1,n-1,h}&h=0,\\ c_{m-1,n-1,h-1}+c_{m+1,n-1,h}&0<h<n,\\ c_{m-1,n-1,h-1}&h=n.\end{cases}$$
--
--   4. **The maps $\alpha_{m,n,h}$** (Definition 2.8). For $0\le h\le\min\{m,n\}$ and $r=m+n-2h$, $\alpha_{m,n,h}:P_r\to P_m\otimes P_n$ is
--   $$\alpha_{m,n,h}(f)=\sqrt{c_{m,n,h}}\;\Gamma_{xy}^h\Delta_{yx}^{n-h}f,$$
--   recorded as its matrix in the canonical bases.
--
--   5. **EPOSIC channels** (Proposition 2.18, Definition 2.19). $\Phi_{m,n,h}(A)=\mathrm{Tr}_{P_n}(\alpha_{m,n,h}A\alpha_{m,n,h}^*)$ for $A\in\mathrm{End}(P_r)$, the partial trace being over the factor $P_n$, and
--   $$EC(r,m)=\{\Phi_{m,n,h}:(n,h)\in E(r,m)\},\qquad E(r,m)=\{(n,h)\in\mathbb N^2: r=m+n-2h,\ 0\le h\le\min\{m,n\}\}.$$
--
--   6. **Covariant channels** ((1.1), Definition 1.12). $QC_{SU(2)}(\rho_r,\rho_m)$ is the set of quantum channels $\Phi:\mathrm{End}(P_r)\to\mathrm{End}(P_m)$ with
--   $$\Phi(\rho_r(g)A\rho_r(g)^*)=\rho_m(g)\Phi(A)\rho_m(g)^*\quad\text{for all }A\in\mathrm{End}(P_r),\ g\in SU(2).$$
--
--   These are the objects of the paper's main result: the extreme points of $QC_{SU(2)}(\rho_r,\rho_m)$ are exactly the channels in $EC(r,m)$.
--
--   **Formalization Note** $\mathbb C[x,y]$ is `MvPolynomial (Fin 4) ℂ` with variables $x_1,x_2,y_1,y_2$ in this order. $P_k$ is represented by coordinates in the canonical basis (0-based), so $\mathrm{End}(P_k)$ is the algebra of $(k+1)\times(k+1)$ complex matrices and adjoints are conjugate transposes; $P_m\otimes P_n$ is indexed with $P_m$ first. The degree $r$ of the input of $\alpha$ is an explicit argument, and every statement assumes $r+2h=m+n$, $h\le m$, $h\le n$; outside that range the recursion's value of $c$ is $0$ and is never used. Channels use the published Kraus-form predicate `QAlgorithms.IsChannel` and the partial trace `WildeQIT.partialTraceRight`. $SU(2)$ is Mathlib's special unitary group of $2\times2$ complex matrices.
-- source:
--   Al Nuwairan, SU(2)-irreducibly covariant and EPOSIC channels, arXiv:1306.5321v1, pp. 7–12 and 18, (1.1), Definition 1.12, (2.1), (2.2), canonical basis (p. 8), operators of p. 10, Theorem 2.7 (recursion for c_{m,n,h}), Definition 2.8, Proposition 2.18, Definition 2.19

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_WildeQIT_partialTrace

/-!
# SU(2), the irreducible representations ρ_m, the operators Γ, ∆, Ω, the coefficients
# c_{m,n,h}, the isometries α_{m,n,h}, the EPOSIC channels and QC_{SU(2)}(ρ_r, ρ_m)

M. Al Nuwairan, *SU(2)-irreducibly covariant and EPOSIC channels*, arXiv:1306.5321v1,
pp. 7–12 and 18: (1.1), (2.1), (2.2), the canonical basis f^m_l (p. 8), the operators of p. 10,
the recursion of Theorem 2.7 (p. 11), Definition 2.8 (pp. 11–12), Proposition 2.18 and
Definition 2.19 (p. 18).

Conventions.
* The polynomial ring `ℂ[x, y]` is `MvPolynomial (Fin 4) ℂ` with `X 0 = x₁`, `X 1 = x₂`,
  `X 2 = y₁`, `X 3 = y₂`. A polynomial of `P_k` is a polynomial in `x₁, x₂` only.
* `P_k` is represented by coordinates in the canonical orthonormal basis
  `f^k_l = x₁^l x₂^{k−l} / √(l!(k−l)!)`, `l = 0, …, k` (0-based, `Fin (k+1)`); End(P_k) is
  `Matrix (Fin (k+1)) (Fin (k+1)) ℂ`, and adjoints for the inner product (2.2) are conjugate
  transposes.
* `P_m ⊗ P_n` is the space of bi-degree `(m, n)` polynomials (p. 10), with coordinates in the
  basis `f^m_l ⊗ f^n_j`, indexed by `Fin (m+1) × Fin (n+1)` (`P_m` first).
* ρ_m is (2.1) literally: `(ρ_m(g) f)(x₁, x₂) = f((x₁, x₂) g)`, the row vector multiplied by `g`
  on the right.
-/

namespace SU2Eposic.Extreme

open MvPolynomial
open scoped Matrix ComplexConjugate Kronecker

/-- The polynomial ring `ℂ[x₁, x₂, y₁, y₂]` (p. 10); variable `0 = x₁`, `1 = x₂`, `2 = y₁`,
`3 = y₂`. -/
abbrev Poly := MvPolynomial (Fin 4) ℂ

/-- The exponent vector of the monomial `x₁^a x₂^b y₁^c y₂^d`. -/
noncomputable def expo (a b c d : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c + Finsupp.single 3 d

/-- `√(l!(k−l)!)`, the norm of the monomial `x₁^l x₂^{k−l}` for the inner product (2.2), i.e.
`1 / a^l_k` in the notation of p. 8. -/
noncomputable def normX (k l : ℕ) : ℝ :=
  Real.sqrt ((l.factorial * (k - l).factorial : ℕ) : ℝ)

/-- The canonical basis vector `f^k_l = a^l_k x₁^l x₂^{k−l}` of `P_k`, `a^l_k = 1/√(l!(k−l)!)`
(p. 8). -/
noncomputable def canonX (k : ℕ) (l : Fin (k + 1)) : Poly :=
  C (((normX k l)⁻¹ : ℝ) : ℂ) * X 0 ^ (l : ℕ) * X 1 ^ (k - l)

/-- The coordinate of a polynomial `p ∈ P_k` on the canonical basis vector `f^k_l`:
`√(l!(k−l)!) · coeff(x₁^l x₂^{k−l}, p)`. -/
noncomputable def coordX (k : ℕ) (p : Poly) (l : Fin (k + 1)) : ℂ :=
  ((normX k l : ℝ) : ℂ) * coeff (expo l (k - l) 0 0) p

/-- The basis vector `f^m_l ⊗ f^n_j = a^l_m a^j_n x₁^l x₂^{m−l} y₁^j y₂^{n−j}` of
`P_m ⊗ P_n ≅ P_{m,n}` (p. 10). -/
noncomputable def canonXY (m n : ℕ) (l : Fin (m + 1)) (j : Fin (n + 1)) : Poly :=
  C (((normX m l * normX n j)⁻¹ : ℝ) : ℂ) *
    X 0 ^ (l : ℕ) * X 1 ^ (m - l) * X 2 ^ (j : ℕ) * X 3 ^ (n - j)

/-- The coordinate of a bi-degree `(m, n)` polynomial `p` on `f^m_l ⊗ f^n_j`:
`√(l!(m−l)! j!(n−j)!) · coeff(x₁^l x₂^{m−l} y₁^j y₂^{n−j}, p)`. -/
noncomputable def coordXY (m n : ℕ) (p : Poly) (lj : Fin (m + 1) × Fin (n + 1)) : ℂ :=
  ((normX m lj.1 * normX n lj.2 : ℝ) : ℂ) *
    coeff (expo lj.1 (m - lj.1) lj.2 (n - lj.2)) p

/-- The substitution `(x₁, x₂) ↦ (x₁, x₂) g = (g₀₀ x₁ + g₁₀ x₂, g₀₁ x₁ + g₁₁ x₂)` of (2.1); for
`g = [[a, b], [−b̄, ā]]` this is `(a x₁ − b̄ x₂, b x₁ + ā x₂)`. The `y` variables are fixed. -/
noncomputable def actSubst (g : Matrix (Fin 2) (Fin 2) ℂ) : Fin 4 → Poly :=
  ![C (g 0 0) * X 0 + C (g 1 0) * X 1, C (g 0 1) * X 0 + C (g 1 1) * X 1, X 2, X 3]

/-- **(2.1), p. 8.** The representation `ρ_m` of `SU(2)` on `P_m`,
`(ρ_m(g) f)(x₁, x₂) = f((x₁, x₂) g)`, as the matrix in the canonical basis: column `l` holds the
canonical coordinates of `ρ_m(g) f^m_l`. -/
noncomputable def rho (m : ℕ) (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  Matrix.of fun k l => coordX m (aeval (actSubst (g : Matrix (Fin 2) (Fin 2) ℂ)) (canonX m l)) k

/-- The conjugate representation `g ↦ ρ̄_k(g)` on the conjugate space `P̄_k` (p. 3), in the same
canonical coordinates: the entrywise complex conjugate of `ρ_k(g)`. For the unitary `ρ_k` it is
the contragredient `ρ̌_k` (p. 3). -/
noncomputable def rhoConj (k : ℕ) (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  (rho k g).map (starRingEnd ℂ)

/-- The partial derivative `∂/∂X_i` on `ℂ[x₁, x₂, y₁, y₂]`, as a `ℂ`-linear map. -/
noncomputable def pd (i : Fin 4) : Module.End ℂ Poly :=
  (pderiv i : Derivation ℂ Poly Poly).toLinearMap

/-- **p. 10.** `∆_xy = x₁ ∂/∂y₁ + x₂ ∂/∂y₂`. -/
noncomputable def deltaXY : Module.End ℂ Poly :=
  LinearMap.mulLeft ℂ (X 0) ∘ₗ pd 2 +
    LinearMap.mulLeft ℂ (X 1) ∘ₗ pd 3

/-- **p. 10.** `∆_yx = y₁ ∂/∂x₁ + y₂ ∂/∂x₂`. -/
noncomputable def deltaYX : Module.End ℂ Poly :=
  LinearMap.mulLeft ℂ (X 2) ∘ₗ pd 0 +
    LinearMap.mulLeft ℂ (X 3) ∘ₗ pd 1

/-- **p. 10.** `Γ_xy f = (x₁ y₂ − y₁ x₂) f`. -/
noncomputable def gammaXY : Module.End ℂ Poly :=
  LinearMap.mulLeft ℂ (X 0 * X 3 - X 2 * X 1)

/-- **p. 10.** `Ω_xy = ∂/∂x₁ ∂/∂y₂ − ∂/∂x₂ ∂/∂y₁`. -/
noncomputable def omegaXY : Module.End ℂ Poly :=
  pd 0 ∘ₗ pd 3 -
    pd 1 ∘ₗ pd 2

/-- **Theorem 2.7, p. 11 (the recursion).** `c m n h = c_{m,n,h}`: `c_{m,0,0} = 1` and, for
`n ≥ 1`, with the factor `1/((m+1)n)`: `c_{m+1,n−1,h}` if `h = 0`;
`c_{m−1,n−1,h−1} + c_{m+1,n−1,h}` if `0 < h < n`; `c_{m−1,n−1,h−1}` if `h = n`. The value
outside `0 ≤ h ≤ min{m, n}` is `0` (never used: from a starting point in range the recursion only
calls arguments in range). -/
noncomputable def c : ℕ → ℕ → ℕ → ℝ
  | _, 0, h => if h = 0 then 1 else 0
  | m, n + 1, h =>
      (1 / (((m : ℝ) + 1) * ((n : ℝ) + 1))) *
        (if h = 0 then c (m + 1) n 0
        else if h < n + 1 then c (m - 1) n (h - 1) + c (m + 1) n h
        else if h = n + 1 then c (m - 1) n (h - 1)
        else 0)

/-- **Definition 2.8, pp. 11–12.** `α_{m,n,h} : P_r → P_m ⊗ P_n`,
`α_{m,n,h}(f) = √c_{m,n,h} Γ_xy^h ∆_yx^{n−h} f`, as a matrix in the canonical bases: column `i`
holds the coordinates of `√c_{m,n,h} Γ^h ∆_yx^{n−h} f^r_i` on `f^m_l ⊗ f^n_j`. The degree `r`
of the input is an explicit argument; it is the paper's map when `r = m + n − 2h` and
`h ≤ min{m, n}`, which every statement assumes. -/
noncomputable def alpha (r m n h : ℕ) : Matrix (Fin (m + 1) × Fin (n + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun lj i =>
    coordXY m n (((Real.sqrt (c m n h) : ℝ) : ℂ) • (gammaXY ^ h) ((deltaYX ^ (n - h)) (canonX r i)))
      lj

/-- **Proposition 2.18, p. 18.** `Φ_{m,n,h}(A) = Tr_{P_n}(α_{m,n,h} A α*_{m,n,h})` from End(P_r)
to End(P_m); the partial trace is over the right factor `P_n`. -/
noncomputable def eposic (r m n h : ℕ) : QAlgorithms.Superop (Fin (r + 1)) (Fin (m + 1)) :=
  fun A => WildeQIT.partialTraceRight (alpha r m n h * A * (alpha r m n h)ᴴ)

/-- **(1.1) and Definition 1.12, p. 7.** `QC_{SU(2)}(ρ_r, ρ_m)`: the quantum channels
(completely positive trace preserving maps, here in Kraus form) `Φ : End(P_r) → End(P_m)` with
`Φ(ρ_r(g) A ρ_r(g)*) = ρ_m(g) Φ(A) ρ_m(g)*` for every `A` and every `g ∈ SU(2)`. -/
def QC (r m : ℕ) : Set (QAlgorithms.Superop (Fin (r + 1)) (Fin (m + 1))) :=
  {Φ | QAlgorithms.IsChannel Φ ∧
    ∀ (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ),
      Φ (rho r g * A * (rho r g)ᴴ) = rho m g * Φ A * (rho m g)ᴴ}

/-- **Definition 2.19, p. 18.** `EC(r, m) = {Φ_{m,n,h} : (n, h) ∈ E(r, m)}`, where
`E(r, m) = {(n, h) ∈ ℕ² : r = m + n − 2h, 0 ≤ h ≤ min{m, n}}`. -/
def EC (r m : ℕ) : Set (QAlgorithms.Superop (Fin (r + 1)) (Fin (m + 1))) :=
  {Φ | ∃ n h : ℕ, r + 2 * h = m + n ∧ h ≤ m ∧ h ≤ n ∧ Φ = eposic r m n h}

end SU2Eposic.Extreme


